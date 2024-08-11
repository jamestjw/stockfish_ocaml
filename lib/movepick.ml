(*
  Stockfish, a UCI chess playing engine derived from Glaurung 2.1
  Copyright (C) 2004-2024 The Stockfish developers (see AUTHORS file)

  Stockfish is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Stockfish is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program. If not, see <http://www.gnu.org/licenses/>.
*)

open Base
open Movegen
open Position
open Types
open Unsigned
module MG = MoveGen
module P = Position

module MovePick = struct
  (* Depth at which we start considering checks during QS *)
  let depth_qs_checks = 0
  let depth_qs_no_checks = -1
  let pawn_history_size = 512 (* has to be a power of 2 *)
  let correction_history_size = 16384 (* has to be a power of 2 *)
  let correction_history_limit = 1024

  let _ =
    assert (pawn_history_size land (pawn_history_size - 1) = 0);
    assert (correction_history_size land (correction_history_size - 1) = 0)

  type pawn_history_type = NORMAL | CORRECTION

  let pawn_structure_index ?(pht = NORMAL) pos =
    let i =
      match pht with
      | NORMAL -> pawn_history_size
      | CORRECTION -> correction_history_size
    in

    UInt64.(logand (P.pawn_key pos) (pred @@ of_int i) |> to_int)

  (* The type `t` is the base type of the data structure, and the
     parameter `bounds` limits the range of updates in [-bounds, bounds]
     when we update using the `add` function in StatsEntry *)
  module type StatsEntryType = sig
    type t

    val bounds : int
    val default : t
    val add : t -> t -> t
    val sub : t -> t -> t
    val mul : t -> t -> t
    val div : t -> t -> t
    val of_int : int -> t
    val to_int : t -> int
  end

  module StatsEntry = struct
    module type S = sig
      type t

      val bounds : int
      val default : t
      val add : t -> int -> t
    end

    module Make (T : StatsEntryType) : S with type t = T.t = struct
      type t = T.t

      let bounds = T.bounds
      let default = T.default

      let add e bonus =
        assert (Int.abs bonus <= bounds);

        let abs_bonus = T.of_int @@ Int.abs bonus in
        let bonus = T.of_int bonus in
        let e =
          T.add e @@ T.sub bonus (T.div (T.mul e abs_bonus) (T.of_int bounds))
        in
        assert (Int.abs @@ T.to_int e <= bounds);
        e
    end
  end

  (* We will be using a Map as the underlying data structure *)
  module type StatsKey = sig
    type t

    val compare : t -> t -> int
  end

  module Stats = struct
    module type S = sig
      type k
      type v
      type t

      val make : unit -> t
      val find : t -> k -> v
      val add : t -> k -> int -> t
      val enter : t -> k -> v -> t
    end

    module Make (K : StatsKey) (E : StatsEntry.S) :
      S with type k := K.t and type v := E.t = struct
      module Map = Stdlib.Map.Make (K)

      type v = E.t
      type t = v Map.t

      let make () = Map.empty

      let find m k =
        match Map.find_opt k m with Some v -> v | None -> E.default

      (* TODO: Decide if I want to make this data structure mutable or not *)
      let add m k v = Map.add k (E.add (find m k) v) m
      let enter m k v = Map.add k v m
    end
  end

  module MakeIntStatsEntry (T : sig
    val bounds : int
  end) =
  StatsEntry.Make (struct
    include Int

    let default = 0
    let bounds = T.bounds
    let add = ( + )
    let sub = ( - )
    let mul = ( * )
    let div = ( / )
  end)

  (*
   * ButterflyHistory records how often quiet moves have been successful or unsuccessful
   * during the current search, and is used for reduction and move ordering decisions.
   * It is indexed by colour and the move's from and to squares,
   * see www.chessprogramming.org/Butterfly_Boards
   *)
  module ButterflyHistory =
    Stats.Make
      (struct
        type t = Types.colour * Types.square * Types.square

        let compare = Poly.compare
      end)
      (MakeIntStatsEntry (struct
        let bounds = 7183
      end))

  (*
   * CounterMoveHistory stores counter moves indexed by [piece][to] of the previous
   * move, see www.chessprogramming.org/Countermove_Heuristic
   * 
   * This table doesn't require arithmetic
   *)
  module CounterMoveHistory =
    Stats.Make
      (struct
        type t = Types.piece * Types.square

        let compare = Poly.compare
      end)
      (StatsEntry.Make (struct
        type t = Types.move

        let default = Types.null_move
        let bounds = 0
        let add _ _ = failwith "not implemented"
        let sub _ _ = failwith "not implemented"
        let mul _ _ = failwith "not implemented"
        let div _ _ = failwith "not implemented"
        let of_int _ = failwith "not implemented"
        let to_int _ = failwith "not implemented"
      end))

  (* CapturePieceToHistory is addressed by a move's [piece][to][captured piece type] *)
  module CapturePieceToHistory =
    Stats.Make
      (struct
        type t = Types.piece * Types.square * Types.piece_type

        let compare = Poly.compare
      end)
      (MakeIntStatsEntry (struct
        let bounds = 10692
      end))

  (* PieceToHistory is like ButterflyHistory but is addressed by a move's [piece][to] *)
  module PieceToHistory =
    Stats.Make
      (struct
        type t = Types.piece * Types.square

        let compare = Poly.compare
      end)
      (MakeIntStatsEntry (struct
        let bounds = 29952
      end))

  (*
   * ContinuationHistory is the combined history of a given pair of moves, usually
   * the current one given a previous one. The nested history table is based on
   * PieceToHistory instead of ButterflyBoards.
   *)
  (* TODO: The fact that two of these maps are nested makes it quite hard for this
     data structure to be mutable I think *)
  module ContinuationHistory =
    Stats.Make
      (struct
        type t = Types.piece option * Types.square

        let compare = Poly.compare
      end)
      (StatsEntry.Make (struct
        type t = PieceToHistory.t

        let default = PieceToHistory.make ()
        let bounds = 0
        let add _ _ = failwith "not implemented"
        let sub _ _ = failwith "not implemented"
        let mul _ _ = failwith "not implemented"
        let div _ _ = failwith "not implemented"
        let of_int _ = failwith "not implemented"
        let to_int _ = failwith "not implemented"
      end))

  (* PawnHistory is addressed by the pawn structure and a move's [piece][to] *)
  module PawnHistory =
    Stats.Make
      (struct
        (* int = pawn_history_size *)
        type t = int * Types.piece * Types.square

        let compare = Poly.compare
      end)
      (MakeIntStatsEntry (struct
        let bounds = 8192
      end))

  (* CorrectionHistory is addressed by color and pawn structure *)
  module CorrectionHistory =
    Stats.Make
      (struct
        type t = Types.colour * int (* int = correction_history_size *)

        let compare = Poly.compare
      end)
      (MakeIntStatsEntry (struct
        let bounds = correction_history_limit
      end))

  type pick_type = NEXT | BEST

  type stage =
    (* Generate main search moves *)
    | MAIN_TT
    | CAPTURE_INIT
    | GOOD_CAPTURE
    | REFUTATION
    | QUIET_INIT
    | GOOD_QUIET
    | BAD_CAPTURE
    | BAD_QUIET
    (* Generate evasion moves *)
    | EVASION_TT
    | EVASION_INIT
    | EVASION
    (* Generate probcut moves *)
    | PROBCUT_TT
    | PROBCUT_INIT
    | PROBCUT
    (* Generate quiescence search moves *)
    | QSEARCH_TT
    | QCAPTURE_INIT
    | QCAPTURE
    | QCHECK_INIT
    | QCHECK
  [@@deriving enum, show]

  let next_stage_exn stage =
    stage_to_enum stage |> ( + ) 1 |> stage_of_enum |> Stdlib.Option.get

  (*
   * MovePicker is used to pick one pseudo-legal move at a time from the
   * current position. The most important function is `next_move`, which returns a
   * new pseudo-legal move each time it is called, until there are no moves left,
   * when `none_move` is returned. In order to improve the efficiency of the
   * alpha-beta algorithm, MovePicker attempts to return the moves which are most
   * likely to get a cut-off first.
   *)

  type t = {
    pos : P.t;
    main_history : ButterflyHistory.t;
    capture_history : CapturePieceToHistory.t;
    continuation_history : PieceToHistory.t array;
    pawn_history : PawnHistory.t;
    tt_move : Types.move;
    refutations : Types.move * Types.move * Types.move;
    cur : Types.move list; (* The moves that we consider now *)
    end_moves : Types.move list;
    bad_quiets : Types.move list;
    bad_captures : Types.move list;
    stage : stage;
    threshold : int; (* TODO: What is this precisely? *)
    depth : int;
    moves : Types.move list; (* All moves we generated *)
  }

  (*
   * Constructors of `movepicker`. As arguments, we pass information
   * to help it return the (presumably) good moves first, to decide which
   * moves to return (in the quiescence search, for instance, we only want to
   * search captures, promotions, and some checks) and how important a good
   * move ordering is at the current node.
   *)

  (* constructor for the main search *)

  let mk ~pos ~tt_move ~depth ~mh ~cph ~ch ~ph ~counter_move ~killers =
    assert (depth > 0);
    let in_check = P.checkers pos |> BB.bb_not_zero in
    let exists_tt_move =
      Types.move_not_none tt_move && P.pseudo_legal pos tt_move
    in
    let stage =
      match (in_check, exists_tt_move) with
      | true, true -> EVASION_TT
      | true, false -> EVASION_INIT
      | false, true -> MAIN_TT
      | false, false -> CAPTURE_INIT
    in
    let k1, k2 = killers in
    {
      pos;
      main_history = mh;
      capture_history = cph;
      continuation_history = ch;
      pawn_history = ph;
      tt_move;
      refutations = (k1, k2, counter_move);
      cur = [];
      end_moves = [];
      bad_quiets = [];
      bad_captures = [];
      stage;
      depth;
      moves = [];
      threshold = 0;
    }

  let mk_for_probcut ~pos ~tt_move ~threshold ~cph =
    let stage =
      if
        Types.move_not_none tt_move
        && P.is_capture_stage pos tt_move
        && P.pseudo_legal pos tt_move
        && P.see_ge pos tt_move threshold
      then PROBCUT_INIT
      else PROBCUT_TT
    in
    assert (BB.bb_is_empty @@ P.checkers pos);
    {
      pos;
      capture_history = cph;
      tt_move;
      threshold;
      stage;
      (* Dummy values *)
      main_history = ButterflyHistory.make ();
      continuation_history = Array.create ~len:0 @@ PieceToHistory.make ();
      pawn_history = PawnHistory.make ();
      refutations = (Types.none_move, Types.none_move, Types.none_move);
      cur = [];
      end_moves = [];
      bad_quiets = [];
      bad_captures = [];
      depth = Types.depth_none;
      moves = [];
    }

  (* Move picker for quiescence search *)
  let mk_for_qs ~pos ~tt_move ~depth ~mh ~cph ~ch ~ph =
    assert (depth <= 0);
    let in_check = P.checkers pos |> BB.bb_not_zero in
    let exists_tt_move =
      Types.move_not_none tt_move && P.pseudo_legal pos tt_move
    in
    let stage =
      match (in_check, exists_tt_move) with
      | true, true -> EVASION_TT
      | true, false -> EVASION_INIT
      | false, true -> QSEARCH_TT
      | false, false -> QCAPTURE_INIT
    in
    {
      stage;
      depth;
      pos;
      capture_history = cph;
      tt_move;
      main_history = mh;
      continuation_history = ch;
      pawn_history = ph;
      (* Dummy values *)
      threshold = Types.value_none;
      refutations = (Types.none_move, Types.none_move, Types.none_move);
      cur = [];
      end_moves = [];
      bad_quiets = [];
      bad_captures = [];
      moves = [];
    }

  (* Sort moves in descending order up to and including a given limit. The order
     of moves smaller than the limit is left unspecified. *)
  let partial_insertion_sort lst limit =
    let rec insert sorted x =
      match sorted with
      | [] -> [ x ]
      | h :: _ when Types.move_value h < Types.move_value x -> x :: sorted
      | h :: t -> h :: insert t x
    in
    let rec sort unsorted sorted l =
      match l with
      | [] -> sorted @ List.rev unsorted
      | x :: xs ->
          if Types.move_value x >= limit then
            let sorted' = insert sorted x in
            sort unsorted sorted' xs
          else sort (x :: unsorted) sorted xs
    in
    sort [] [] lst

  (* let mk_movepicker pos = { pos ; capture_history; _ } *)

  let score
      {
        pos;
        capture_history;
        main_history;
        pawn_history;
        continuation_history;
        _;
      } gt moves =
    (match gt with
    | MG.CAPTURES | MG.QUIETS | MG.EVASIONS -> ()
    | _ -> failwith "invalid type");
    let us = P.side_to_move pos in
    let ( threatened_by_pawn,
          threatened_by_minor,
          threatened_by_rook,
          threatened_pieces ) =
      if MG.equal_gen_type MG.QUIETS gt then
        let them = Types.other_colour us in
        let threatened_by_pawn = P.attacks_by pos Types.PAWN them in
        let threatened_by_minor =
          P.attacks_by pos Types.KNIGHT them
          |> BB.bb_or (P.attacks_by pos Types.BISHOP them)
          |> BB.bb_or threatened_by_pawn
        in
        (* FIXME: Minors aren't rooks, what gives? *)
        let threatened_by_rook =
          P.attacks_by pos Types.ROOK them |> BB.bb_or threatened_by_minor
        in
        (* Pieces threatened by pieces of lesser material value *)
        let threatened_pieces =
          P.pieces_of_colour_and_pt pos us Types.QUEEN
          |> BB.bb_and threatened_by_rook
          |> BB.bb_or
               (P.pieces_of_colour_and_pt pos us Types.ROOK
               |> BB.bb_and threatened_by_minor)
          |> BB.bb_or
               (P.pieces_of_colour_and_pts pos us [ Types.KNIGHT; Types.BISHOP ]
               |> BB.bb_and threatened_by_pawn)
        in

        ( threatened_by_pawn,
          threatened_by_minor,
          threatened_by_rook,
          threatened_pieces )
      else (BB.empty, BB.empty, BB.empty, BB.empty)
    in
    let update_move_value m =
      let piece = P.moved_piece_exn pos m in
      let pt = Types.type_of_piece piece in
      let dst = Types.move_dst m in
      let src = Types.move_src m in
      let value =
        match gt with
        | MG.CAPTURES ->
            let moved_piece = P.moved_piece_exn pos m in
            let move_dst = Types.move_dst m in
            let captured_piece = P.piece_on_exn pos move_dst in
            (* Capture value depends on the value of the captured piece and
               move history *)
            (7 * Types.piece_value captured_piece)
            + CapturePieceToHistory.find capture_history
                (moved_piece, move_dst, Types.type_of_piece captured_piece)
        | MG.QUIETS ->
            let escaping_capture_bonus =
              if BB.bb_not_zero (BB.bb_and_sq threatened_pieces src) then
                match pt with
                | Types.QUEEN
                  when BB.bb_is_empty (BB.sq_and_bb dst threatened_by_rook) ->
                    50000
                | Types.ROOK
                  when BB.bb_is_empty (BB.sq_and_bb dst threatened_by_minor) ->
                    25000
                | _ when BB.bb_is_empty (BB.sq_and_bb dst threatened_by_pawn) ->
                    15000
                | _ -> 0
              else 0
            in
            let en_prise_malus =
              if BB.bb_is_empty (BB.bb_and_sq threatened_pieces src) then
                match pt with
                | Types.QUEEN ->
                    Bool.to_int
                      (BB.bb_not_zero @@ BB.sq_and_bb dst threatened_by_rook)
                    * 50000
                | Types.ROOK
                  when BB.bb_not_zero (BB.sq_and_bb dst threatened_by_minor) ->
                    25000
                | (Types.KNIGHT | Types.BISHOP)
                  when BB.bb_not_zero (BB.sq_and_bb dst threatened_by_pawn) ->
                    15000
                | _ -> 0
              else 0
            in
            (* Histories *)
            (2 * ButterflyHistory.find main_history (us, src, dst))
            + 2
              * PawnHistory.find pawn_history
                  (pawn_structure_index pos, piece, dst)
            + PieceToHistory.find (Array.get continuation_history 0) (piece, dst)
            + PieceToHistory.find (Array.get continuation_history 1) (piece, dst)
            + PieceToHistory.find (Array.get continuation_history 2) (piece, dst)
              / 4
            + PieceToHistory.find (Array.get continuation_history 3) (piece, dst)
            + PieceToHistory.find (Array.get continuation_history 5) (piece, dst)
            (* Bonus for checks *)
            + Bool.to_int
                (P.check_squares pos pt |> BB.sq_and_bb dst |> BB.bb_not_zero)
              * 16384
              (* Bonus for escaping capture *)
            + escaping_capture_bonus
            (* malus for putting piece en prise *)
            - en_prise_malus
        | MG.EVASIONS ->
            (* Greatly prioritise evasions that also capture material. *)
            (* Deducting the piece type enum makes it so that we
               use the least valuable piece to defend against the check *)
            (* FIXME: Why not use the piece value of the moved piece? *)
            if P.is_capture_stage pos m then
              Types.piece_value (P.piece_on_exn pos @@ Types.move_src m)
              - (Types.piece_type_to_enum @@ Types.type_of_piece piece)
              + (1 lsl 28)
            else
              ButterflyHistory.find main_history (us, src, dst)
              + PieceToHistory.find
                  (Array.get continuation_history 0)
                  (piece, dst)
              + PawnHistory.find pawn_history
                  (pawn_structure_index pos, piece, dst)
        | _ -> failwith "impossible"
      in
      { m with value }
    in
    List.map ~f:update_move_value moves

  let select ({ tt_move; _ } as mp) pick_type pred =
    let equal_to_tt move = Types.equal_move move tt_move in
    let rec select_best ({ cur; end_moves; _ } as mp) =
      match (cur, end_moves) with
      | [], _ -> (mp, Types.none_move)
      (* If an end move is better than the curr move, swap their positions *)
      | m :: ms, em :: ems when Types.move_value em > Types.move_value m ->
          select_best { mp with cur = em :: ms; end_moves = m :: ems }
      | m :: ms, _ when not @@ equal_to_tt m ->
          let res, mp = pred m mp in
          if res then ({ mp with cur = ms }, m)
          else select_best { mp with cur = ms }
      | _ :: ms, _ -> select_best { mp with cur = ms }
    in

    let rec select_next ({ cur; _ } as mp) =
      match cur with
      | [] -> (mp, Types.none_move)
      | m :: rest when not @@ equal_to_tt m ->
          let res, mp = pred m mp in
          if res then ({ mp with cur = rest }, m)
          else select_next { mp with cur = rest }
      | _ :: rest -> select_next { mp with cur = rest }
    in
    match pick_type with BEST -> select_best mp | NEXT -> select_next mp

  (*
   * Most important method of the MovePicker class. It
   * returns a new pseudo-legal move every time it is called until there are no more
   * moves left, picking the move with the highest score from a list of generated moves.
   *)
  let rec next_move ?(skip_quiets = false)
      ({
         stage;
         tt_move;
         pos;
         moves;
         depth;
         threshold;
         bad_quiets;
         bad_captures;
         refutations;
         _;
       } as mp) =
    (* Stdlib.Printf.printf "Next move, stage : %s\n" (show_stage stage); *)
    let quiet_threshold d = -3330 * d in
    match stage with
    | MAIN_TT | EVASION_TT | QSEARCH_TT | PROBCUT_TT ->
        ({ mp with stage = next_stage_exn stage }, tt_move)
    | CAPTURE_INIT | PROBCUT_INIT | QCAPTURE_INIT ->
        let moves' = MG.generate MG.CAPTURES pos in
        let moves' = score mp MG.CAPTURES moves' in
        let moves' = partial_insertion_sort moves' Int.min_value in

        next_move
          {
            mp with
            stage = next_stage_exn stage;
            cur = moves';
            moves = moves' @ moves;
          }
          ~skip_quiets
    | GOOD_CAPTURE ->
        let mp, move =
          (* Store losing captures to bad_captures so we may try them again
             later*)
          select mp NEXT (fun m mp ->
              if P.see_ge pos m (-Types.move_value m / 18) then (true, mp)
              else (false, { mp with bad_captures = m :: mp.bad_captures }))
        in

        if Types.move_is_ok move then (mp, move)
        else
          (* Set `cur` to the refutations *)
          let cur =
            (* If the countermove is the same as a killer, skip it *)
            match refutations with
            | r0, r1, r2 when Types.equal_move r0 r2 || Types.equal_move r1 r2
              ->
                [ r0; r1 ]
            | r0, r1, r2 -> [ r0; r1; r2 ]
          in

          next_move { mp with stage = next_stage_exn stage; cur } ~skip_quiets
    | REFUTATION ->
        let mp, move =
          select mp NEXT (fun m mp ->
              ( Types.move_is_ok m
                && (not (P.is_capture_stage pos m))
                && P.pseudo_legal pos m,
                mp ))
        in
        if Types.move_is_ok move then (mp, move)
        else next_move { mp with stage = next_stage_exn stage } ~skip_quiets
    | QUIET_INIT ->
        let quiets =
          if not skip_quiets then
            let quiets = MG.generate MG.QUIETS pos in
            let quiets = score mp MG.QUIETS quiets in
            let quiets =
              partial_insertion_sort quiets @@ quiet_threshold depth
            in
            quiets
          else []
        in
        next_move
          {
            mp with
            stage = next_stage_exn stage;
            cur = quiets;
            moves = quiets @ moves;
          }
          ~skip_quiets
    | GOOD_QUIET ->
        if not skip_quiets then
          let mp, move =
            select mp NEXT (fun m mp ->
                let r0, r1, r2 = refutations in
                ( not
                    (Types.equal_move r0 m || Types.equal_move r1 m
                   || Types.equal_move r2 m),
                  mp ))
          in

          if Types.move_is_ok move then
            if
              Types.move_value move > -8000
              || Types.move_value move <= quiet_threshold depth
            then (mp, move)
            else
              (* Remaining quiets are bad *)
              next_move
                {
                  mp with
                  stage = next_stage_exn stage;
                  cur = bad_captures;
                  bad_quiets = mp.cur;
                }
                ~skip_quiets
          else
            next_move
              { mp with stage = next_stage_exn stage; cur = bad_captures }
              ~skip_quiets
        else
          next_move
            { mp with stage = next_stage_exn stage; cur = bad_captures }
            ~skip_quiets
    | BAD_CAPTURE ->
        let mp, move = select mp NEXT (fun _ mp -> (true, mp)) in
        if Types.move_is_ok move then (mp, move)
        else
          next_move
            { mp with stage = next_stage_exn stage; cur = bad_quiets }
            ~skip_quiets
    | BAD_QUIET ->
        if not skip_quiets then
          select mp NEXT (fun m mp ->
              let r0, r1, r2 = refutations in
              ( not
                  (Types.equal_move r0 m || Types.equal_move r1 m
                 || Types.equal_move r2 m),
                mp ))
        else (mp, Types.none_move)
    | EVASION_INIT ->
        let moves' = MG.generate MG.EVASIONS pos in
        let moves' = score mp MG.EVASIONS moves' in

        next_move
          {
            mp with
            stage = next_stage_exn stage;
            cur = moves';
            moves = moves' @ moves;
          }
          ~skip_quiets
    | EVASION -> select mp BEST (fun _ mp -> (true, mp))
    | PROBCUT -> select mp NEXT (fun m mp -> (P.see_ge pos m threshold, mp))
    | QCAPTURE ->
        let mp, move = select mp NEXT (fun _ mp -> (true, mp)) in
        if Types.move_is_ok move then (mp, move)
          (* If we are not at the right depth for QS checks *)
        else if depth <> depth_qs_checks then (mp, Types.none_move)
        else next_move { mp with stage = next_stage_exn stage } ~skip_quiets
    | QCHECK_INIT ->
        let moves' = MG.generate MG.QUIET_CHECKS pos in
        next_move
          {
            mp with
            stage = next_stage_exn stage;
            cur = moves';
            moves = moves' @ moves;
          }
          ~skip_quiets
    | QCHECK -> select mp NEXT (fun _ mp -> (true, mp))

  (*
   * Unit tests of helper functions within the module
   *)
  let%test_unit "test_partial_insertion_sort" =
    let mk_move v = Types.mk_move ~value:v Types.A1 Types.A1 in
    let inp =
      [
        mk_move 5;
        mk_move 7;
        mk_move (-1);
        mk_move 3;
        mk_move 9;
        mk_move (-3);
        mk_move 2;
        mk_move 10;
        mk_move 1;
      ]
    in
    let exp =
      [
        mk_move 10;
        mk_move 9;
        mk_move 7;
        mk_move 5;
        mk_move 3;
        mk_move 2;
        mk_move 1;
        mk_move (-1);
        mk_move (-3);
      ]
    in

    (* The default `equal_move` function ignores the value, so we write a
       special equal function that only looks at the values *)
    [%test_result: Types.move list]
      ~equal:
        (List.equal (fun m1 m2 -> Types.move_value m1 = Types.move_value m2))
      ~expect:exp
      (partial_insertion_sort inp 0)
end
