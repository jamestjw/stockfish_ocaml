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
  let pawn_history_size = 512 (* has to be a power of 2 *)
  let correction_history_size = 16384 (* has to be a power of 2 *)
  let correction_history_limit = 1024

  let _ =
    assert (pawn_history_size land (pawn_history_size - 1) = 0);
    assert (correction_history_size land (correction_history_size - 1) = 0)

  type pawn_history_type = NORMAL | CORRECTION

  let pawn_structure_index pht pos =
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
          T.add e @@ T.sub bonus (T.mul e (T.div abs_bonus @@ T.of_int bounds))
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
        type t = Types.piece * Types.square

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
        type t = Types.square * int (* int = correction_history_size *)

        let compare = Poly.compare
      end)
      (MakeIntStatsEntry (struct
        let bounds = correction_history_limit
      end))

  type pick_type = NEXT | BEST

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
    refutations : Types.move list;
    cur : Types.move list;
    end_moves : Types.move list;
    end_bad_captures : Types.move list;
    begin_bad_quiets : Types.move list;
    end_bad_quiets : Types.move list;
    stage : int;
    threshold : int;
    depth : int;
    moves : Types.move list;
  }

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

  let score gt
      ({
         pos;
         moves;
         capture_history;
         main_history;
         pawn_history;
         continuation_history;
         _;
       } as mp) =
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
                  (pawn_structure_index NORMAL pos, piece, dst)
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
                  (pawn_structure_index NORMAL pos, piece, dst)
        | _ -> failwith "impossible"
      in
      { m with value }
    in
    { mp with moves = List.map ~f:update_move_value moves }

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

    [%test_result: Types.move list] ~expect:exp (partial_insertion_sort inp 0)
end
