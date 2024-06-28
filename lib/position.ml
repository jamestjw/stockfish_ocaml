(*
 *   Stockfish, a UCI chess playing engine derived from Glaurung 2.1
 *   Copyright (C) 2004-2024 The Stockfish developers (see AUTHORS file)
 *
 *   Stockfish is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   Stockfish is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *)

open Base
open Bitboard
open Types
open Unsigned
open Utils

module Position = struct
  type key = UInt64.t

  (*
   * StateInfo struct stores information needed to restore a Position object to
   * its previous state when we retract a move. Whenever a move is made on the
   * board (by calling Position::do_move), a StateInfo object must be passed.
   *)
  type state_info = {
    (* Copied when making a move *)
    material_key : key;
    pawn_key : key;
    non_pawn_material : Types.value array;
    castling_rights : int;
    rule50 : int;
    plies_from_null : int;
    (* En passant square *)
    ep_square : Types.square option;
    (* Not copied when making a move (will be recomputed anyhow) *)
    key : key;
    checkers_bb : Bitboard.t;
    previous : state_info list;
    blockers_for_king : Bitboard.t array;
    pinners : Bitboard.t array;
    (* Squares checked by each piece type *)
    check_squares : Bitboard.t array;
    captured_piece : Types.piece;
    repetition : int;
  }

  type t = {
    board : Types.piece option array;
    by_type_bb : Bitboard.t array;
    by_colour_bb : Bitboard.t array;
    piece_count : int array;
    castling_rights_mask : int array;
    castling_rook_square : Types.square option array;
    castling_path : Bitboard.t array;
    game_ply : int;
    side_to_move : Types.colour;
    chess960 : bool;
    st_list : state_info list;
  }

  let side_to_move { side_to_move; _ } = side_to_move
  let piece_on { board; _ } sq = Array.get board (Types.square_to_enum sq)
  let piece_on_exn pos sq = piece_on pos sq |> Stdlib.Option.get
  let is_empty pos sq = piece_on pos sq |> Option.is_none
  let moved_piece pos m = piece_on pos @@ Types.move_src m
  let moved_piece_exn pos m = moved_piece pos m |> Stdlib.Option.get

  let pieces_of_pt { by_type_bb; _ } pt =
    Array.get by_type_bb (Types.piece_type_to_enum pt)

  let pieces_of_pts pos pts =
    List.fold ~init:Bitboard.empty
      ~f:(fun acc pt -> Bitboard.bb_or acc @@ pieces_of_pt pos pt)
      pts

  let pieces_of_colour { by_colour_bb; _ } colour =
    Array.get by_colour_bb (Types.colour_to_enum colour)

  (* Get all pieces *)
  let pieces pos =
    Bitboard.bb_or
      (pieces_of_colour pos Types.WHITE)
      (pieces_of_colour pos Types.BLACK)

  let pieces_of_colour_and_pt pos colour pt =
    Bitboard.bb_and (pieces_of_colour pos colour) (pieces_of_pt pos pt)

  let pieces_of_colour_and_pts pos colour pts =
    Bitboard.bb_and (pieces_of_colour pos colour) (pieces_of_pts pos pts)

  let count_by_colour_and_pt { piece_count; _ } colour pt =
    Array.get piece_count @@ Types.piece_to_enum @@ Types.mk_piece colour pt

  let count_by_pt pos pt =
    count_by_colour_and_pt pos Types.WHITE pt
    + count_by_colour_and_pt pos Types.BLACK pt

  (* When there is only one of this piece on the board, get its square. *)
  let square_of_pt_and_colour pos pt colour =
    assert (count_by_colour_and_pt pos colour pt = 1);
    pieces_of_colour_and_pts pos colour [ pt ]
    |> Bitboard.lsb |> Bitboard.bb_to_square

  let ep_square { st_list; _ } =
    match st_list with
    | { ep_square; _ } :: _ -> ep_square
    | _ -> failwith "Empty state info list"

  (* TODO: Check what we are calling this with and where its used, maybe
     expecting enumbit*)
  (* See if any pieces are in the castling path *)
  let castling_impeded ({ castling_path; _ } as pos) cr =
    match cr with
    | Types.WHITE_OO | Types.WHITE_OOO | Types.BLACK_OO | Types.BLACK_OOO ->
        Bitboard.bb_and (pieces pos)
          (Array.get castling_path (Types.castling_right_to_enum cr))
        |> Bitboard.bb_not_zero

  (* TODO: Check what we are calling this with and where its used, maybe
     expecting enumbit*)
  let castling_rook_square { castling_rook_square; _ } cr =
    match cr with
    | Types.WHITE_OO | Types.WHITE_OOO | Types.BLACK_OO | Types.BLACK_OOO ->
        Array.get castling_rook_square (Types.castling_right_to_enum cr)

  (* Returns all the squares attacked by a certain colour *)
  let attacks_by pos pt colour =
    let rec helper threats attackers pt obstacles =
      if Bitboard.bb_not_zero attackers then
        let attacker, attackers = Bitboard.pop_lsb attackers in
        let attacker_sq = Bitboard.bb_to_square attacker in
        helper
          (Bitboard.bb_or threats
          @@ Bitboard.attacks_bb_occupied pt attacker_sq obstacles)
          attackers pt obstacles
      else threats
    in
    match pt with
    | Types.PAWN ->
        Bitboard.pawn_attacks_bb colour
          (pieces_of_colour_and_pt pos colour Types.PAWN)
    | _ ->
        helper Bitboard.empty
          (pieces_of_colour_and_pt pos colour pt)
          pt (pieces pos)

  let checkers { st_list; _ } = (List.hd_exn st_list).checkers_bb

  let blockers_for_king { st_list; _ } colour =
    Array.get (List.hd_exn st_list).blockers_for_king
    @@ Types.colour_to_enum colour

  let pinners { st_list; _ } colour =
    Array.get (List.hd_exn st_list).pinners @@ Types.colour_to_enum colour

  let check_squares { st_list; _ } colour =
    Array.get (List.hd_exn st_list).check_squares @@ Types.colour_to_enum colour

  (* Based on a congruential pseudo-random number generator *)
  let make_key seed =
    UInt64.mul seed @@ UInt64.of_string "6364136223846793005"
    |> UInt64.add @@ UInt64.of_string "1442695040888963407"

  let adjust_key50 { st_list; _ } after_move k =
    let rule50 = (List.hd_exn st_list).rule50 in
    let threshold = if after_move then 14 - 1 else 14 in
    if rule50 < threshold then k
    else UInt64.logor k @@ make_key (UInt64.of_int ((rule50 - threshold) / 8))

  let key ({ st_list; _ } as pos) =
    adjust_key50 pos false @@ (List.hd_exn st_list).key

  let pawn_key { st_list; _ } = (List.hd_exn st_list).pawn_key
  let material_key { st_list; _ } = (List.hd_exn st_list).material_key

  let non_pawn_material_for_colour { st_list; _ } colour =
    Array.get (List.hd_exn st_list).non_pawn_material
    @@ Types.colour_to_enum colour

  let non_pawn_material pos =
    non_pawn_material_for_colour pos Types.WHITE
    + non_pawn_material_for_colour pos Types.BLACK

  let game_ply { game_ply; _ } = game_ply

  (* FIXME: Document what this means *)
  let rule50_count { st_list; _ } = (List.hd_exn st_list).rule50
  let is_chess960 { chess960; _ } = chess960

  (* FIXME: I think this returns moves generated during the capture stage? *)
  let is_capture pos m =
    assert (Types.move_is_ok m);

    (* If the destination square is already occupied, then this is a capture. *)
    (not (is_empty pos @@ Types.move_dst m))
    && not (Types.equal_move_type (Types.get_move_type m) Types.CASTLING)
    || Types.equal_move_type (Types.get_move_type m) Types.EN_PASSANT

  (* Returns true if a move is generated from the capture stage, having also
     queen promotions covered, i.e. consistency with the capture stage move
     generation is needed to avoid the generation of duplicate moves. *)
  let is_capture_stage pos m =
    assert (Types.move_is_ok m);
    match (is_capture pos m, Types.get_ppt m) with
    | true, _ | _, Some Types.QUEEN -> true
    | _ -> false

  let captured_piece { st_list; _ } = (List.hd_exn st_list).captured_piece

  (* FIXME: Reconsider this mix of mutable and immutable data structure. Using
     functional updates alongside with inplace mutations doesn't feel very good. *)
  (* TODO: Consider caching total piece count and by_type_bb for all pieces *)
  let put_piece { board; by_type_bb; by_colour_bb; piece_count; _ } piece sq =
    let piece_type_enum =
      Types.piece_type_to_enum @@ Types.type_of_piece piece
    in
    let piece_enum = Types.piece_to_enum piece in
    let colour_enum = Types.colour_to_enum @@ Types.color_of_piece piece in

    Array.set board (Types.square_to_enum sq) (Some piece);

    Array.set by_type_bb piece_type_enum
      (Bitboard.bb_or_sq (Array.get by_type_bb piece_type_enum) sq);

    Array.set by_colour_bb colour_enum
      (Bitboard.bb_or_sq (Array.get by_colour_bb colour_enum) sq);

    Array.set piece_count piece_enum
      (Int.succ (Array.get piece_count piece_enum))

  let remove_piece { board; by_type_bb; by_colour_bb; piece_count; _ } sq =
    match Array.get board (Types.square_to_enum sq) with
    | Some piece ->
        let piece_type_enum =
          Types.piece_type_to_enum @@ Types.type_of_piece piece
        in
        let piece_enum = Types.piece_to_enum piece in
        let colour_enum = Types.colour_to_enum @@ Types.color_of_piece piece in

        Array.set by_type_bb piece_type_enum
          (Bitboard.bb_xor_sq (Array.get by_type_bb piece_type_enum) sq);

        Array.set by_colour_bb colour_enum
          (Bitboard.bb_xor_sq (Array.get by_colour_bb colour_enum) sq);

        Array.set board (Types.square_to_enum sq) None;

        Array.set piece_count piece_enum
          (Int.pred (Array.get piece_count piece_enum))
    | None -> failwith "Removing nonexistent piece"

  let move_piece { board; by_type_bb; by_colour_bb; _ } src dst =
    match Array.get board (Types.square_to_enum src) with
    | Some piece ->
        let src_dest = Bitboard.square_bb src |> Bitboard.sq_or_bb dst in
        let piece_type_enum =
          Types.piece_type_to_enum @@ Types.type_of_piece piece
        in
        let colour_enum = Types.colour_to_enum @@ Types.color_of_piece piece in

        Array.set by_type_bb piece_type_enum
          (Bitboard.bb_xor (Array.get by_type_bb piece_type_enum) src_dest);

        Array.set by_colour_bb colour_enum
          (Bitboard.bb_xor (Array.get by_colour_bb colour_enum) src_dest);

        Array.set board (Types.square_to_enum src) None;
        Array.set board (Types.square_to_enum dst) (Some piece)
    | None -> failwith "Moving nonexistent piece"

  (*
   * Implements Marcel van Kervinck's cuckoo algorithm to detect repetition of positions
   * for 3-fold repetition draws. The algorithm uses two hash tables with Zobrist hashes
   * to allow fast detection of recurring positions. For details see:
   * http://web.archive.org/web/20201107002606/https://marcelk.net/2013-04-06/paper/upcoming-rep-v2.pdf
   *)

  type zobrist = {
    psq : key array array;
    en_passant : key array;
    castling : key array;
    side : key;
    no_pawns : key;
  }

  (* First and second hash functions for indexing the cuckoo tables *)
  (*  h & 0x1fff *)
  let h1 h = UInt64.to_int @@ UInt64.logand h @@ UInt64.of_int 0x1fff

  (* (h >> 16) & 0x1fff *)
  let h2 h =
    UInt64.to_int
    @@ (UInt64.shift_right h 16 |> UInt64.logand @@ UInt64.of_int 0x1fff)

  (* Cuckoo tables with Zobrist hashes of valid reversible moves, and the moves themselves *)
  let cuckoo = Array.create ~len:8192 UInt64.zero
  let cuckoo_move = Array.create ~len:8192 Types.none_move

  (* TODO: Test that this is right, but how? *)
  let zobrist_data =
    (* Helper function *)
    let rec insert_cuckoo key move i =
      let key' = Array.get cuckoo i in
      let move' = Array.get cuckoo_move i in
      Array.set cuckoo i key;
      Array.set cuckoo_move i move;
      if Types.equal_move move' Types.none_move then
        (* This is an empty slot so we are done *)
        ()
      else
        (* Push victim to alternative slot *)
        let i = if i = h1 key then h2 key else h1 key in
        insert_cuckoo key' move' i
    in
    Random.init 42;
    (* TODO: Find a better seed? *)
    let gen_uint64 () = Random.bits64 () |> UInt64.of_int64 in
    let psq =
      Array.make_matrix
        ~dimx:(List.length Types.all_pieces)
        ~dimy:(List.length Types.all_squares)
        UInt64.zero
    in
    let en_passant =
      Array.create ~len:(List.length Types.all_files) UInt64.zero
    in
    let castling =
      Array.create ~len:Types.castling_right_num_combinations UInt64.zero
    in
    let side = gen_uint64 () in
    let no_pawns = gen_uint64 () in
    List.iter (List.cartesian_product Types.all_pieces Types.all_squares)
      ~f:(fun (piece, sq) ->
        matrix_set psq
          (Types.piece_to_enum piece)
          (Types.square_to_enum sq) (gen_uint64 ()));
    List.iter Types.all_files ~f:(fun file ->
        Array.set en_passant (Types.file_to_enum file) (gen_uint64 ()));
    List.iter
      (0 -- (Types.castling_right_num_combinations - 1))
      ~f:(fun i -> Array.set castling i (gen_uint64 ()));
    (* Setup tables with all possible piece movements, we ignore pawn moves as they
       reset the repetition count *)
    let count = ref 0 in
    List.iter Types.all_pieces ~f:(fun piece ->
        ignore
        @@ List.fold
             ~init:(List.tl_exn Types.all_squares)
             ~f:(fun other_sqs s1 ->
               let s1_enum = Types.square_to_enum s1 in
               List.iter other_sqs ~f:(fun s2 ->
                   let s2_enum = Types.square_to_enum s2 in
                   let piece_type = Types.type_of_piece piece in
                   if
                     (not (Types.equal_piece_type piece_type Types.PAWN))
                     && Bitboard.bb_not_zero
                        @@ (Bitboard.attacks_bb_occupied piece_type s1
                              Bitboard.empty
                           |> Bitboard.sq_and_bb s2)
                   then (
                     let piece_enum = Types.piece_to_enum piece in
                     let m = Types.mk_move s2 s1 in
                     let key =
                       UInt64.Infix.(
                         matrix_get psq piece_enum s1_enum
                         lxor matrix_get psq piece_enum s2_enum
                         lxor side)
                     in
                     let i = h1 key in
                     insert_cuckoo key m i;
                     count := !count + 1));
               List.tl other_sqs |> Option.value ~default:[])
             Types.all_squares);
    assert (!count = 3668);
    { psq; en_passant; castling; side; no_pawns }

  (* TODO: Test this function *)
  let set_castling_right
      ({ st_list; castling_rights_mask; castling_rook_square; castling_path; _ }
       as pos) colour rook_sq =
    let king_sq = square_of_pt_and_colour pos Types.KING colour in
    let king_sq_enum = Types.square_to_enum king_sq in
    let rook_sq_enum = Types.square_to_enum rook_sq in
    let cr =
      (* If king < rook, i.e. the king is on the left of the rook, that means that
         we are dealing with kingside castling. *)
      match (colour, Types.compare_square king_sq rook_sq < 0) with
      | WHITE, true -> Types.WHITE_OO
      | WHITE, false -> Types.WHITE_OOO
      | BLACK, true -> Types.BLACK_OO
      | BLACK, false -> Types.BLACK_OOO
    in
    let cr_enum = Types.castling_right_to_enum cr in
    let st_list =
      match st_list with
      | ({ castling_rights; _ } as hd) :: rest ->
          { hd with castling_rights = castling_rights lor cr_enum } :: rest
      | [] -> failwith "Missing st"
    in
    Array.set castling_rights_mask king_sq_enum
      (Array.get castling_rights_mask king_sq_enum lor cr_enum);
    Array.set castling_rights_mask rook_sq_enum
      (Array.get castling_rights_mask rook_sq_enum lor cr_enum);
    Array.set castling_rook_square cr_enum (Some rook_sq);
    let king_dest_sq =
      Types.relative_sq colour
      @@ if Types.is_kingside_castling cr then Types.G1 else Types.C1
    in
    let rook_dest_sq =
      Types.relative_sq colour
      @@ if Types.is_kingside_castling cr then Types.F1 else Types.D1
    in
    (* The squares that the rook and king need to traverse in order to castle
       (this includes the destination squares of both pieces). We ignore the
       current squares of the king and rook because the pieces may 'cross' each
       other in chess960. *)
    let path =
      BitboardInfix.(
        (Bitboard.between_bb rook_sq rook_dest_sq
        || Bitboard.between_bb king_sq king_dest_sq)
        & Bitboard.bb_not
            (Bitboard.square_bb king_sq || Bitboard.square_bb rook_sq))
    in
    Array.set castling_path cr_enum path;
    { pos with st_list }

  (*
   * Calculates st->blockersForKing[c] and st->pinners[~c],
   * which store respectively the pieces preventing king of color c from being
   * in check and the slider pieces of color ~c pinning pieces of color c to the
   * king.
   *)
  let update_slider_blockers ({ st_list; _ } as pos) c =
    let other_c = Types.other_colour c in
    let king_sq = square_of_pt_and_colour pos Types.KING c in
    let our_pieces = pieces_of_colour pos c in
    (* Snipers are enemy sliders that attack `king_sq` when other snipers are
       not in the way. *)
    let snipers =
      BitboardInfix.(
        (Bitboard.attacks_bb Types.ROOK king_sq
         & pieces_of_pts pos [ Types.QUEEN; Types.ROOK ]
        || Bitboard.attacks_bb Types.BISHOP king_sq
           & pieces_of_pts pos [ Types.QUEEN; Types.BISHOP ])
        & pieces_of_colour pos other_c)
    in
    let occupancy = Bitboard.bb_xor (pieces pos) snipers in
    let rec do_snipers snipers blockers pinners =
      if Bitboard.bb_not_zero snipers then
        let sniper_bb, others = Bitboard.pop_lsb snipers in
        let sniper_sq = Bitboard.bb_to_square sniper_bb in
        (* This will not include the sniper itself as it won't be in
           `occupancy` *)
        let candidate_blockers =
          Bitboard.between_bb king_sq sniper_sq |> Bitboard.bb_and occupancy
        in
        let blockers, pinners =
          (* Check if there is exactly one piece between the sniper and the
             king *)
          if
            Bitboard.bb_not_zero candidate_blockers
            && not (Bitboard.more_than_one candidate_blockers)
          then
            let blockers = Bitboard.bb_and blockers candidate_blockers in
            (* If the piece is ours, then the sniper is pinning it to our
               king*)
            if
              Bitboard.bb_not_zero
              @@ Bitboard.bb_and candidate_blockers our_pieces
            then (blockers, Bitboard.bb_or pinners sniper_bb)
            else (blockers, pinners)
          else (blockers, pinners)
        in
        do_snipers others blockers pinners
      else (blockers, pinners)
    in
    let blockers_bb, pinners_bb =
      do_snipers snipers Bitboard.empty Bitboard.empty
    in
    match st_list with
    | { blockers_for_king; pinners; _ } :: _ ->
        Array.set blockers_for_king (Types.colour_to_enum c) blockers_bb;
        Array.set pinners (Types.colour_to_enum other_c) pinners_bb
    | [] -> failwith "Missing state info"

  (* Sets king attacks to detect if a move gives check *)
  let set_check_info ({ side_to_move; st_list; _ } as pos) =
    update_slider_blockers pos Types.WHITE;
    update_slider_blockers pos Types.BLACK;

    let enemy_colour = Types.other_colour side_to_move in
    (* Get square of opponent's king *)
    let king_sq = square_of_pt_and_colour pos Types.KING enemy_colour in
    let check_squares = (List.hd_exn st_list).check_squares in
    let set_check_squares pt =
      Array.set check_squares (Types.piece_type_to_enum pt)
    in

    let all_pieces = pieces pos in
    (* Populate the table with the squares from which the king may be attacked *)
    let bishop_attacks =
      Bitboard.attacks_bb_occupied Types.BISHOP king_sq all_pieces
    in
    let rook_attacks =
      Bitboard.attacks_bb_occupied Types.ROOK king_sq all_pieces
    in
    set_check_squares Types.PAWN
      (Bitboard.pawn_attacks_bb_from_sq enemy_colour king_sq);
    set_check_squares Types.KNIGHT
      (Bitboard.attacks_bb_occupied Types.KNIGHT king_sq all_pieces);
    set_check_squares Types.BISHOP bishop_attacks;
    set_check_squares Types.ROOK rook_attacks;
    set_check_squares Types.QUEEN (Bitboard.bb_or bishop_attacks rook_attacks);
    set_check_squares Types.KING Bitboard.empty

  let attackers_to_occupied pos sq occupied =
    let pieces_of_colour_and_pt = pieces_of_colour_and_pt pos in
    let pieces_of_pt = pieces_of_pt pos in
    let pieces_of_pts = pieces_of_pts pos in

    Bitboard.pawn_attacks_bb_from_sq Types.BLACK sq
    |> Bitboard.bb_and (pieces_of_colour_and_pt Types.WHITE Types.PAWN)
    |> Bitboard.bb_or
         (Bitboard.pawn_attacks_bb_from_sq Types.WHITE sq
         |> Bitboard.bb_and (pieces_of_colour_and_pt Types.BLACK Types.PAWN))
    |> Bitboard.bb_or
         (Bitboard.attacks_bb Types.KNIGHT sq
         |> Bitboard.bb_and (pieces_of_pt Types.KNIGHT))
    |> Bitboard.bb_or
         (Bitboard.attacks_bb_occupied Types.ROOK sq occupied
         |> Bitboard.bb_and (pieces_of_pts [ Types.ROOK; Types.QUEEN ]))
    |> Bitboard.bb_or
         (Bitboard.attacks_bb_occupied Types.BISHOP sq occupied
         |> Bitboard.bb_and (pieces_of_pts [ Types.BISHOP; Types.QUEEN ]))
    |> Bitboard.bb_or
         (Bitboard.attacks_bb Types.KING sq
         |> Bitboard.bb_and (pieces_of_pt Types.KING))

  let attackers_to_sq pos sq = attackers_to_occupied pos sq (pieces pos)

  (* TODO: Unit test this *)
  let set_state ({ st_list; side_to_move; piece_count; _ } as pos) =
    let rec do_pieces pieces_bb (key, pawn_key, white_npm, black_npm) =
      if Bitboard.bb_not_zero pieces_bb then
        let sq_bb, rest = Bitboard.pop_lsb pieces_bb in
        let sq = Bitboard.bb_to_square sq_bb in
        let sq_enum = Types.square_to_enum sq in
        let piece = piece_on_exn pos sq in
        let piece_enum = Types.piece_to_enum piece in
        let key =
          UInt64.logxor key @@ matrix_get zobrist_data.psq piece_enum sq_enum
        in
        let pawn_key, white_npm, black_npm =
          match Types.type_of_piece piece with
          | Types.PAWN ->
              ( UInt64.logxor pawn_key
                @@ matrix_get zobrist_data.psq piece_enum sq_enum,
                white_npm,
                black_npm )
          (* King doesn't affect pawn key or npm *)
          | Types.KING -> (pawn_key, white_npm, black_npm)
          (* Increment npm *)
          | _ -> (
              match Types.color_of_piece piece with
              | Types.WHITE ->
                  (pawn_key, white_npm + Types.piece_value piece, black_npm)
              | Types.BLACK ->
                  (pawn_key, white_npm, black_npm + Types.piece_value piece))
        in
        do_pieces rest (key, pawn_key, white_npm, black_npm)
      else (key, pawn_key, white_npm, black_npm)
    in
    let checkers_bb =
      attackers_to_sq pos (square_of_pt_and_colour pos Types.KING side_to_move)
      |> Bitboard.bb_and
           (pieces_of_colour pos (Types.other_colour side_to_move))
    in
    set_check_info pos;
    let { castling_rights; ep_square; non_pawn_material; _ } =
      List.hd_exn pos.st_list
    in
    let all_pieces = pieces pos in
    let key, pawn_key, white_npm, black_npm =
      do_pieces all_pieces
        (UInt64.zero, zobrist_data.no_pawns, Types.value_zero, Types.value_zero)
    in
    Array.set non_pawn_material (Types.colour_to_enum Types.WHITE) white_npm;
    Array.set non_pawn_material (Types.colour_to_enum Types.BLACK) black_npm;
    let key =
      match ep_square with
      | Some ep_square ->
          UInt64.logxor key
          @@ Array.get zobrist_data.en_passant
          @@ Types.file_to_enum @@ Types.file_of_sq ep_square
      | None -> key
    in
    (* The default value is zobrist_data.side, we save computation by
       toggling it when its black to move. *)
    let key =
      match side_to_move with
      | Types.WHITE -> key
      | Types.BLACK -> UInt64.logxor key zobrist_data.side
    in
    let key =
      UInt64.logxor key @@ Array.get zobrist_data.castling castling_rights
    in
    let material_key =
      List.fold ~init:UInt64.zero
        ~f:(fun mk pc ->
          let piece_enum = Types.piece_to_enum pc in
          List.fold ~init:mk
            ~f:(fun mk cnt ->
              UInt64.logxor mk @@ matrix_get zobrist_data.psq piece_enum cnt)
            (0 -- (Array.get piece_count piece_enum - 1)))
        Types.all_pieces
    in
    match st_list with
    | st :: rest ->
        {
          pos with
          st_list = { st with key; pawn_key; material_key; checkers_bb } :: rest;
        }
    | [] -> failwith "Missing state info"

  (* TODO: Unit test this *)
  let legal ({ side_to_move = us; chess960; _ } as pos) m =
    assert (Types.move_is_ok m);
    let src = Types.move_src m in
    let dst = Types.move_dst m in
    let them = Types.other_colour us in

    (* Some sanity checks,
       1. Moved piece is our colour
       2. There is exactly one king of our colour on the board *)
    assert (
      Types.equal_colour us @@ Types.color_of_piece @@ moved_piece_exn pos m);
    assert (
      Types.equal_piece
        (piece_on_exn pos @@ square_of_pt_and_colour pos Types.KING us)
        (Types.mk_piece us Types.KING));
    if Types.equal_move_type (Types.get_move_type m) Types.EN_PASSANT then (
      (* TODO: Check if move generation would still generate this move if
         we are in check, if that's the case, fix the below description! *)
      (* En passant would be legal as long as the king is not under attack after
         the move, i.e. this also handles the case where the king is already in
         check as capturing en passant never blocks checks. *)
      let king_sq = square_of_pt_and_colour pos Types.KING us in
      (* The captured pawn is one square behind our destination *)
      let captured_sq =
        Types.sq_sub_dir dst (Types.pawn_push_direction us) |> Stdlib.Option.get
      in
      let occupied =
        pieces pos |> Bitboard.sq_xor_bb src
        |> Bitboard.sq_xor_bb captured_sq
        |> Bitboard.sq_or_bb dst
      in
      assert (Types.equal_square dst (Stdlib.Option.get @@ ep_square pos));
      assert (
        Types.equal_piece (moved_piece_exn pos m) (Types.mk_piece us Types.PAWN));
      assert (
        Types.equal_piece
          (piece_on_exn pos captured_sq)
          (Types.mk_piece them Types.PAWN));
      assert (piece_on pos dst |> Option.is_none);
      (* Test that the king is not in ray of an enemy slider. *)
      Bitboard.bb_is_empty
        (Bitboard.attacks_bb_occupied Types.ROOK king_sq occupied
        |> Bitboard.bb_and
             (pieces_of_colour_and_pts pos them [ Types.QUEEN; Types.ROOK ]))
      && Bitboard.bb_is_empty
           (Bitboard.attacks_bb_occupied Types.BISHOP king_sq occupied
           |> Bitboard.bb_and
                (pieces_of_colour_and_pts pos them
                   [ Types.QUEEN; Types.BISHOP ])))
    else if Types.equal_move_type (Types.get_move_type m) Types.CASTLING then
      (* Castling moves generation does not check if the castling path is clear of
         enemy attacks, it relies on this function to verify that. *)

      (* After castling, the rook and king final positions are the same in
         Chess960 as they would be in standard chess. *)
      let dst =
        (* We store the position of the rook as the destination *)
        Types.relative_sq us
          (if Types.compare_square dst src > 0 then Types.G1 else Types.C1)
      in
      (* Get a direction that we will use to trace our steps to see if the
         king was ever exposed. *)
      let step =
        if Types.compare_square dst src > 0 then Types.WEST else Types.EAST
      in
      let rec is_path_safe curr_sq =
        (* Check all squares in the path between src (exclusive) and
           dst (inclusive) *)
        if Types.equal_square curr_sq src then true
        else if
          attackers_to_sq pos curr_sq
          |> Bitboard.bb_and @@ pieces_of_colour pos them
          |> Bitboard.bb_not_zero
        then false
        else is_path_safe (Types.sq_plus_dir curr_sq step |> Stdlib.Option.get)
      in
      (* In chess960, the rook could be shielding the king from some sideway
         attack, it which case we would not be able to castle, e.g.
         an enemy queen on A1 when the rook is on B1. *)
      is_path_safe dst
      && ((not chess960)
         || Bitboard.bb_is_empty
              (blockers_for_king pos us
              |> Bitboard.sq_and_bb @@ Types.move_dst m))
    else if
      Types.equal_piece_type Types.KING
      @@ Types.type_of_piece @@ piece_on_exn pos src
    then
      (* If the moving piece is a king, check whether the destination square is
         attacked by the opponent. *)
      attackers_to_occupied pos dst (pieces pos |> Bitboard.sq_xor_bb src)
      |> Bitboard.bb_and @@ pieces_of_colour pos them
      |> Bitboard.bb_is_empty
    else
      (* We have a non-king move, it would be legal as long as the piece is
         not pinned. If it is, then it needs to be moving along the ray between
         the king and the pinner. *)
      Bitboard.bb_and_sq (blockers_for_king pos us) src |> Bitboard.bb_is_empty
      || Bitboard.aligned src dst (square_of_pt_and_colour pos Types.KING us)

  (* Takes a random move and tests whether the move is
     pseudo-legal. It is used to validate moves from TT that can be corrupted
     due to SMP concurrent access or hash position key aliasing. *)
  (* TODO: This huge function must be unit tested *)
  let pseudo_legal ({ side_to_move = us; _ } as pos) m =
    let them = Types.other_colour us in
    let src = Types.move_src m in
    let dst = Types.move_dst m in
    let our_pieces = pieces_of_colour pos them in
    let their_pieces = pieces_of_colour pos them in
    let all_pieces = pieces pos in
    (* TODO: Figure out if null-moves may be passed to this fn. *)
    let piece = moved_piece pos m in

    (* Use a slower but simpler function for uncommon cases
       yet we skip the legality check of MoveList<LEGAL>(). *)
    if not @@ Types.equal_move_type (Types.get_move_type m) Types.NORMAL then
      failwith "TODO: Implement this after move generation is done"
    else (
      (* We know this is not a promotion, hence `ppt` should be None *)
      assert (Types.get_ppt m |> Option.is_none);
      match piece with
      | None -> false (* If there is no piece, the move is definitely illegal *)
      | Some piece ->
          let piece_type = Types.type_of_piece piece in
          (* If the moved piece doesn't belong to the side to move *)
          if not @@ Types.equal_colour us @@ Types.color_of_piece piece then
            false
            (* If the destination square is occupied by a friendly piece *)
          else if Bitboard.bb_not_zero (Bitboard.bb_and_sq our_pieces dst) then
            false
          else if
            (* Handle pawn moves:
               1. This can't be a promotion, hence the destination cannot be
               on the 1st and last ranks *)
            Types.equal_piece_type piece_type Types.PAWN
            && Bitboard.bb_not_zero
                 (Bitboard.bb_or Bitboard.rank_8 Bitboard.rank_1
                 |> Bitboard.sq_and_bb dst)
          then false
          else if
            (* 2. It must be either a capture, a single push, or double push *)
            Types.equal_piece_type piece_type Types.PAWN
            (* Not a capture *)
            && Bitboard.bb_is_empty
                 (Bitboard.pawn_attacks_bb_from_sq us src
                 |> Bitboard.bb_and their_pieces
                 |> Bitboard.sq_and_bb dst)
            (* Not a single push *)
            && (not
                  (Types.equal_square
                     (Types.sq_plus_dir src (Types.pawn_push_direction us)
                     |> Stdlib.Option.get)
                     dst
                  && is_empty pos dst))
            (* Not a double push *)
            && not
                 (Types.equal_square
                    (Types.sq_plus_dir_twice src (Types.pawn_push_direction us)
                    |> Stdlib.Option.get)
                    dst
                 (* Verify that pawn is on starting rank *)
                 && Types.equal_rank Types.RANK_2
                    @@ Types.relative_rank_of_sq us src
                 (* Verify that both squares in front of the pawn are empty *)
                 && is_empty pos dst
                 && is_empty pos
                      (Types.sq_sub_dir dst (Types.pawn_push_direction us)
                      |> Stdlib.Option.get))
          then false
          else if
            (* If its not a pawn, then the destination square must be a
               square that it attacks. *)
            (not @@ Types.equal_piece_type piece_type Types.PAWN)
            && Bitboard.bb_is_empty
                 (Bitboard.attacks_bb_occupied piece_type src all_pieces
                 |> Bitboard.sq_and_bb dst)
          then false
            (* Evasions generator already takes care to avoid some kind of
               illegal moves and legal() relies on this. We therefore have
               to take care that the same kind of moves are filtered out
               here. *)
          else if Bitboard.bb_not_zero @@ checkers pos then
            let checkers' = checkers pos in
            if not @@ Types.equal_piece_type Types.KING piece_type then
              (* There is more than one checker, hence moving the king
                 cannot be legal. *)
              if Bitboard.more_than_one checkers' then false
              else
                (* Since we are not moving the king, we must either capture
                   the attacker or interpose the check. *)
                Bitboard.bb_not_zero
                  (Bitboard.between_bb
                     (square_of_pt_and_colour pos Types.KING us)
                     (Bitboard.lsb checkers' |> Bitboard.bb_to_square)
                  |> Bitboard.sq_and_bb dst)
            else
              (* Ensure that we are not moving the king to another attacked
                 square. *)
              Bitboard.bb_is_empty
                (attackers_to_occupied pos dst
                   (Bitboard.bb_xor_sq all_pieces src)
                |> Bitboard.bb_and their_pieces)
          else true)
end

let%test_unit "dummy_test" = ()
