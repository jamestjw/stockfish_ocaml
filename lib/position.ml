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
    (* FIXME: What in the world is EP square?! *)
    ep_square : Types.square;
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
    st : state_info list;
  }

  let side_to_move { side_to_move; _ } = side_to_move
  let piece_on { board; _ } sq = Array.get board (Types.square_to_enum sq)
  let is_empty pos sq = piece_on pos sq |> Option.is_none
  let moved_piece pos m = piece_on pos @@ Types.move_src m

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

  let ep_square { st; _ } =
    match st with
    | { ep_square; _ } :: _ -> ep_square
    | _ -> failwith "Empty state info list"

  (* See if any pieces are in the castling path *)
  let castling_impeded ({ castling_path; _ } as pos) cr =
    match cr with
    | Types.WHITE_OO | Types.WHITE_OOO | Types.BLACK_OO | Types.BLACK_OOO ->
        Bitboard.bb_and (pieces pos)
          (Array.get castling_path (Types.castling_right_to_enum cr))
        |> Bitboard.bb_not_zero
    | _ -> failwith "Invalid castling right"

  let castling_rook_square { castling_rook_square; _ } cr =
    match cr with
    | Types.WHITE_OO | Types.WHITE_OOO | Types.BLACK_OO | Types.BLACK_OOO ->
        Array.get castling_rook_square (Types.castling_right_to_enum cr)
    | _ -> failwith "Invalid castling right"

  (* Returns all the squares attacked by a certain colour *)
  let attacks_by pos pt colour =
    let rec helper threats attackers pt obstacles =
      if Bitboard.bb_not_zero attackers then
        let attacker, attackers = Bitboard.pop_lsb attackers in
        let attacker_sq = Bitboard.bb_to_square attacker in
        helper
          (Bitboard.bb_or threats
          @@ Bitboard.attacks_bb pt attacker_sq obstacles)
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

  let checkers { st; _ } = (List.hd_exn st).checkers_bb

  let blockers_for_king { st; _ } colour =
    Array.get (List.hd_exn st).blockers_for_king @@ Types.colour_to_enum colour

  let pinners { st; _ } colour =
    Array.get (List.hd_exn st).pinners @@ Types.colour_to_enum colour

  let check_squares { st; _ } colour =
    Array.get (List.hd_exn st).check_squares @@ Types.colour_to_enum colour

  (* Based on a congruential pseudo-random number generator *)
  let make_key seed =
    UInt64.mul seed @@ UInt64.of_string "6364136223846793005"
    |> UInt64.add @@ UInt64.of_string "1442695040888963407"

  let adjust_key50 { st; _ } after_move k =
    let rule50 = (List.hd_exn st).rule50 in
    let threshold = if after_move then 14 - 1 else 14 in
    if rule50 < threshold then k
    else UInt64.logor k @@ make_key (UInt64.of_int ((rule50 - threshold) / 8))

  let key ({ st; _ } as pos) = adjust_key50 pos false @@ (List.hd_exn st).key
  let pawn_key { st; _ } = (List.hd_exn st).pawn_key
  let material_key { st; _ } = (List.hd_exn st).material_key

  let non_pawn_material_for_colour { st; _ } colour =
    Array.get (List.hd_exn st).non_pawn_material @@ Types.colour_to_enum colour

  let non_pawn_material pos =
    non_pawn_material_for_colour pos Types.WHITE
    + non_pawn_material_for_colour pos Types.BLACK

  let game_ply { game_ply; _ } = game_ply

  (* FIXME: Document what this means *)
  let rule50_count { st; _ } = (List.hd_exn st).rule50
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

  let captured_piece { st; _ } = (List.hd_exn st).captured_piece

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
  let h1 h = UInt64.logand h @@ UInt64.of_int 0x1fff

  (* (h >> 16) & 0x1fff *)
  let h2 h = UInt64.shift_right h 16 |> UInt64.logand @@ UInt64.of_int 0x1fff

  (* Cuckoo tables with Zobrist hashes of valid reversible moves, and the moves themselves *)
  let cuckoo = Array.create ~len:8192 UInt64.zero
  let cuckooMove = Array.create ~len:8192 Types.none_move

  let zobrist_data =
    Random.init 42;
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
      Array.create ~len:(List.length Types.all_castling_rights) UInt64.zero
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
    List.iter Types.all_castling_rights ~f:(fun cr ->
        Array.set castling (Types.castling_right_to_enum cr) (gen_uint64 ()));
    { psq; en_passant; castling; side; no_pawns }
end
