open Base
open Unsigned
open Types

module type BITBOARD = sig
  type t

  val show : t -> string
  val sexp_of_t : t -> Sexp.t
  val compare : t -> t -> int
  val empty : t
  val file_A : t
  val file_B : t
  val file_C : t
  val file_D : t
  val file_E : t
  val file_F : t
  val file_G : t
  val file_H : t
  val rank_1 : t
  val rank_2 : t
  val rank_3 : t
  val rank_4 : t
  val rank_5 : t
  val rank_6 : t
  val rank_7 : t
  val rank_8 : t
  val square_bb : Types.square -> t
  val bb_and_sq : t -> Types.square -> t
  val bb_or_sq : t -> Types.square -> t
  val bb_xor_sq : t -> Types.square -> t
  val more_than_one : t -> bool
  val rank_bb : Types.rank -> t
  val rank_bb_of_sq : Types.square -> t
  val file_bb : Types.file -> t
  val file_bb_of_sq : Types.square -> t
  val shift : t -> Types.direction -> t

  (* bb contains the positions of all pawns of the given color *)
  val pawn_attacks_bb : Types.colour -> t -> t

  (* Squares attacked by a pawn of a given colour on a given square *)
  val pawn_attacks_bb_from_sq : Types.colour -> Types.square -> t

  (*
   * Returns a bitboard representing an entire line (from board edge
   * to board edge) that intersects the two given squares. If the given squares
   * are not on a same file/rank/diagonal, the function returns 0. For instance,
   * line_bb(SQ_C4, SQ_F7) will return a bitboard with the A2-G8 diagonal.
   *)
  val line_bb : Types.square -> Types.square -> t

  (*
   * Returns a bitboard representing the squares in the semi-open
   * segment between the squares s1 and s2 (excluding s1 but including s2). If the
   * given squares are not on a same file/rank/diagonal, it returns s2. For instance,
   * between_bb(SQ_C4, SQ_F7) will return a bitboard with squares D5, E6 and F7, but
   * between_bb(SQ_E6, SQ_F8) will return a bitboard with the square F8. This trick
   * allows to generate non-king evasion moves faster: the defending piece must either
   * interpose itself to cover the check or capture the checking piece.
   *)
  val between_bb : Types.square -> Types.square -> t

  (*
   * Returns true if the squares s1, s2 and s3 are aligned either on a
   * straight or on a diagonal line.
   * inline bool aligned(Square s1, Square s2, Square s3) { return line_bb(s1, s2) & s3; }
   *)
  val aligned : Types.square -> Types.square -> Types.square -> bool

  (* TODO: Implement this when required
   *
   * template<typename T1 = Square>
   * inline int distance(Square x, Square y);
   * 
   * template<>
   * inline int distance<File>(Square x, Square y) {
   *     return std::abs(file_of(x) - file_of(y));
   * }
   * 
   * template<>
   * inline int distance<Rank>(Square x, Square y) {
   *     return std::abs(rank_of(x) - rank_of(y));
   * }
   * 
   * template<>
   * inline int distance<Square>(Square x, Square y) {
   *     return SquareDistance[x][y];
   * }
   * 
   * FIXME: Why is this even in this file?! 
   * inline int edge_distance(File f) { return std::min(f, File(FILE_H - f)); }
   *)
  val lsb : t -> t
  val msb : t -> t
  val pop_lsb : t -> t * t
  val sq_distance : Types.square -> Types.square -> int
end

module Bitboard : BITBOARD = struct
  type t = UInt64.t

  let sexp_of_t t = Sexp.Atom (UInt64.to_string t)
  let compare = UInt64.compare
  let empty = UInt64.zero

  (* The first of every 8 bits is set, this is repeated 8 times *)
  let file_A = UInt64.of_int 0x0101010101010101
  let file_B = UInt64.shift_left file_A 1
  let file_C = UInt64.shift_left file_A 2
  let file_D = UInt64.shift_left file_A 3
  let file_E = UInt64.shift_left file_A 4
  let file_F = UInt64.shift_left file_A 5
  let file_G = UInt64.shift_left file_A 6
  let file_H = UInt64.shift_left file_A 7

  (* First 8 bits are set *)
  let rank_1 = UInt64.of_int 0xFF
  let rank_2 = UInt64.shift_left rank_1 (8 * 1)
  let rank_3 = UInt64.shift_left rank_1 (8 * 2)
  let rank_4 = UInt64.shift_left rank_1 (8 * 3)
  let rank_5 = UInt64.shift_left rank_1 (8 * 4)
  let rank_6 = UInt64.shift_left rank_1 (8 * 5)
  let rank_7 = UInt64.shift_left rank_1 (8 * 6)
  let rank_8 = UInt64.shift_left rank_1 (8 * 7)

  (* TODO: Implement this
   * extern uint8_t PopCnt16[1 << 16];
   * extern uint8_t SquareDistance[SQUARE_NB][SQUARE_NB];
   * extern Bitboard BetweenBB[SQUARE_NB][SQUARE_NB];
   * extern Bitboard LineBB[SQUARE_NB][SQUARE_NB];
   * extern Bitboard PseudoAttacks[PIECE_TYPE_NB][SQUARE_NB];
   * extern Bitboard PawnAttacks[COLOR_NB][SQUARE_NB];
   *)

  let square_bb sq =
    UInt64.shift_left (UInt64.of_int 1) (Types.square_to_enum sq)

  let bb_and_sq bb sq = UInt64.logand bb @@ square_bb sq
  let bb_or_sq bb sq = UInt64.logor bb @@ square_bb sq
  let bb_xor_sq bb sq = UInt64.logxor bb @@ square_bb sq
  let bb_not_zero bb = not @@ UInt64.equal bb UInt64.zero

  (* b & (b - 1) pops the least significant bit, so if the result is not zero
     then there was more than 1 bit in the original bb *)
  let more_than_one bb = bb_not_zero (UInt64.logand bb @@ UInt64.pred bb)

  let rank_bb = function
    | Types.RANK_1 -> rank_1
    | Types.RANK_2 -> rank_2
    | Types.RANK_3 -> rank_3
    | Types.RANK_4 -> rank_4
    | Types.RANK_5 -> rank_5
    | Types.RANK_6 -> rank_6
    | Types.RANK_7 -> rank_7
    | Types.RANK_8 -> rank_8

  let rank_bb_of_sq sq = Types.rank_of_sq sq |> rank_bb

  let file_bb = function
    | Types.FILE_A -> file_A
    | Types.FILE_B -> file_B
    | Types.FILE_C -> file_C
    | Types.FILE_D -> file_D
    | Types.FILE_E -> file_E
    | Types.FILE_F -> file_F
    | Types.FILE_G -> file_G
    | Types.FILE_H -> file_H

  let file_bb_of_sq sq = Types.file_of_sq sq |> file_bb

  let shift bb dir =
    match dir with
    | Types.NORTH -> UInt64.shift_left bb 8
    | Types.EAST ->
        (*  (bb & ~file_H) << 1 *)
        UInt64.logand bb @@ UInt64.lognot file_H |> Fn.flip UInt64.shift_left 1
    | Types.SOUTH -> UInt64.shift_right bb 8
    | Types.WEST ->
        (*  (bb & ~file_A) >> 1 *)
        UInt64.logand bb @@ UInt64.lognot file_A |> Fn.flip UInt64.shift_right 1
    | Types.NORTH_EAST ->
        UInt64.logand bb @@ UInt64.lognot file_H |> Fn.flip UInt64.shift_left 9
    | Types.SOUTH_EAST ->
        (*  (bb & ~file_H) >> 7 *)
        UInt64.logand bb @@ UInt64.lognot file_H |> Fn.flip UInt64.shift_right 7
    | Types.SOUTH_WEST ->
        (*  (bb & ~file_A) >> 9 *)
        UInt64.logand bb @@ UInt64.lognot file_A |> Fn.flip UInt64.shift_right 9
    | Types.NORTH_WEST ->
        (*  (bb & ~file_A) << 7 *)
        UInt64.logand bb @@ UInt64.lognot file_A |> Fn.flip UInt64.shift_left 7

  let pawn_attacks_bb colour bb =
    match colour with
    | Types.WHITE ->
        UInt64.logor (shift bb Types.NORTH_EAST) (shift bb Types.NORTH_WEST)
    | Types.BLACK ->
        UInt64.logor (shift bb Types.SOUTH_EAST) (shift bb Types.SOUTH_WEST)

  (* TODO: We should cache this in a table or pre-generate this *)
  let pawn_attacks_bb_from_sq colour sq = square_bb sq |> pawn_attacks_bb colour
  let line_bb _s1 _s2 = failwith "TODO!"
  let between_bb _s1 _s2 = failwith "TODO!"
  let aligned s1 s2 s3 = bb_not_zero @@ bb_and_sq (line_bb s1 s2) s3

  let lsb bb =
    (* Instead of doing bb & -bb, we do bb & (~bb + 1) *)
    UInt64.logand bb (UInt64.lognot bb |> UInt64.succ)

  let msb bb =
    let bb = UInt64.logor bb (UInt64.shift_right bb 1) in
    let bb = UInt64.logor bb (UInt64.shift_right bb 2) in
    let bb = UInt64.logor bb (UInt64.shift_right bb 4) in
    let bb = UInt64.logor bb (UInt64.shift_right bb 8) in
    let bb = UInt64.logor bb (UInt64.shift_right bb 16) in
    let bb = UInt64.logor bb (UInt64.shift_right bb 32) in
    UInt64.logor
      (UInt64.shift_right (UInt64.succ bb) 1)
      (UInt64.logand bb (UInt64.shift_left UInt64.one 63))

  let pop_lsb bb =
    let lsb = lsb bb in
    (lsb, UInt64.logand bb @@ UInt64.lognot lsb)

  let show bb =
    let res =
      List.fold ~init:"+---+---+---+---+---+---+---+---+\n"
        ~f:(fun acc rank ->
          let res =
            List.fold ~init:acc
              ~f:(fun acc file ->
                let to_add =
                  if bb_not_zero @@ bb_and_sq bb (Types.mk_square ~file ~rank)
                  then "| X "
                  else "|   "
                in
                acc ^ to_add)
              Types.all_files
          in
          res
          ^ Printf.sprintf "| %d\n\n+---+---+---+---+---+---+---+---+\n"
              (Types.rank_to_enum rank + 1))
        (List.rev Types.all_ranks)
    in
    res ^ "  a   b   c   d   e   f   g   h\n"

  (* Initialisation of bitboards *)

  (*
   * * template<>
   * * inline int distance<File>(Square x, Square y) {
   * *     return std::abs(file_of(x) - file_of(y));
   * * }
   * * 
   * * template<>
   * * inline int distance<Rank>(Square x, Square y) {
   * *     return std::abs(rank_of(x) - rank_of(y));
   * * }
   * * 
   * * template<>
   * * inline int distance<Square>(Square x, Square y) {
   * *     return SquareDistance[x][y];
   * * }
   *)
  let distance_by_file sq1 sq2 =
    Int.abs
      (Types.file_to_enum (Types.file_of_sq sq1)
      - Types.file_to_enum (Types.file_of_sq sq2))

  let distance_by_rank sq1 sq2 =
    Int.abs
      (Types.rank_to_enum (Types.rank_of_sq sq1)
      - Types.rank_to_enum (Types.rank_of_sq sq2))

  (* TODO: Should this be made lazy? *)
  let sq_distance_tbl =
    let tbl = Array.make_matrix ~dimx:64 ~dimy:64 0 in
    List.iter ~f:(fun (sq1, sq2) ->
        Array.set
          (Array.get tbl (Types.square_to_enum sq1))
          (Types.square_to_enum sq2)
          (Int.max (distance_by_file sq1 sq2) (distance_by_rank sq1 sq2)))
    @@ List.cartesian_product Types.all_squares Types.all_squares;

    tbl

  let sq_distance sq1 sq2 =
    Array.get
      (Array.get sq_distance_tbl (Types.square_to_enum sq1))
      (Types.square_to_enum sq2)

  let%test_unit "test_lsb" =
    [%test_result: t] ~expect:(UInt64.of_int 0b0010)
      (lsb @@ UInt64.of_int 0b1010);
    [%test_result: t] ~expect:(UInt64.of_int 0) (lsb @@ UInt64.of_int 0);
    [%test_result: t] ~expect:(UInt64.of_int 1) (lsb @@ UInt64.of_int 1)

  let%test_unit "test_msb" =
    [%test_result: t] ~expect:(UInt64.of_int 0b00100000)
      (msb @@ UInt64.of_int 0b00110100);
    [%test_result: t] ~expect:(UInt64.of_int 0b0010)
      (msb @@ UInt64.of_int 0b0010);
    [%test_result: t] ~expect:(UInt64.of_int 0b1) (msb @@ UInt64.one);
    [%test_result: t] ~expect:(UInt64.of_int 0b0) (msb @@ UInt64.zero);
    [%test_result: t]
      ~expect:(UInt64.shift_left UInt64.one 63)
      (msb @@ UInt64.max_int)

  let%test_unit "test_pop_lsb" =
    [%test_result: t * t]
      ~expect:(UInt64.of_int 0b100, UInt64.of_int 0b00110000)
      (pop_lsb @@ UInt64.of_int 0b00110100)
end

let%test_unit "test_more_than_one" =
  [%test_result: bool] ~expect:false
    (Bitboard.more_than_one @@ Bitboard.square_bb Types.E4);
  [%test_result: bool] ~expect:true (Bitboard.more_than_one Bitboard.rank_1);
  [%test_result: bool] ~expect:true (Bitboard.more_than_one Bitboard.file_G)

let%test_unit "test_shift" =
  [%test_result: Bitboard.t] ~expect:Bitboard.rank_2
    (Bitboard.shift Bitboard.rank_1 Types.NORTH);
  [%test_result: Bitboard.t] ~expect:Bitboard.rank_6
    (Bitboard.shift Bitboard.rank_7 Types.SOUTH);
  [%test_result: Bitboard.t] ~expect:Bitboard.file_B
    (Bitboard.shift Bitboard.file_A Types.EAST);
  [%test_result: Bitboard.t] ~expect:Bitboard.file_D
    (Bitboard.shift Bitboard.file_E Types.WEST);
  [%test_result: Bitboard.t]
    ~expect:(Bitboard.square_bb Types.E5)
    (Bitboard.shift (Bitboard.square_bb Types.D4) Types.NORTH_EAST);
  [%test_result: Bitboard.t]
    ~expect:(Bitboard.square_bb Types.F8)
    (Bitboard.shift (Bitboard.square_bb Types.G7) Types.NORTH_WEST);
  [%test_result: Bitboard.t]
    ~expect:(Bitboard.square_bb Types.H1)
    (Bitboard.shift (Bitboard.square_bb Types.G2) Types.SOUTH_EAST);
  [%test_result: Bitboard.t]
    ~expect:(Bitboard.square_bb Types.A4)
    (Bitboard.shift (Bitboard.square_bb Types.B5) Types.SOUTH_WEST)

(* TODO: Implement this after `line_bb` is implemented *)
let%test_unit "test_aligned" = ()

let%test_unit "test_sq_distance" =
  [%test_result: int] ~expect:4 (Bitboard.sq_distance Types.A1 Types.E4);
  [%test_result: int] ~expect:0 (Bitboard.sq_distance Types.A1 Types.A1);
  [%test_result: int] ~expect:1 (Bitboard.sq_distance Types.F6 Types.F5);
  [%test_result: int] ~expect:7 (Bitboard.sq_distance Types.H2 Types.A8)
