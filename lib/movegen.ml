open Base
open Types

module MoveGen = struct
  type gen_type =
    | CAPTURES
    | QUIETS
    | QUIET_CHECKS
    | EVASIONS
    | NON_EVASIONS
    | LEGAL
  [@@deriving eq]

  type move_list = Types.move list

  (* TODO: Figure out what `enemy` means *)
  (* TODO: Figure out what the `gen_types` here mean and why they influence
     move generation of promotions the way they do. *)
  let mk_promotions gt dir enemy move_list dst =
    let src = Types.sq_sub_dir dst dir |> Stdlib.Option.get in
    let all = match gt with EVASIONS | NON_EVASIONS -> true | _ -> false in
    let move_list =
      if equal_gen_type gt CAPTURES || all then
        Types.mk_move ~move_type:Types.PROMOTION ~ppt:Types.QUEEN dst src
        :: move_list
      else move_list
    in

    let move_list =
      if
        (equal_gen_type gt CAPTURES && enemy)
        || (equal_gen_type gt QUIETS && not enemy)
        || all
      then
        Types.mk_move ~move_type:Types.PROMOTION ~ppt:Types.ROOK dst src
        :: Types.mk_move ~move_type:Types.PROMOTION ~ppt:Types.BISHOP dst src
        :: Types.mk_move ~move_type:Types.PROMOTION ~ppt:Types.KNIGHT dst src
        :: move_list
      else move_list
    in
    move_list

  (* let generate_pawn_moves our_colour gt position move_list target = () *)
end
