open Base
open Movepick
open Position
open Types
module MP = MovePick

module Search = struct
  type node_type = NON_PV | PV | ROOT

  (*
   * Stack struct keeps track of the information we need to remember from nodes
   * shallower and deeper in the tree during the search. Each search thread has
   * its own array of Stack objects, indexed by the current ply.
   *)

  type stack = {
    pv : Types.move list;
    continuation_history : MP.PieceToHistory.t;
    ply : int;
    current_move : Types.move;
    excluded_move : Types.move;
    killers : Types.move * Types.move;
    static_eval : Types.value;
    stat_score : int; (* TODO: Whats this? *)
    move_count : int;
    in_check : bool;
    tt_pv : bool; (* TODO: Whether this node is a PV in the TT? *)
    tt_hit : bool;
    multiple_extensions : int;
    cut_off_count : int;
  }

  (*
   * RootMove struct is used for moves at the root of the tree. For each root move
   * we store a score and a PV (really a refutation in the case of moves which
   * fail low). Score is normally set at -VALUE_INFINITE for all non-pv moves.
   *)

  type root_move = {
    score : Types.value;
    prev_score : Types.value;
    avg_score : Types.value;
    uci_score : Types.value;
    (* Score lower and upper bound *)
    score_lb : bool;
    score_ub : bool;
    sel_depth : int;
    tb_rank : int;
    tb_score : int;
    pv : Types.move list;
  }

  let mk_root_move m =
    {
      score = -Types.value_infinite;
      prev_score = -Types.value_infinite;
      avg_score = -Types.value_infinite;
      uci_score = -Types.value_infinite;
      score_lb = false;
      score_ub = false;
      sel_depth = 0;
      tb_rank = 0;
      tb_score = 0;
      pv = [ m ];
    }

  (* Check if move is equal to the root of the PV *)
  let root_move_eq_move { pv; _ } m =
    List.rev pv |> List.hd_exn |> Types.equal_move m

  (* Sort in descending order *)
  let root_move_lt m1 m2 =
    if m1.score <> m2.score then m2.score < m1.score
    else m2.prev_score < m1.prev_score

  (* TODO: Implement LimitsType *)

  type depth = int

  (*
   * `worker` contains the data used by the thread that does the actual search.
   * It is instantiated once per thread, and it is responsible for keeping track
   * of the search history, and storing data required for the search.
   *)
  type worker = {
    pv_idx : int;
    pv_last : int;
    nodes : int;
    tb_hits : int;
    best_move_changes : int;
    (* TODO: What's the meaning of the following 2 fields *)
    sel_depth : int;
    nmp_min_ply : int;
    optimism : Types.value * Types.value;
    root_pos : Position.t;
    (* TODO: Maybe make this a dynamic array depending on how it's used *)
    root_moves : root_move list;
    root_depth : depth;
    completed_depth : depth;
    root_delta : Types.value; (* TODO: Whats this? *)
    (* thread_idx : int;  *)
    reductions : int array;
        (* TODO: Thread pool, UCI options and transposition table *)
  }
end
