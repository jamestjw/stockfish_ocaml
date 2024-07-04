open Base
open Movepick
open Position
open Types
module MP = MovePick
module P = Position

module Search = struct
  type node_type = NON_PV | PV | ROOT

  (*
   * Stack struct keeps track of the information we need to remember from nodes
   * shallower and deeper in the tree during the search. Each search thread has
   * its own array of Stack objects, indexed by the current ply.
   *)

  type stack = {
    pv : Types.move array;
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

  let mk_empty_stack () =
    {
      pv = Array.of_list [];
      continuation_history = MP.PieceToHistory.make ();
      ply = 0;
      current_move = Types.none_move;
      excluded_move = Types.none_move;
      killers = (Types.none_move, Types.none_move);
      static_eval = Types.value_zero;
      stat_score = 0;
      move_count = 0;
      in_check = false;
      tt_pv = false;
      tt_hit = false;
      multiple_extensions = 0;
      cut_off_count = 0;
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

  (* Consistent with root_move_lt *)
  let compare_root_move m1 m2 =
    Poly.compare (m2.score, m2.prev_score) (m1.score, m1.prev_score)

  let sort_root_moves rms = List.stable_sort rms ~compare:compare_root_move

  (* TODO: Implement LimitsType *)

  type depth = int

  (*
   * `worker` contains the data used by the thread that does the actual search.
   * It is instantiated once per thread, and it is responsible for keeping track
   * of the search history, and storing data required for the search.
   *)
  type worker = {
    correction_history : MP.CorrectionHistory.t;
    pv_idx : int;
    pv_last : int;
    nodes : int;
    tb_hits : int;
    best_move_changes : int;
    (* TODO: What's the meaning of the following 2 fields *)
    sel_depth : int;
    nmp_min_ply : int;
    optimism : Types.value * Types.value;
    root_pos : P.t;
    (* TODO: Maybe make this a dynamic array depending on how it's used *)
    root_moves : root_move list;
    root_depth : depth;
    completed_depth : depth;
    root_delta : Types.value; (* TODO: Whats this? *)
    (* thread_idx : int;  *)
    reductions : int array;
        (* TODO: Thread pool, UCI options and transposition table *)
  }

  (* Futility margin *)
  (* TODO: Document meaning of the 2nd and 3rd arguments *)
  let futility_margin depth no_tt_cut_node improving =
    let futility_mult = if no_tt_cut_node then 117 - 44 else 117 in
    (* The more the remaining the depth, the bigger the margin should be *)
    (futility_mult * depth) - (3 * futility_mult / 2 * Bool.to_int improving)

  (* TODO: Document meaning *)
  let futility_move_count improving depth =
    if improving then 3 + (depth * depth) else (3 + (depth * depth)) / 2

  (* Add correction_history value to raw static_eval and guarantee evaluation
     does not hit the tablebase range *)
  let to_corrected_static_eval value { correction_history; _ } pos =
    let psi = MP.pawn_structure_index MP.CORRECTION pos in
    let cv =
      MP.CorrectionHistory.find correction_history (P.side_to_move pos, psi)
    in
    let value = value + (cv * Int.abs cv / 12475) in
    (* Larger than min TB value but smaller than max TB value *)
    Int.clamp_exn value
      ~min:(Types.value_tb_loss_in_max_ply + 1)
      ~max:(Types.value_tb_win_in_max_ply - 1)

  (* TODO: Current search depth or remaining depth ? *)
  (* History and stats update bonus, based on depth *)
  let stat_bonus d = Int.min ((246 * d) - 351) 1136

  (* History and stats update malus, based on depth *)
  let stat_malus d = Int.min ((519 * d) - 306) 1258

  (* Add a small random component to draw evaluations to avoid 3-fold blindness.
     This makes it so that we don't always search the same draw-ish lines during
     each iteration, making it less likely that we will miss something.
     See explanation: https://chess.stackexchange.com/questions/29530/stockfish-draw-value-randomization-and-3-fold-blindness*)
  let value_draw nodes = Types.value_draw - 1 + (nodes land 0x2)

  (* TODO: Implement skill limit *)

  let mk_worker _state _sm _thread_id = failwith "TODO"

  (*
   * Quiescence search function, which is called by the main search
   * function with zero depth, or recursively with further decreasing depth per call.
   *)
  let qsearch _node_type _pos _stack _ss _alpha _beta _depth = failwith "TODO"

  let search _worker _node_type _pos _stack _ss _alpha _beta _depth _is_cut_node
      =
    failwith "TODO"

  (* Main iterative deepening loop *)
  let iterative_deepening ({ root_pos; _ } as worker) =
    let pv = Array.create ~len:(Types.max_ply + 1) Types.none_move in
    let us = P.side_to_move root_pos in

    (* TODO: Use this when we implement time management *)
    (* let time_reduction = 1. in *)
    (* PV variability metric *)
    (* TODO: Use this when we implement time management *)
    (* let to_best_move_changes = 0. in *)
    (* let iter_idx = 0 in *)

    (*
     * Allocate stack with extra size to allow access from (ss - 7) to (ss + 2):
     * (ss - 7) is needed for update_continuation_histories(ss - 1) which accesses (ss - 6),
     * (ss + 2) is needed for initialization of cutOffCnt and killers.

      * ss : Stack start index
     *)
    let ss = 7 in
    let stack =
      Array.init (Types.max_ply + 10) ~f:(fun i ->
          let s = mk_empty_stack () in
          if i < 7 then { s with static_eval = Types.value_none }
          else if 7 <= i && i <= 7 + Types.max_ply + 2 then
            { s with ply = i - 7; pv = (if i = ss then pv else s.pv) }
          else s)
    in

    (* TODO: Handle other threads when we do this in a multi-threaded fashion *)

    (* TODO: For now, only allow one PV? *)
    let _multi_pv = 1 in
    (* TODO: For now, hard code max depth? *)
    let depth_limit = 5 in

    let rec loop ({ root_depth; root_moves; _ } as worker) to_best_move_changes
        search_again_counter last_best_pv last_best_score last_best_move_depth
        _best_value =
      if root_depth < Types.max_ply && not (root_depth > depth_limit) then
        let to_best_move_changes = to_best_move_changes /. 2. in
        (*
         * Save the last iteration's scores before the first PV line is searched and
         * all the move scores except the (new) PV are set to -VALUE_INFINITE.
         *)
        let root_moves =
          List.map ~f:(fun rm -> { rm with prev_score = rm.score }) root_moves
        in

        let worker = { worker with root_moves } in

        (* Assume that we only have one PV line *)
        (* SEARCH CODE START *)

        (* FIXME: Generalise to more PVs  *)

        (* Reset aspiration window starting size *)
        let avg = (List.hd_exn root_moves).avg_score in
        let delta = 9 + (avg * avg / 12487) in
        let alpha = Int.max (avg - delta) (-Types.value_infinite) in
        let beta = Int.min (avg + delta) Types.value_infinite in

        (* Adjust optimism based on root move's averageScore (~4 Elo) *)
        let optimism =
          let value = 134 * avg / (Int.abs avg + 97) in
          match us with
          | Types.WHITE -> (value, -value)
          | Types.BLACK -> (-value, value)
        in

        let worker =
          {
            worker with
            (* Reset UCI info selDepth for each depth and each PV line *)
            sel_depth = 0;
            optimism;
          }
        in

        (*
         * Start with a small aspiration window and, in the case of a fail
         * high/low, re-search with a bigger window until we don't fail
         * high/low anymore.
         *)
        let rec search_loop worker failed_high_count alpha beta delta =
          (*
           * Adjust the effective depth searched, but ensure at least one effective increment
           * for every four searchAgain steps (see issue #2717).
           *)
          let adjusted_depth =
            Int.max 1
              (root_depth - failed_high_count
              - (3 * (search_again_counter + 1) / 4))
          in
          (* TODO: Should this modify root moves? *)
          let worker, best_value =
            search worker ROOT root_pos stack ss alpha beta adjusted_depth false
          in

          (*
           * Bring the best move to the front. It is critical that sorting
           * is done with a stable algorithm because all the values but the
           * first and eventually the new best one is set to -VALUE_INFINITE
           * and we want to keep the same order for all the moves except the
           * new PV that goes to the front. Note that in the case of MultiPV
           * search the already searched PV lines are preserved.
           *)
          let worker =
            { worker with root_moves = sort_root_moves worker.root_moves }
          in

          (*
           * In case of failing low/high increase aspiration window and
           * re-search, otherwise exit the loop.
           *)
          if best_value <= alpha then
            let beta = (alpha + beta) / 2 in
            let alpha = Int.max (best_value - delta) (-Types.value_infinite) in
            let delta = delta + (delta / 3) in
            search_loop worker 0 alpha beta delta
          else if best_value >= beta then
            let beta = Int.min (best_value + delta) Types.value_infinite in
            let delta = delta + (delta / 3) in
            search_loop worker (failed_high_count + 1) alpha beta delta
          else (
            (* TODO: What to return here? *)
            ignore @@ failwith "TODO";
            (worker, best_value))
        in

        let worker, best_value = search_loop worker 0 alpha beta delta in

        (* SEARCH CODE END *)
        let worker = { worker with completed_depth = worker.root_depth } in
        let first_rm = List.hd_exn worker.root_moves in
        let last_best_pv, last_best_score, last_best_move_depth =
          (* Check the first move of the two PVs *)
          if
            not
            @@ Types.equal_move
                 (List.hd_exn @@ List.rev first_rm.pv)
                 (List.hd_exn @@ List.rev last_best_pv)
          then (first_rm.pv, first_rm.score, worker.root_depth)
          else (last_best_pv, last_best_score, last_best_move_depth)
        in

        loop worker to_best_move_changes search_again_counter last_best_pv
          last_best_score last_best_move_depth best_value
      else
        (* Early stopping *)
        (worker, last_best_pv, last_best_score, last_best_move_depth)
    in
    let worker, _best_pv, _best_score, _best_move_depth =
      loop worker 0. 0 [ Types.none_move ] (-Types.value_infinite) 0
        (-Types.value_infinite)
    in
    worker

  let%test_unit "test_root_move_order" =
    let m1 =
      { (mk_root_move Types.none_move) with score = 10; prev_score = 30 }
    in
    let m2 =
      { (mk_root_move Types.none_move) with score = 15; prev_score = 5 }
    in
    let m3 =
      { (mk_root_move Types.none_move) with score = 15; prev_score = 10 }
    in
    let m4 =
      { (mk_root_move Types.none_move) with score = 15; prev_score = 20 }
    in
    let m5 =
      { (mk_root_move Types.none_move) with score = 20; prev_score = 0 }
    in

    [%test_result: bool] ~expect:true (root_move_lt m2 m1);
    [%test_result: int] ~expect:(-1) (compare_root_move m2 m1);
    [%test_result: int] ~expect:1 (compare_root_move m1 m2);
    [%test_result: int] ~expect:0 (compare_root_move m5 m5);
    [%test_result: bool] ~expect:true (root_move_lt m3 m2);
    [%test_result: int] ~expect:(-1) (compare_root_move m3 m2);
    [%test_result: int] ~expect:1 (compare_root_move m2 m3);
    [%test_result: bool] ~expect:true (root_move_lt m4 m3);
    [%test_result: int] ~expect:(-1) (compare_root_move m4 m3);
    [%test_result: int] ~expect:1 (compare_root_move m3 m4);
    [%test_result: int] ~expect:(-1) (compare_root_move m5 m1)
end
