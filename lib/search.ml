open Base
open Movepick
open Position
open Types
module MP = MovePick
module P = Position
module TT = Transposition_table

module Search = struct
  type node_type = NON_PV | PV | ROOT [@@deriving eq]

  let dummy_ch = MP.PieceToHistory.make ()

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

  let mk_empty_stack () =
    {
      pv = [];
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
    main_history : MP.ButterflyHistory.t;
    counter_moves : MP.CounterMoveHistory.t;
    pawn_history : MP.PawnHistory.t;
    capture_history : MP.CapturePieceToHistory.t;
    continuation_history :
      (MP.ContinuationHistory.t * MP.ContinuationHistory.t)
      * (MP.ContinuationHistory.t * MP.ContinuationHistory.t);
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
    reductions : int array; (* TODO: Thread pool, UCI options*)
    tt : TT.t;
  }

  (* Futility margin
   *
   * no_tt_cut_node : The node does not have a TT hit, and is a cut node
   * improving : Whether the static eval since our last move (our the one
                 before that) *)
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
    let psi = MP.pawn_structure_index ~pht:MP.CORRECTION pos in
    let cv =
      MP.CorrectionHistory.find correction_history (P.side_to_move pos, psi)
    in
    let value = value + (cv * Int.abs cv / 12475) in
    (* Larger than min TB value but smaller than max TB value *)
    Int.clamp_exn value
      ~min:(Types.value_tb_loss_in_max_ply + 1)
      ~max:(Types.value_tb_win_in_max_ply - 1)

  (* History and stats update bonus, based on current search depth *)
  let stat_bonus d = Int.min ((246 * d) - 351) 1136

  (* History and stats update malus, based on depth *)
  let stat_malus d = Int.min ((519 * d) - 306) 1258

  (* Add a small random component to draw evaluations to avoid 3-fold blindness.
     This makes it so that we don't always search the same draw-ish lines during
     each iteration, making it less likely that we will miss something.
     See explanation: https://chess.stackexchange.com/questions/29530/stockfish-draw-value-randomization-and-3-fold-blindness*)
  let value_draw nodes = Types.value_draw - 1 + (nodes land 0x2)

  (*
   * Adjusts a mate or TB score from "plies to mate from the root"
   * to "plies to mate from the current position". Standard scores are unchanged.
   * The function is called before storing a value in the transposition table.
   *)
  let value_to_tt v ply =
    assert (v <> Types.value_none);
    if v >= Types.value_tb_win_in_max_ply then v + ply
    else if v <= Types.value_tb_loss_in_max_ply then v - ply
    else v

  (*
   * Inverse of value_to_tt(): it adjusts a mate or TB score
   * from the transposition table (which refers to the plies to mate/be mated from
   * current position) to "plies to mate/be mated (TB win/loss) from the root".
   * However, to avoid potentially false mate or TB scores related to the 50 moves rule
   * and the graph history interaction, we return the highest non-TB score instead.
   *)
  let value_from_tt v ply r50c =
    if v = Types.value_none then Types.value_none
    else if v >= Types.value_tb_win_in_max_ply then
      (* Handle tb win or better *)
      if
        (* Downgrade a potentially false mate score *)
        v >= Types.value_mate_in_max_ply && Types.value_mate - v > 100 - r50c
      then Types.value_tb_win_in_max_ply - 1
        (* Downgrade a potentially false tb score. *)
      else if Types.value_tb - v > 100 - r50c then
        Types.value_tb_win_in_max_ply - 1
      else v - ply
    else if v <= Types.value_tb_loss_in_max_ply then
      (* Handle tb loss or worse *)
      if
        (* Downgrade a potentially false mate score. *)
        v <= Types.value_mated_in_max_ply && Types.value_mate + v > 100 - r50c
      then Types.value_tb_loss_in_max_ply + 1
        (* Downgrade a potentially false tb score. *)
      else if Types.value_tb + v > 100 - r50c then
        Types.value_tb_loss_in_max_ply + 1
      else v + ply
    else v

  let reduction { reductions; root_delta; _ } i d mn delta =
    let reduction_scale = Array.get reductions d * Array.get reductions mn in
    ((reduction_scale + 1118 - (delta * 793 / root_delta)) / 1024)
    + Bool.to_int ((not i) && reduction_scale > 863)

  (* TODO: Implement skill limit *)

  let mk_worker _state _sm _thread_id = failwith "TODO"

  let get_from_ch { continuation_history = p1, p2; _ } ~in_check ~captures
      ~piece ~sq =
    let ch1, ch2 = if in_check then p2 else p1 in
    let ch = if captures then ch2 else ch1 in
    MP.ContinuationHistory.find ch (piece, sq)

  let update_pv pv move child_pv = child_pv @ (move :: pv)

  let optimism { optimism; _ } colour =
    let white_optimism, black_optimism = optimism in
    match colour with
    | Types.WHITE -> white_optimism
    | Types.BLACK -> black_optimism

  let update_continuation_histories stack ss piece dst bonus =
    let { in_check; _ } = Array.get stack ss in
    (* Only update the first 2 continuation histories if we are in check *)
    let idxs = if in_check then [ 1; 2 ] else [ 1; 2; 3; 4; 6 ] in
    List.iter idxs ~f:(fun i ->
        let ({ current_move; continuation_history; _ } as se) =
          Array.get stack (ss - i)
        in
        if Types.move_is_ok current_move then
          let continuation_history =
            MP.PieceToHistory.add continuation_history (piece, dst)
              (bonus / (1 + (3 * Bool.to_int (i = 3))))
          in

          Array.set stack (ss - 1) { se with continuation_history })

  (* Update move sorting heuristics *)
  let update_quiet_stats pos stack ss
      ({ main_history; counter_moves; _ } as worker) move bonus =
    let curr_se = Array.get stack ss in
    let k1, _k2 = curr_se.killers in
    (* Update killer moves *)
    let curr_se =
      (* Put the new move in the first slot and evict the second move *)
      if not @@ Types.equal_move k1 move then
        { curr_se with killers = (move, k1) }
      else curr_se
    in
    Array.set stack ss curr_se;
    let us = P.side_to_move pos in
    let main_history =
      MP.ButterflyHistory.add main_history
        (us, Types.move_src move, Types.move_dst move)
        bonus
    in
    update_continuation_histories stack ss
      (P.moved_piece_exn pos move)
      (Types.move_dst move) bonus;

    (* Update counter moves history *)
    let { current_move = previous_move; _ } = Array.get stack (ss - 1) in
    if Types.move_is_ok previous_move then
      let prev_sq = Types.move_dst previous_move in
      let prev_piece = P.piece_on_exn pos prev_sq in
      let counter_moves =
        MP.CounterMoveHistory.enter counter_moves (prev_piece, prev_sq) move
      in
      { worker with counter_moves; main_history }
    else { worker with main_history }

  (* Updates stats at the end of search() when a bestMove is found *)
  let update_all_stats pos stack ss
      ({ capture_history; pawn_history; main_history; _ } as worker) best_move
      best_value beta prev_sq quiets_searched captures_searched depth =
    let us = P.side_to_move pos in
    let moved_piece = P.moved_piece_exn pos best_move in

    let quiet_move_bonus = stat_bonus (depth + 1) in
    let quiet_move_malus = stat_malus depth in
    let worker =
      if not @@ P.is_capture_stage pos best_move then
        let best_move_bonus =
          if best_value > beta + 166 then (* larger bonus *)
            quiet_move_bonus
          else (* smaller bonus *)
            stat_bonus depth
        in

        (* Increase stats for the best move in case it was a quiet move *)
        let worker =
          update_quiet_stats pos stack ss worker best_move best_move_bonus
        in

        let p_index = MP.pawn_structure_index pos in
        let pawn_history =
          MP.PawnHistory.add pawn_history
            (p_index, moved_piece, Types.move_dst best_move)
            quiet_move_bonus
        in
        (* Decrease stats for all non-best quiet moves *)
        let pawn_history, main_history =
          List.fold
            ~init:(pawn_history, main_history)
            ~f:(fun (ph, mh) m ->
              let ph =
                MP.PawnHistory.add ph
                  (p_index, P.moved_piece_exn pos m, Types.move_dst m)
                  (-quiet_move_malus)
              in

              let mh =
                MP.ButterflyHistory.add mh
                  (us, Types.move_src m, Types.move_dst m)
                  (-quiet_move_malus)
              in

              update_continuation_histories stack ss (P.moved_piece_exn pos m)
                (Types.move_dst m) (-quiet_move_malus);
              (ph, mh))
            quiets_searched
        in
        { worker with pawn_history; main_history }
      else
        (* Increase stats for the best move in case it was a capture move *)
        let captured = P.piece_type_on_exn pos @@ Types.move_dst best_move in
        let capture_history =
          MP.CapturePieceToHistory.add capture_history
            (moved_piece, Types.move_dst best_move, captured)
            quiet_move_bonus
        in

        { worker with capture_history }
    in

    (* Extra penalty for a quiet early move that was not a TT move or
       main killer move in previous ply when it gets refuted. *)
    let prev_se = Array.get stack @@ (ss - 1) in

    (match prev_sq with
    | Some prev_sq
      when (prev_se.move_count = 1 + Bool.to_int prev_se.tt_hit
           || Types.equal_move prev_se.current_move (fst prev_se.killers))
           && (Option.is_none @@ P.captured_piece pos) ->
        update_continuation_histories stack (ss - 1)
          (P.piece_on_exn pos prev_sq)
          prev_sq (-quiet_move_malus)
    | _ -> ());

    let capture_history =
      List.fold ~init:worker.capture_history
        ~f:(fun ch m ->
          let moved_piece = P.moved_piece_exn pos m in
          let captured = P.piece_type_on_exn pos (Types.move_dst m) in

          MP.CapturePieceToHistory.add ch
            (moved_piece, Types.move_dst m, captured)
            (-quiet_move_malus))
        captures_searched
    in

    { worker with capture_history }

  let default_no_piece_cont_history = -71

  (*
   * Quiescence search function, which is called by the main search
   * function with zero depth, or recursively with further decreasing depth per call.
   *)
  let qsearch _worker _node_type _pos _stack _ss _alpha _beta _depth =
    failwith "TODO"

  let rec search ({ nodes; _ } as worker) node_type pos stack ss alpha beta
      depth is_cut_node : worker * Types.value =
    let is_pv = not @@ equal_node_type node_type NON_PV in
    let is_root = equal_node_type node_type ROOT in
    let maybe_get_draw_alpha alpha beta =
      if
        (not is_root) && alpha < Types.value_draw
        && P.has_game_cycle pos (Array.get stack ss).ply
      then
        let alpha = value_draw nodes in
        (alpha, alpha >= beta)
      else (alpha, false)
    in
    let us = P.side_to_move pos in
    let them = Types.other_colour us in
    let prior_capture = P.captured_piece pos |> Option.is_some in
    let rec step1 worker stack ss =
      let curr_se =
        {
          (Array.get stack ss) with
          in_check = BB.bb_not_zero (P.checkers pos);
          move_count = 0;
        }
      in
      let worker =
        if is_pv && worker.sel_depth < curr_se.ply + 1 then
          { worker with sel_depth = curr_se.ply + 1 }
        else worker
      in
      Array.set stack ss curr_se;
      let best_value = -Types.value_infinite in
      let max_value = Types.value_infinite in
      if not is_root then step2 worker stack ss best_value max_value
      else
        let worker = { worker with root_delta = beta - alpha } in
        step3_5 worker stack ss best_value max_value alpha beta
    and step2 worker stack ss best_value max_value =
      (* Step 2. Check for aborted search and immediate draw *)
      let { ply; in_check; _ } = Array.get stack ss in
      if P.is_draw pos ply || ply >= Types.max_ply then
        if ply >= Types.max_ply && not in_check then
          Evaluation.evaluate pos (optimism worker us)
        else (worker, value_draw worker.nodes)
      else step3 worker stack ss best_value max_value
    and step3 worker stack ss best_value max_value =
      (* Step 3. Mate distance pruning. Even if we mate at the next move our score
         would be at best mate_in(ss->ply + 1), but if alpha is already bigger because
         a shorter mate was found upward in the tree then there is no need to search
         because we will never beat the current alpha. Same logic but with reversed
         signs apply also in the opposite condition of being mated instead of giving
         mate. In this case, return a fail-high score. *)
      let { ply; _ } = Array.get stack ss in
      let alpha = Int.max (Types.mated_in ply) alpha in
      let beta = Int.min (Types.mate_in ply + 1) beta in
      if alpha >= beta then (worker, alpha)
      else step3_5 worker stack ss best_value max_value alpha beta
    and step3_5 worker stack ss best_value max_value alpha beta =
      let curr_se = Array.get stack ss in
      assert (0 <= curr_se.ply && curr_se.ply < Types.max_ply);
      Array.set stack (ss + 1)
        { (Array.get stack (ss + 1)) with excluded_move = Types.none_move };
      Array.set stack (ss + 2)
        {
          (Array.get stack (ss + 2)) with
          killers = (Types.none_move, Types.none_move);
          cut_off_count = 0;
        };
      let prev_se = Array.get stack (ss - 1) in
      let curr_se =
        {
          curr_se with
          multiple_extensions = prev_se.multiple_extensions;
          stat_score = 0;
        }
      in
      let prev_sq =
        if Types.move_is_ok prev_se.current_move then
          Some (Types.move_dst prev_se.current_move)
        else None
      in
      Array.set stack ss curr_se;
      step4 worker stack ss best_value max_value alpha beta prev_sq
    and step4 worker stack ss best_value max_value alpha beta prev_sq =
      (* Step 4. Transposition table lookup. *)
      let curr_se = Array.get stack ss in
      let excluded_move = curr_se.excluded_move in
      let is_excluded = not @@ Types.equal_move excluded_move Types.none_move in
      let pos_key = P.key pos in
      let tt_entry = TT.probe worker.tt pos_key in
      let curr_se, tt_value, tt_is_pv =
        match tt_entry with
        | Some entry ->
            ( { curr_se with tt_hit = true },
              value_from_tt entry.value curr_se.ply (P.rule50_count pos),
              entry.is_pv )
        | None -> ({ curr_se with tt_hit = false }, Types.value_none, false)
      in
      let tt_move =
        match (is_root, tt_entry) with
        | true, _ -> (List.hd_exn worker.root_moves).pv |> Utils.list_last_exn
        | false, Some entry -> entry.move
        | false, None -> Types.none_move
      in

      let tt_capture =
        Types.move_is_ok tt_move && P.is_capture_stage pos tt_move
      in
      (* Skip straight to step 6 if excluded *)
      if is_excluded then (
        Array.set stack ss curr_se;
        step6 worker stack ss best_value max_value alpha beta prev_sq true
          tt_entry tt_value tt_move tt_capture excluded_move)
      else
        let curr_se =
          { curr_se with tt_pv = is_pv || (curr_se.tt_hit && tt_is_pv) }
        in
        Array.set stack ss curr_se;
        (* At non-PV nodes we check for an early TT cutoff *)
        let early_tt_cutoff =
          match tt_entry with
          | Some tte ->
              (not is_pv) && (not is_excluded) && tte.depth > depth
              && TT.bound_contains tte.bound
                   (if tt_value >= beta then TT.BOUND_LOWER else TT.BOUND_UPPER)
          | None -> false
        in
        if early_tt_cutoff then
          let worker =
            if Types.move_not_none tt_move && tt_value >= beta then (
              let worker =
                (* Bonus for a quiet ttMove that fails high (~2 Elo) *)
                if not tt_capture then
                  update_quiet_stats pos stack ss worker tt_move
                    (stat_bonus depth)
                else worker
              in
              let prev_se = Array.get stack @@ (ss - 1) in

              (*
               * Extra penalty for early quiet moves of
               * the previous ply (~0 Elo on STC, ~2 Elo on LTC).
               *)
              (match prev_sq with
              | Some prev_sq when prev_se.move_count <= 2 && not prior_capture
                ->
                  update_continuation_histories stack ss
                    (P.piece_on_exn pos prev_sq)
                    prev_sq
                    (-stat_malus (depth + 1))
              | _ -> ());
              worker)
            else worker
          in
          if P.rule50_count pos < 90 then
            let ret_val =
              if
                tt_value >= beta
                && Int.abs tt_value < Types.value_tb_win_in_max_ply
              then ((tt_value * 3) + beta) / 4
              else tt_value
            in
            (worker, ret_val)
          else
            step5 worker stack ss best_value max_value alpha beta prev_sq
              tt_entry tt_value tt_move tt_capture excluded_move
        else
          step5 worker stack ss best_value max_value alpha beta prev_sq tt_entry
            tt_value tt_move tt_capture excluded_move
    and step5 worker stack ss best_value max_value alpha beta prev_sq tte
        tt_value tt_move tt_capture excluded_move =
      (* Step 5. Tablebases probe *)
      (* TODO: Implement this *)
      step6 worker stack ss best_value max_value alpha beta prev_sq false tte
        tt_value tt_move tt_capture excluded_move
    and step6 worker stack ss best_value max_value alpha beta prev_sq
        is_excluded tte tt_value tt_move tt_capture excluded_move =
      (* Step 6. Static evaluation of the position *)
      let ({ in_check; static_eval; tt_hit; _ } as se) = Array.get stack ss in

      if in_check then (
        (* Skip early pruning when in check *)
        Array.set stack ss { se with static_eval = Types.value_none };
        let improving = false in

        (* Go straight to moves loop *)
        step12 worker stack ss best_value max_value alpha beta depth improving
          excluded_move tte tt_capture tt_value tt_move Types.value_none prev_sq)
      else
        let unadjusted_static_eval, eval, se, tte =
          if is_excluded then
            (* TODO: NNUE stuff *)
            (static_eval, static_eval, se, tte)
          else if tt_hit then
            let tte' = Stdlib.Option.get tte in
            (* Never assume anything about values stored in TT *)
            let unadjusted_static_eval =
              if tte'.eval_value = Types.value_none then
                Evaluation.evaluate pos (optimism worker us)
              else tte'.eval_value
            in
            (* TODO: NNUE hint *)
            let eval =
              to_corrected_static_eval unadjusted_static_eval worker pos
            in
            let se = { se with static_eval = eval } in
            (* tt_value can be used as a better position evaluation (~7 Elo) *)
            let eval =
              if
                tt_value <> Types.value_none
                && TT.bound_contains tte'.bound
                     (if tt_value >= eval then TT.BOUND_LOWER
                      else TT.BOUND_UPPER)
              then tt_value
              else eval
            in

            (unadjusted_static_eval, eval, se, tte)
          else
            let unadjusted_static_eval =
              Evaluation.evaluate pos (optimism worker us)
            in
            let eval =
              to_corrected_static_eval unadjusted_static_eval worker pos
            in
            let se = { se with static_eval = eval } in

            (* Static evaluation is saved as it was before adjustment by
               correction history *)
            let tte =
              TT.store worker.tt ~key:(P.key pos) ~m:Types.none_move
                ~depth:Types.depth_none ~bound:TT.BOUND_NONE ~is_pv:se.tt_pv
                ~value:Types.value_none ~eval_value:unadjusted_static_eval
            in

            (unadjusted_static_eval, eval, se, Some tte)
        in
        Array.set stack ss se;

        (* Use static evaluation difference to improve quiet move ordering (~9 Elo) *)
        let prev_se = Array.get stack (ss - 1) in
        let worker =
          if
            Types.move_is_ok prev_se.current_move
            && (not prev_se.in_check) && not prior_capture
          then
            let bonus =
              Int.clamp_exn
                (-14 * (prev_se.static_eval + se.static_eval))
                ~min:(-1723) ~max:1455
            in
            (* TODO: What's the rationale behind this? *)
            let bonus = if bonus > 0 then 2 * bonus else bonus / 2 in
            let main_history =
              MP.ButterflyHistory.add worker.main_history
                ( them,
                  Types.move_src prev_se.current_move,
                  Types.move_dst prev_se.current_move )
                bonus
            in
            match prev_sq with
            | Some prev_sq
              when (not
                      (Types.equal_piece_type Types.PAWN
                      @@ P.piece_type_on_exn pos prev_sq))
                   && not
                      @@ Types.equal_move_type Types.PROMOTION
                      @@ Types.get_move_type prev_se.current_move ->
                let pawn_history =
                  MP.PawnHistory.add worker.pawn_history
                    ( MP.pawn_structure_index pos,
                      P.piece_on_exn pos prev_sq,
                      prev_sq )
                    (bonus / 4)
                in
                { worker with main_history; pawn_history }
            | _ -> { worker with main_history }
          else worker
        in
        (*
         * Set up the improving flag, which is true if current static evaluation is
         * bigger than the previous static evaluation at our turn (if we were in
         * check at our previous move we look at static evaluation at move prior to it
         * and if we were in check at move prior to it flag is set to true) and is
         * false otherwise. The improving flag is used in various pruning heuristics.
         *)
        let our_prev_static = (Array.get stack @@ (ss - 2)).static_eval in
        let improving =
          if our_prev_static <> Types.value_none then
            se.static_eval > our_prev_static
          else
            let our_prev_prev_static =
              (Array.get stack @@ (ss - 4)).static_eval
            in
            our_prev_prev_static <> Types.value_none
            && se.static_eval > our_prev_prev_static
        in

        step7 worker stack ss best_value max_value alpha beta is_excluded
          tt_move tt_capture tte tt_value unadjusted_static_eval eval improving
          excluded_move prev_sq
    and step7 worker stack ss best_value max_value alpha beta is_excluded
        tt_move tt_capture tte tt_value unadjusted_static_eval eval improving
        excluded_move prev_sq =
      (*
       * Step 7. Razoring (~1 Elo)
       * If eval is really low check with qsearch if it can exceed alpha, if it can't,
       * return a fail low.
       * Adjust razor margin according to cutoffCnt. (~1 Elo)
       *)
      let cut_off_count = (Array.get stack (ss + 1)).cut_off_count in
      if
        (* TODO: What's the logic behind this formula? *)
        eval
        < alpha - 438
          - ((332 - (154 * Bool.to_int (cut_off_count > 3))) * depth * depth)
      then
        let value = qsearch worker NON_PV pos stack ss (alpha - 1) alpha 0 in
        if value < alpha then (worker, value)
        else
          step8 worker stack ss best_value max_value alpha beta is_excluded
            tt_move tt_capture tte tt_value unadjusted_static_eval eval
            improving excluded_move prev_sq
      else
        step8 worker stack ss best_value max_value alpha beta is_excluded
          tt_move tt_capture tte tt_value unadjusted_static_eval eval improving
          excluded_move prev_sq
    and step8 worker stack ss best_value max_value alpha beta is_excluded
        tt_move tt_capture tte tt_value unadjusted_static_eval eval improving
        excluded_move prev_sq =
      (*
       * Step 8. Futility pruning: child node (~40 Elo)
       * The depth condition is important for mate finding.
       *)
      let { tt_pv; tt_hit; _ } = Array.get stack ss in
      let { stat_score = prev_stat_score; _ } = Array.get stack @@ (ss - 1) in
      if
        (not tt_pv) && depth < 11
        (* The eval is way too high, the minimising side would not allow
           this *)
        && eval
           - futility_margin depth (is_cut_node && not tt_hit) improving
           - (prev_stat_score / 314)
           >= beta
        && eval >= beta
        && eval < 30016 (* smaller than TB wins *)
        (* Don't prune if the TT move was a capture *)
        && (Types.move_not_none tt_move || tt_capture)
      then
        if beta > Types.value_tb_loss_in_max_ply then (worker, (eval + beta) / 2)
        else (worker, eval)
      else
        step9 worker stack ss best_value max_value alpha beta is_excluded
          unadjusted_static_eval eval tt_move tte tt_capture tt_value improving
          excluded_move prev_sq
    and step9 worker stack ss best_value max_value alpha beta is_excluded
        unadjusted_static_eval eval tt_move tte tt_capture tt_value improving
        excluded_move prev_sq =
      (* Step 9. Null move search with verification search (~35 Elo) *)
      let curr_se = Array.get stack ss in
      let prev_se = Array.get stack @@ (ss - 1) in
      if
        (not is_pv)
        && Types.move_not_null prev_se.current_move
        && prev_se.stat_score < 16620 && eval >= beta
        && eval >= curr_se.static_eval
        && curr_se.static_eval >= beta - (21 * depth) + 330
        && (not is_excluded)
        && P.non_pawn_material_for_colour pos us <> 0
        && curr_se.ply >= worker.nmp_min_ply
        && beta > Types.value_tb_loss_in_max_ply
      then (
        assert (eval - beta >= 0);
        (* Null move dynamic reduction based on depth and eval *)
        let r = Int.min ((eval - beta) / 154) 6 + (depth / 3) + 4 in
        let curr_se =
          {
            curr_se with
            current_move = Types.null_move;
            continuation_history =
              get_from_ch worker ~in_check:false ~captures:false ~piece:None
                ~sq:Types.A1;
          }
        in
        Array.set stack ss curr_se;
        let pos = P.do_null_move pos in
        let worker, null_value =
          search worker NON_PV pos stack (ss + 1) (-beta) (-beta + 1)
            (depth - r) (not is_cut_node)
        in
        let null_value = -null_value in
        let pos = P.undo_null_move pos in
        (* Do not return unproven mate or TB scores *)
        if null_value >= beta && null_value < Types.value_tb_win_in_max_ply then
          if worker.nmp_min_ply <> 0 || depth < 16 then (worker, null_value)
          else (
            (* Recursive verification is not allowed *)
            assert (worker.nmp_min_ply = 0);
            (* Do verification search at high depths, with null move pruning
               disabled until ply exceeds `nmp_min_ply`. *)
            let worker =
              { worker with nmp_min_ply = curr_se.ply + (3 * (depth - r) / 4) }
            in

            let worker, v =
              search worker NON_PV pos stack ss (beta - 1) beta (depth - r)
                false
            in
            let worker = { worker with nmp_min_ply = 0 } in

            if v >= beta then (worker, null_value)
            else
              step10 worker stack ss best_value max_value alpha beta
                unadjusted_static_eval tt_move tte tt_capture tt_value improving
                excluded_move prev_sq)
        else
          step10 worker stack ss best_value max_value alpha beta
            unadjusted_static_eval tt_move tte tt_capture tt_value improving
            excluded_move prev_sq)
      else
        step10 worker stack ss best_value max_value alpha beta
          unadjusted_static_eval tt_move tte tt_capture tt_value improving
          excluded_move prev_sq
    and step10 worker stack ss best_value max_value alpha beta
        unadjusted_static_eval tt_move tte tt_capture tt_value improving
        excluded_move prev_sq =
      (*
       * Step 10. Internal iterative reductions (~9 Elo)
       * For PV nodes without a ttMove, we decrease depth by 2,
       * or by 4 if the current position is present in the TT and
       * the stored depth is greater than or equal to the current depth.
       * Use qsearch if depth <= 0.
       *)
      let depth =
        if is_pv && (not @@ Types.move_not_none tt_move) then
          match tte with
          | Some tte when tte.depth >= depth -> depth - 4
          | _ -> depth - 2
        else depth
        (* TODO: CHECK that this depth is right? should it have been passed as an arg *)
      in
      if depth <= 0 then qsearch worker PV pos stack ss alpha beta 0
      else
        let depth =
          if is_cut_node && depth >= 8 && Types.move_is_none tt_move then
            depth - 2
          else depth
        in
        step11 worker stack ss best_value max_value alpha beta depth
          unadjusted_static_eval tt_move tte tt_capture tt_value improving
          excluded_move prev_sq
    and step11 ({ capture_history; _ } as worker) stack ss best_value max_value
        alpha beta depth unadjusted_static_eval tt_move tte tt_capture tt_value
        improving excluded_move prev_sq =
      (*
       * Step 11. ProbCut (~10 Elo)
       * If we have a good enough capture (or queen promotion) and a reduced search returns a value
       * much above beta, we can (almost) safely prune the previous move.
       *)
      let curr_se = Array.get stack ss in
      let prob_cut_beta = beta + 181 - (68 * Bool.to_int improving) in
      let tt_depth =
        match tte with Some tte -> tte.depth | None -> Types.depth_none
      in
      if
        (not is_pv) && depth > 3
        && Int.abs beta < Types.value_tb_win_in_max_ply
        (* If value from transposition table is lower than probCutBeta, don't
           attempt probCut there and in further interactions with transposition
           table cutoff depth is set to depth - 3 because probCut search has
           depth set to depth - 4 but we also do a move before it. So effective
           depth is equal to depth - 3 *)
        && not
             (tt_depth >= depth - 3
             && tt_value <> Types.value_none
             && tt_value < prob_cut_beta)
      then (
        assert (prob_cut_beta < Types.value_infinite && prob_cut_beta > beta);
        let mp =
          MP.mk_for_probcut ~pos ~tt_move
            ~threshold:(prob_cut_beta - curr_se.static_eval)
            ~cph:capture_history
        in
        let rec probcut_loop mp =
          let mp, move = MP.next_move mp in
          if Types.move_not_none move then
            if (not @@ Types.equal_move move excluded_move) && P.legal pos move
            then (
              assert (P.is_capture_stage pos move);
              let moved_piece = P.moved_piece pos move in
              let move_dst = Types.move_dst move in
              let curr_se = Array.get stack ss in
              let curr_se =
                {
                  curr_se with
                  current_move = move;
                  continuation_history =
                    get_from_ch worker ~in_check:curr_se.in_check ~captures:true
                      ~piece:moved_piece ~sq:move_dst;
                }
              in
              Array.set stack ss curr_se;
              let worker = { worker with nodes = worker.nodes + 1 } in
              let pos = P.do_move pos move (P.gives_check pos move) in

              (* Perform a preliminary qsearch to verify that the move holds *)
              let value =
                -qsearch worker NON_PV pos stack (ss + 1) (-prob_cut_beta)
                   (-prob_cut_beta + 1) 0
              in
              (* If the qsearch held, perform the regular search *)
              let worker, value =
                if value >= prob_cut_beta then
                  let worker, value =
                    search worker NON_PV pos stack (ss + 1) (-prob_cut_beta)
                      (-prob_cut_beta + 1) (depth - 4) (not is_cut_node)
                  in
                  (worker, -value)
                else (worker, value)
              in

              let pos = P.undo_move pos move in

              if value >= prob_cut_beta then
                let _ =
                  TT.store worker.tt ~key:(P.key pos)
                    ~value:(value_to_tt value curr_se.ply)
                    ~is_pv:curr_se.tt_pv ~bound:BOUND_LOWER ~depth:(depth - 3)
                    ~m:move ~eval_value:unadjusted_static_eval
                in
                let ret_val =
                  if Int.abs value < Types.value_tb_win_in_max_ply then
                    value - (prob_cut_beta - beta)
                  else value
                in
                (worker, ret_val)
              else probcut_loop mp)
            else probcut_loop mp
          else
            step12 worker stack ss best_value max_value alpha beta depth
              improving excluded_move tte tt_capture tt_value tt_move
              unadjusted_static_eval prev_sq
        in

        probcut_loop mp)
      else
        step12 worker stack ss best_value max_value alpha beta depth improving
          excluded_move tte tt_capture tt_value tt_move unadjusted_static_eval
          prev_sq
    and step12 worker stack ss best_value max_value alpha beta depth improving
        excluded_move tte tt_capture tt_value tt_move unadjusted_static_eval
        prev_sq =
      (* move_loop *)
      (* Step 12. A small Probcut idea, when we are in check (~4 Elo) *)
      let prob_cut_beta = beta + 452 in
      let curr_se = Array.get stack ss in
      match tte with
      | Some tte
        when curr_se.in_check && (not is_pv) && tt_capture
             && TT.bound_contains tte.bound TT.BOUND_LOWER
             && tte.depth >= depth - 4
             && tt_value >= prob_cut_beta
             && Int.abs tt_value < Types.value_tb_win_in_max_ply
             && Int.abs beta < Types.value_tb_win_in_max_ply ->
          (worker, prob_cut_beta)
      | _ ->
          let cont_hist =
            Array.of_list
              [
                (Array.get stack (ss - 1)).continuation_history;
                (Array.get stack (ss - 2)).continuation_history;
                (Array.get stack (ss - 3)).continuation_history;
                (Array.get stack (ss - 4)).continuation_history;
                dummy_ch;
                (Array.get stack (ss - 6)).continuation_history;
              ]
          in
          let counter_move =
            match prev_sq with
            | Some sq ->
                MP.CounterMoveHistory.find worker.counter_moves
                  (P.piece_on_exn pos sq, sq)
            | None -> Types.none_move
          in
          let mp =
            MP.mk ~pos ~tt_move ~depth ~mh:worker.main_history
              ~cph:worker.capture_history ~ch:cont_hist ~ph:worker.pawn_history
              ~killers:curr_se.killers ~counter_move
          in

          (* TODO: The best value might be from table base, fix this when we
             implement that. *)
          step13 worker stack ss best_value max_value Types.none_move alpha beta
            depth improving ([], []) tte tt_capture tt_value tt_move
            unadjusted_static_eval prev_sq excluded_move mp
            (-Types.value_infinite) false 0 cont_hist
    and step13 worker stack ss best_value max_value best_move alpha beta depth
        improving searched tte tt_capture tt_value tt_move
        unadjusted_static_eval prev_sq excluded_move mp value move_count_pruning
        move_count cont_hist =
      (*
       * Step 13. Loop through all pseudo-legal moves until no moves remain
       * or a beta cutoff occurs.
       *)
      let mp, move = MP.next_move ~skip_quiets:move_count_pruning mp in
      if Types.move_not_none move then (
        assert (Types.move_is_ok move);
        if Types.equal_move move excluded_move || (not @@ P.legal pos move) then
          step13 worker stack ss best_value max_value best_move alpha beta depth
            improving searched tte tt_capture tt_value tt_move
            unadjusted_static_eval prev_sq excluded_move mp value
            move_count_pruning move_count cont_hist
        else
          (* TOOD: See how the following works? *)
          (* At root obey the "searchmoves" option and skip moves not listed in Root
             Move List. In MultiPV mode we also skip PV moves that have been already
             searched and those of lower "TB rank" if we are in a TB root position.
             if (rootNode
                 && !std::count(thisThread->rootMoves.begin() + thisThread->pvIdx,
                                thisThread->rootMoves.begin() + thisThread->pvLast, move))
                 continue; *)
          (* TODO: Save this back to stack *)
          let curr_se = Array.get stack ss in
          let next_se = Array.get stack (ss + 1) in
          let move_count = move_count + 1 in
          let curr_se = { curr_se with move_count } in
          Array.set stack ss curr_se;
          (* TODO: Debug info here *)
          let next_se = if is_pv then { next_se with pv = [] } else next_se in
          Array.set stack (ss + 1) next_se;
          let capture = P.is_capture_stage pos move in
          let moved_piece = P.moved_piece_exn pos move in
          let gives_check = P.gives_check pos move in

          (* Calculate new depth for this move *)
          let new_depth = depth - 1 in

          let delta = beta - alpha in

          let r = reduction worker improving depth move_count delta in
          step14 worker stack ss best_value max_value best_move alpha beta depth
            tte tt_capture tt_value tt_move unadjusted_static_eval prev_sq
            excluded_move new_depth improving searched mp value move_count
            cont_hist move_count_pruning r move moved_piece capture gives_check)
      else
        step21 worker stack ss best_value max_value alpha beta depth
          unadjusted_static_eval prev_sq excluded_move move_count best_move
          searched
    and step14 worker stack ss best_value max_value best_move alpha beta depth
        tte tt_capture tt_value tt_move unadjusted_static_eval prev_sq
        excluded_move new_depth improving searched mp value move_count cont_hist
        move_count_pruning r move moved_piece capture gives_check =
      (*
       * Step 14. Pruning at shallow depth (~120 Elo).
       * Depth conditions are important for mate finding.
       *)
      (* Make it cleaner to perform the recursive call to skip to the next
         move *)
      let step13' () =
        step13 worker stack ss best_value max_value best_move alpha beta depth
          improving searched tte tt_capture tt_value tt_move
          unadjusted_static_eval prev_sq excluded_move mp value
          move_count_pruning move_count cont_hist
      in
      (* Proceed to next step, i.e. step 15 *)
      let step15' move_count_pruning =
        step15 worker stack ss best_value best_move max_value searched alpha
          beta depth excluded_move tte tt_capture tt_value tt_move prev_sq
          new_depth unadjusted_static_eval improving move_count r move
          moved_piece gives_check mp move_count_pruning cont_hist value
      in

      let curr_se = Array.get stack ss in
      if
        (not is_root)
        && P.non_pawn_material_for_colour pos us <> 0
        && best_value > Types.value_tb_loss_in_max_ply
      then
        (* Skip quiet moves if movecount exceeds our FutilityMoveCount
           threshold (~8 Elo) *)
        let move_count_pruning =
          if not move_count_pruning then
            move_count >= futility_move_count improving depth
          else move_count_pruning
        in
        (* Reduced depth of the next LMR search *)
        let lmr_depth = new_depth - r in

        let move_src = Types.move_src move in
        let move_dst = Types.move_dst move in
        if capture || gives_check then
          if
            (* Futility pruning for captures (~2 Elo) *)
            (not gives_check) && lmr_depth < 7 && not curr_se.in_check
          then
            let captured_piece = P.piece_on_exn pos move_dst in
            let futility_eval =
              curr_se.static_eval + 277 + (292 * lmr_depth)
              + Types.piece_value captured_piece
              + MP.CapturePieceToHistory.find worker.capture_history
                  ( moved_piece,
                    Types.move_dst move,
                    Types.type_of_piece captured_piece )
                / 7
            in
            if futility_eval < alpha then step13' ()
            else if not (P.see_ge pos move (-197 * depth)) then step13' ()
            else step15' move_count_pruning
          else if not (P.see_ge pos move (-197 * depth)) then step13' ()
          else
            let history =
              MP.PieceToHistory.find (Array.get cont_hist 0)
                (moved_piece, move_dst)
              + MP.PieceToHistory.find (Array.get cont_hist 1)
                  (moved_piece, move_dst)
              + MP.PieceToHistory.find (Array.get cont_hist 3)
                  (moved_piece, move_dst)
              + MP.PawnHistory.find worker.pawn_history
                  (MP.pawn_structure_index pos, moved_piece, move_dst)
            in

            (* Continuation history based pruning (~2 Elo) *)
            if lmr_depth < 6 && history < -4211 * depth then step13' ()
            else
              let history =
                history
                + 2
                  * MP.ButterflyHistory.find worker.main_history
                      (us, move_src, move_dst)
              in
              let lmr_depth = lmr_depth + (history / 6437) in
              (* Futility pruning: parent node (~13 Elo) *)
              if
                (not curr_se.in_check) && lmr_depth < 15
                && curr_se.static_eval
                   + (if best_value < curr_se.static_eval - 57 then 144 else 57)
                   + (121 * lmr_depth)
                   <= alpha
              then step13' ()
              else
                let lmr_depth = Int.max lmr_depth 0 in
                (* Prune moves with negative SEE (~4 Elo) *)
                if not @@ P.see_ge pos move (-26 * lmr_depth * lmr_depth) then
                  step13' ()
                else step15' move_count_pruning
        else step15' move_count_pruning
      else step15' move_count_pruning
    and step15 worker stack ss best_value best_move max_value searched alpha
        beta depth excluded_move tte tt_capture tt_value tt_move prev_sq
        new_depth unadjusted_static_eval improving move_count r move moved_piece
        gives_check mp move_count_pruning cont_hist value =
      (* Step 15. Extensions (~100 Elo)
         We take care to not overdo to avoid search getting stuck. *)
      let update_and_next_step extension depth new_depth =
        let curr_se = Array.get stack ss in
        let prev_se = Array.get stack @@ (ss - 1) in
        let new_depth = new_depth + extension in
        let curr_se =
          {
            curr_se with
            multiple_extensions =
              prev_se.multiple_extensions + Bool.to_int (extension >= 2);
            (* Update the current move (this must be done after singular extension search) *)
            current_move = move;
            continuation_history =
              get_from_ch worker ~in_check:curr_se.in_check
                ~captures:(P.is_capture_stage pos move)
                ~piece:(Some moved_piece) ~sq:(Types.move_dst move);
          }
        in
        Array.set stack ss curr_se;
        (* TODO: Use this when implementing `effort` *)
        let _node_count = if is_root then nodes else 0 in
        step16 worker stack ss best_value best_move max_value searched alpha
          beta depth excluded_move tte tt_capture tt_value tt_move prev_sq
          new_depth unadjusted_static_eval improving move_count r move
          moved_piece gives_check mp move_count_pruning cont_hist value
      in

      let curr_se = Array.get stack ss in
      if curr_se.ply < worker.root_depth * 2 then
        (* Singular extension search (~94 Elo). If all moves but one fail low on a
           search of (alpha-s, beta-s), and just one fails high on (alpha, beta),
           then that move is singular and should be extended. To verify this we do
           a reduced search on the position excluding the ttMove and if the result
           is lower than ttValue minus a margin, then we will extend the ttMove.

           Note: the depth margin and singularBeta margin are known for having non-linear
           scaling. Their values are optimized to time controls of 180+1.8 and longer
           so changing them requires tests at these types of time controls.
           Recursive singular search is avoided. *)
        match tte with
        | Some tte ->
            if
              (not is_root)
              && Types.equal_move move tt_move
              && Types.move_is_none excluded_move
              && depth
                 >= 4
                    - Bool.to_int (worker.completed_depth > 30)
                    + Bool.to_int curr_se.tt_pv
              && Int.abs tt_value < Types.value_tb_win_in_max_ply
              && TT.bound_contains tte.bound TT.BOUND_LOWER
              && tte.depth >= depth - 3
            then (
              let singular_beta =
                tt_value
                - (60 + (54 * Bool.to_int (curr_se.tt_pv && not is_pv)))
                  * depth / 64
              in
              let singular_depth = new_depth / 2 in
              Array.set stack ss { curr_se with excluded_move = move };
              let worker, value =
                search worker NON_PV pos stack ss (singular_beta - 1)
                  singular_beta singular_depth is_cut_node
              in
              let curr_se = Array.get stack ss in
              Array.set stack ss
                { curr_se with excluded_move = Types.none_move };

              if value < singular_beta then
                let extension, depth =
                  if (not is_pv) && curr_se.multiple_extensions <= 16 then
                    ( 2
                      + Bool.to_int
                          (value < singular_beta - 78 && not tt_capture),
                      depth + Bool.to_int (depth < 16) )
                  else (1, depth)
                in
                update_and_next_step extension depth new_depth
              else if singular_beta >= beta then
                (* Multi-cut pruning:
                   Our ttMove is assumed to fail high based on the bound of the TT entry,
                   and if after excluding the ttMove with a reduced search we fail high over the original beta,
                   we assume this expected cut-node is not singular (multiple moves fail high),
                   and we can prune the whole subtree by returning a softbound. *)
                (worker, singular_beta)
              else
                (* Negative extensions:
                   If other moves failed high over (ttValue - margin) without the ttMove on a reduced search,
                   but we cannot do multi-cut because (ttValue - margin) is lower than the original beta,
                   we do not know if the ttMove is singular or can do a multi-cut,
                   so we reduce the ttMove in favor of other moves based on some conditions: *)
                let extension =
                  (* If the ttMove is assumed to fail high over current beta (~7 Elo) *)
                  if tt_value >= beta then -2 - Bool.to_int (not is_pv)
                    (* If we are on a cutNode but the ttMove is not assumed to fail high over current beta (~1 Elo) *)
                  else if is_cut_node then -2
                    (* If the ttMove is assumed to fail low over the value of the reduced search (~1 Elo) *)
                  else if tt_value <= value then -1
                  else 0
                in
                update_and_next_step extension depth new_depth)
            else
              (* Recapture extensions (~1 Elo) *)
              let extension =
                match prev_sq with
                | Some prev_sq
                  when is_pv
                       && Types.equal_move move tt_move
                       && Types.equal_square (Types.move_dst move) prev_sq
                       && MP.CapturePieceToHistory.find worker.capture_history
                            ( moved_piece,
                              Types.move_dst move,
                              P.piece_type_on_exn pos (Types.move_dst move) )
                          > 4394 ->
                    1
                | _ -> 0
              in

              update_and_next_step extension depth new_depth
        | None -> update_and_next_step 0 depth new_depth
      else update_and_next_step 0 depth new_depth
    and step16 worker stack ss best_value best_move max_value searched alpha
        beta depth excluded_move tte tt_capture tt_value tt_move prev_sq
        new_depth unadjusted_static_eval improving move_count r move moved_piece
        gives_check mp move_count_pruning cont_hist value =
      (* Step 16. Make the move *)
      let curr_se = Array.get stack ss in
      let worker = { worker with nodes = worker.nodes + 1 } in
      let pos = P.do_move pos move gives_check in
      let tte_depth =
        match tte with Some tte -> tte.depth | _ -> Types.depth_none
      in

      (* Decrease reduction if position is or has been on the PV (~7 Elo) *)
      let r =
        if curr_se.tt_pv then
          r - 1
          + Bool.to_int (tt_value > alpha)
          + Bool.to_int (tte_depth >= depth)
        else r
      in

      (* Increase reduction for cut nodes (~4 Elo) *)
      let r =
        if is_cut_node then
          r + 2 - Bool.to_int (tte_depth >= depth && curr_se.tt_pv)
        else r
      in
      (* Increase reduction if ttMove is a capture (~3 Elo) *)
      let r = if tt_capture then r + 1 else r in
      (* Decrease reduction for PvNodes (~3 Elo) *)
      let r = if is_pv then r - 1 else r in
      (* Increase reduction on repetition (~1 Elo) *)
      let r =
        if
          Types.equal_move move (Array.get stack @@ (ss - 4)).current_move
          && P.has_repeated pos
        then r + 2
        else r
      in
      let r =
        (* Increase reduction if next ply has a lot of fail high (~5 Elo) *)
        if (Array.get stack @@ (ss + 1)).cut_off_count > 3 then r + 1
          (* Set reduction to 0 for first picked move (ttMove) (~2 Elo)
             Nullifies all previous reduction adjustments to ttMove and leaves only history to do them *)
        else if Types.equal_move move tt_move then 0
        else r
      in
      let stat_score =
        2
        * MP.ButterflyHistory.find worker.main_history
            (us, Types.move_src move, Types.move_dst move)
        + MP.PieceToHistory.find (Array.get cont_hist 0)
            (moved_piece, Types.move_dst move)
        + MP.PieceToHistory.find (Array.get cont_hist 1)
            (moved_piece, Types.move_dst move)
        + MP.PieceToHistory.find (Array.get cont_hist 3)
            (moved_piece, Types.move_dst move)
        - 4392
      in
      let curr_se = { curr_se with stat_score } in
      Array.set stack ss curr_se;

      (* Decrease/increase reduction for moves with a good/bad history (~8 Elo) *)
      let r = r - (stat_score / 14189) in

      let worker, value, new_depth =
        (* LMR *)
        if depth >= 2 && move_count > 1 + Bool.to_int is_root then
          step17 worker stack ss best_value pos new_depth r move moved_piece
          (* Full depth search *)
        else if (not is_pv) || move_count > 1 then
          let worker, value = step18 worker stack ss tt_move pos new_depth r in

          (worker, value, new_depth)
        else (worker, value, new_depth)
      in
      (* For PV nodes only, do a full PV search on the first move or after a fail high,
         otherwise let the parent node fail low with value <= alpha and try another move. *)
      let worker, value =
        if is_pv && (move_count = 1 || value > alpha) then (
          let next_se = Array.get stack @@ (ss + 1) in
          (* FIXME: Is the PV right? Should it be shared with the main function? *)
          Array.set stack (ss + 1) { next_se with pv = [ Types.none_move ] };

          search_inv worker PV pos stack (ss + 1) (-beta) (-alpha) new_depth
            false)
        else (worker, value)
      in

      step19 worker stack ss pos move move_count value best_value best_move
        max_value improving searched tte tt_capture tt_value tt_move
        unadjusted_static_eval prev_sq excluded_move mp move_count_pruning
        cont_hist
    and step17 worker stack ss best_value pos new_depth r move moved_piece =
      (* Step 17. Late moves reduction / extension (LMR, ~117 Elo) *)
      (*
       * In general we want to cap the LMR depth search at newDepth, but when
       * reduction is negative, we allow this move a limited search extension
       * beyond the first move depth. This may lead to hidden multiple extensions.
       * To prevent problems when the max value is less than the min value,
       * `clamp` has been replaced by a more robust implementation.
       *)
      let d = Int.max 1 (Int.min (new_depth - r) (new_depth + 1)) in
      let worker, value =
        search_inv worker NON_PV pos stack (ss + 1)
          (-(alpha + 1))
          (-alpha) d true
      in
      (* Do a full-depth search when reduced LMR search fails high *)
      if value > alpha && d < new_depth then (
        (* Adjust full-depth search based on LMR results - if the result
           was good enough search deeper, if it was bad enough search shallower. *)
        (* (~1 Elo) *)
        let do_deeper_search = value > best_value + 49 + (2 * new_depth) in
        (* (~2 Elo) *)
        let do_shallower_search = value < best_value + new_depth in

        let new_depth =
          new_depth
          + Bool.to_int do_deeper_search
          - Bool.to_int do_shallower_search
        in
        let worker, value =
          if new_depth > d then
            search_inv worker NON_PV pos stack (ss + 1)
              (-(alpha + 1))
              (-alpha) new_depth (not is_cut_node)
          else (worker, value)
        in
        (* Post LMR continuation history updates (~1 Elo) *)
        let bonus =
          if value <= alpha then -stat_malus new_depth
          else if value >= beta then stat_bonus new_depth
          else 0
        in
        update_continuation_histories stack ss moved_piece (Types.move_dst move)
          bonus;
        (worker, value, new_depth))
      else (worker, value, new_depth)
    and step18 worker stack ss tt_move pos new_depth r =
      (* Step 18. Full-depth search when LMR is skipped *)
      (* Increase reduction if ttMove is not present (~1 Elo) *)
      let r = if Types.move_is_none tt_move then r + 2 else r in

      (* Note that if expected reduction is high, we reduce search depth by 1 here (~9 Elo) *)
      search_inv worker NON_PV pos stack (ss + 1)
        (-(alpha + 1))
        (-alpha)
        (new_depth - Bool.to_int (r > 3))
        (not is_cut_node)
    and step19 worker stack ss pos move move_count value best_value best_move
        max_value improving searched tte tt_capture tt_value tt_move
        unadjusted_static_eval prev_sq excluded_move mp move_count_pruning
        cont_hist =
      let pos = P.undo_move pos move in
      (* TODO: Calculate effort *)
      assert (value > -Types.value_infinite && value < Types.value_infinite);

      step20 worker stack ss pos move move_count value best_value best_move
        max_value improving searched tte tt_capture tt_value tt_move
        unadjusted_static_eval prev_sq excluded_move mp move_count_pruning
        cont_hist
    and step20 worker (stack : stack array) ss pos move move_count value
        best_value best_move max_value improving searched tte tt_capture
        tt_value tt_move unadjusted_static_eval prev_sq excluded_move mp
        move_count_pruning cont_hist =
      (* Step 20. Check for a new best move *)

      (* TODO: Early stopping here *)
      let worker =
        if is_root then
          let update_rm rm =
            if root_move_eq_move rm move then
              let rm =
                {
                  rm with
                  avg_score =
                    (if rm.avg_score <> -Types.value_infinite then
                       ((2 * value) + rm.avg_score) / 3
                     else value);
                }
              in
              (* PV move or new best move? *)
              if move_count = 1 || value > alpha then
                let next_se = Array.get stack @@ (ss + 1) in
                let pv = next_se.pv @ [ List.last_exn rm.pv ] in
                let rm =
                  {
                    rm with
                    score = value;
                    uci_score = value;
                    sel_depth = worker.sel_depth;
                    score_lb = false;
                    score_ub = false;
                    pv;
                  }
                in
                let rm =
                  if value >= beta then
                    { rm with score_lb = true; uci_score = beta }
                  else if value <= alpha then
                    { rm with score_ub = true; uci_score = alpha }
                  else rm
                in

                rm
              else
                (* All other moves but the PV, are set to the lowest value: this
                   is not a problem when sorting because the sort is stable and the
                   move position in the list is preserved - just the PV is pushed up. *)
                { rm with score = -Types.value_infinite }
            else rm
          in

          let root_moves = List.map worker.root_moves ~f:update_rm in
          let worker =
            (* TODO: In MultiPV mode, we must take care to only do this for the
               first PV line. *)
            if value > alpha then
              {
                worker with
                best_move_changes = worker.best_move_changes + 1;
                root_moves;
              }
            else { worker with root_moves }
          in
          worker
        else worker
      in
      let transition_next_move (captures_searched, quiets_searched) best_value
          best_move depth alpha =
        (* If the move is worse than some previously searched move,
           remember it, to update its stats later. *)
        let searched =
          if (not (Types.equal_move move best_move)) && move_count <= 32 then
            if P.is_capture_stage pos move then
              (move :: captures_searched, quiets_searched)
            else (captures_searched, move :: quiets_searched)
          else (captures_searched, quiets_searched)
        in

        step13 worker stack ss best_value max_value best_move alpha beta depth
          improving searched tte tt_capture tt_value tt_move
          unadjusted_static_eval prev_sq excluded_move mp value
          move_count_pruning move_count cont_hist
      in

      if value > best_value then (
        let best_move = move in
        let curr_se = Array.get stack ss in
        let next_se = Array.get stack @@ (ss + 1) in
        let curr_se =
          (* Update pv even in fail-high case *)
          if is_pv && not is_root then
            { curr_se with pv = update_pv curr_se.pv move next_se.pv }
          else curr_se
        in
        if value >= beta then (
          (* Fail high *)
          let curr_se =
            {
              curr_se with
              cut_off_count =
                curr_se.cut_off_count + 1
                + (Bool.to_int @@ Types.move_is_none tt_move);
            }
          in
          Array.set stack ss curr_se;
          (* Skip to next move *)
          step13 worker stack ss best_value max_value best_move alpha beta depth
            improving searched tte tt_capture tt_value tt_move
            unadjusted_static_eval prev_sq excluded_move mp value
            move_count_pruning move_count cont_hist)
        else
          (* Reduce other moves if we have found at least one score improvement (~2 Elo) *)
          let depth =
            if depth > 2 && depth < 13 && beta < 13652 && value > -12761 then
              depth - 2
            else depth
          in

          assert (depth > 0);
          (* Update alpha! Always alpha < beta *)
          let alpha = value in
          Array.set stack ss curr_se;
          transition_next_move searched best_value best_move depth alpha)
      else transition_next_move searched best_value best_move depth alpha
    and step21 worker stack ss best_value max_value alpha beta depth
        unadjusted_static_eval prev_sq excluded_move move_count best_move
        (quiets_searched, captures_searched) =
      (* Step 21. Check for mate and stalemate
         All legal moves have been searched and if there are no legal moves, it
         must be a mate or a stalemate. If we are in a singular extension search then
         return a fail low score. *)
      let curr_se = Array.get stack ss in

      assert (
        move_count <> 0 || (not curr_se.in_check)
        || Types.move_not_none excluded_move
        || List.length @@ MG.generate MG.LEGAL pos = 0);
      (* Adjust best value for fail high cases at non-pv nodes *)
      let best_value =
        if
          (not is_pv) && best_value >= beta
          && Int.abs best_value < Types.value_tb_win_in_max_ply
          && Int.abs beta < Types.value_tb_win_in_max_ply
          && Int.abs alpha < Types.value_tb_win_in_max_ply
        then ((best_value * (depth + 2)) + beta) / (depth + 3)
        else best_value
      in
      let worker, best_value =
        if move_count = 0 then
          let v =
            if Types.move_not_none excluded_move then alpha
            else if curr_se.in_check then Types.mated_in curr_se.ply
            else Types.value_draw
          in
          (worker, v)
          (* If there is a move that produces search value greater than alpha we update the stats of searched moves *)
        else if Types.move_not_none best_move then
          let worker =
            update_all_stats pos stack ss worker best_move best_value beta
              prev_sq quiets_searched captures_searched depth
          in
          (worker, best_value)
        else
          (* Bonus for prior countermove that caused the fail low *)
          match prev_sq with
          | Some prev_sq when not prior_capture ->
              let prev_se = Array.get stack @@ (ss - 1) in
              let bonus =
                List.fold ~init:0
                  ~f:(fun acc e -> acc + Bool.to_int e)
                  [
                    depth > 5;
                    is_pv || is_cut_node;
                    prev_se.stat_score < -15736;
                    prev_se.move_count > 11;
                  ]
              in

              update_continuation_histories stack (ss - 1)
                (P.piece_on_exn pos prev_sq)
                prev_sq
                (bonus * stat_bonus depth);
              let main_history =
                MP.ButterflyHistory.add worker.main_history
                  ( Types.other_colour us,
                    Types.move_src prev_se.current_move,
                    Types.move_dst prev_se.current_move )
                  (stat_bonus depth * bonus / 2)
              in
              ({ worker with main_history }, best_value)
          | _ -> (worker, best_value)
      in
      let best_value =
        if is_pv then Int.min best_value max_value else best_value
      in
      let prev_se = Array.get stack @@ (ss - 1) in
      let curr_se =
        let curr_se = Array.get stack ss in

        (* If no good move is found and the previous position was ttPv, then the previous
           opponent move is probably good and the new position is added to the search tree. (~7 Elo) *)
        let curr_se =
          if best_value <= alpha then
            {
              curr_se with
              tt_pv = curr_se.tt_pv || (prev_se.tt_pv && depth > 3);
            }
          else curr_se
        in
        Array.set stack ss curr_se;
        curr_se
      in
      (* Write gathered information in transposition table
         Static evaluation is saved as it was before correction history *)
      (* FIXME: Support MultiPV *)
      (if Types.move_is_none excluded_move && not is_root then
         let bound =
           if best_value >= beta then TT.BOUND_LOWER
           else if is_pv && Types.move_not_none best_move then TT.BOUND_EXACT
           else TT.BOUND_UPPER
         in
         ignore
         @@ TT.store worker.tt ~key:(P.key pos)
              ~value:(value_to_tt best_value curr_se.ply)
              ~m:best_move ~is_pv:curr_se.tt_pv ~bound ~depth
              ~eval_value:unadjusted_static_eval);

      (* Adjust correction history *)
      let worker =
        if
          (not curr_se.in_check)
          && (Types.move_is_none best_move
             || (not @@ P.is_capture pos best_move))
          && (not (best_value >= beta && best_value <= curr_se.static_eval))
          && not
               (Types.move_is_none best_move
               && best_value >= curr_se.static_eval)
        then
          let bonus =
            Int.clamp_exn
              ((best_value - curr_se.static_eval) * depth / 8)
              ~min:(-MP.correction_history_limit / 4)
              ~max:(MP.correction_history_limit / 4)
          in
          let correction_history =
            MP.CorrectionHistory.add worker.correction_history
              (us, MP.pawn_structure_index ~pht:MP.CORRECTION pos)
              bonus
          in

          { worker with correction_history }
        else worker
      in

      assert (
        best_value > -Types.value_infinite && best_value < Types.value_infinite);

      (worker, best_value)
    in

    if depth <= 0 then
      qsearch worker
        (if is_pv then PV else NON_PV)
        pos stack ss alpha beta depth
    else
      let alpha, early_return = maybe_get_draw_alpha alpha beta in
      if early_return then (worker, alpha)
      else (
        (* Some sanity checks *)
        assert (
          -Types.value_infinite <= alpha
          && alpha < beta
          && beta <= Types.value_infinite);
        assert (is_pv || alpha = beta - 1);
        assert (0 < depth && depth < Types.max_ply);
        assert ((not @@ is_pv) && is_cut_node);

        step1 worker stack ss)

  (* Calls the search function but inverses the sign of the return val *)
  and search_inv worker node_type pos stack ss alpha beta depth is_cut_node =
    let worker, value =
      search worker node_type pos stack ss alpha beta depth is_cut_node
    in
    (worker, -value)

  (* Main iterative deepening loop *)
  let iterative_deepening ({ root_pos; _ } as worker) =
    (* let pv = Array.create ~len:(Types.max_ply + 1) Types.none_move in *)
    let pv = [] in
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
           * In case of failing low/high increase aspiration window 
           * exponentially and re-search, otherwise exit the loop.
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
          else (worker, best_value)
        in

        let worker, best_value = search_loop worker 0 alpha beta delta in

        (* SEARCH CODE END *)
        let worker = { worker with completed_depth = worker.root_depth } in
        let first_rm = List.hd_exn worker.root_moves in
        (* TODO: Handle premature stopping *)
        let last_best_pv, last_best_score, last_best_move_depth =
          (* Check the first move of the two PVs *)
          if
            not
            @@ Types.equal_move
                 (List.last_exn first_rm.pv)
                 (List.last_exn last_best_pv)
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
