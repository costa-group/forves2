Require Import Arith.   
Require Import Nat.  
Require Import Bool.
Require Import bbv.Word.
Require Import Coq.NArith.NArith.
Require Import Coq.NArith.Nnat.
Require Import List.
Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import FORVES2.constants.
Import Constants.

Require Import FORVES2.program.
Import Program.

Require Import FORVES2.execution_state.
Import ExecutionState.

Require Import FORVES2.stack_operation_instructions.
Import StackOpInstrs.

Require Import FORVES2.misc.
Import Misc.

Require Import FORVES2.symbolic_state.
Import SymbolicState.

Require Import FORVES2.symbolic_state_eval.
Import SymbolicStateEval.

Require Import FORVES2.symbolic_state_eval_facts.
Import SymbolicStateEvalFacts.
 
Require Import FORVES2.valid_symbolic_state.
Import ValidSymbolicState.

Require Import FORVES2.storage_ops_solvers.
Import StorageOpsSolvers.

Require Import FORVES2.storage_ops_solvers_impl.
Import StorageOpsSolversImpl.

Require Import FORVES2.symbolic_execution_soundness.
Import SymbolicExecutionSoundness.

Require Import FORVES2.sstack_val_cmp_impl_soundness.
Import SStackValCmpImplSoundness.

Require Import FORVES2.symbolic_state_cmp.
Import SymbolicStateCmp.

Require Import FORVES2.eval_common.
Import EvalCommon.

Require Import FORVES2.concrete_interpreter.
Import ConcreteInterpreter.

Require Import FORVES2.constraints.
Import Constraints.

Require Import FORVES2.context.
Import Context.

Require Import FORVES2.context_facts.
Import ContextFacts.

Require Import FORVES2.symbolic_execution_soundness.
Import SymbolicExecutionSoundness.

Module StorageOpsSolversImplSoundness.

  Lemma trivial_sload_solver_snd: sload_solver_ext_snd trivial_sload_solver.
  Proof.
    unfold sload_solver_ext_snd.
    unfold sload_solver_snd.
    intros.
    split.
    - unfold sload_solver_valid_res.
      intros.
      unfold trivial_sload_solver in H2.
      rewrite <- H2.
      simpl.
      intuition.
    - unfold sload_solver_correct_res.
      intros.
      unfold trivial_sload_solver in H3.
      rewrite <- H3 in H4.
      rewrite H4.
      exists idx1.
      exists m1.
      split; try reflexivity.
      intros.
      unfold eval_sstack_val.
      symmetry in H5.

      assert (H_valid_smap_value: valid_smap_value (get_maxidx_smap m) ops (SymSLOAD skey sstrg)). simpl. intuition.

      symmetry in H4.
      pose proof (add_to_smap_key_lt_maxidx m m1 idx1 (SymSLOAD skey sstrg) H4).
      pose proof (valid_sstack_val_freshvar (get_maxidx_smap m1) idx1 H6).
      symmetry in H4.
      pose proof (add_to_smap_valid_smap idx1 m m1 (SymSLOAD skey sstrg) ops H0 H_valid_smap_value H4).
      pose proof (eval_sstack_val'_succ (S (get_maxidx_smap m1)) (FreshVar idx1) model mem strg exts (get_maxidx_smap m1) (get_bindings_smap m1) ops H7 H8 (gt_Sn_n (get_maxidx_smap m1))).
      destruct H9 as [v H9].
      exists v.
      split; apply H9.
  Qed.

  
  Lemma trivial_sstorage_updater_snd: sstorage_updater_ext_snd trivial_sstorage_updater.
  Proof.
    unfold sstorage_updater_ext_snd.
    intros sstack_val_cmp H_valid_sstack_val_cmp.
    unfold sstorage_updater_snd.
    split.
    - unfold sstorage_updater_valid_res.
      intros ctx m sstrg sstrg' u ops H_valid_sstrg H_valid_u H_updater.
      unfold trivial_sstorage_updater in H_updater.
      rewrite <- H_updater.
      simpl.
      split.
      + apply H_valid_u.
      + apply H_valid_sstrg.
    - unfold sstorage_updater_correct_res.
      intros ctx m sstrg sstrg' u ops H_valid_smap H_valid_sstrg H_valid_u H_updater.
      unfold trivial_sstorage_updater in H_updater.
      rewrite <- H_updater.
      intros stk mem strg exts H_is_model.
      pose proof (valid_sstorage_when_extended_with_valid_update (get_maxidx_smap m) u sstrg H_valid_u H_valid_sstrg) as H_valid_u_sstrg.
      unfold valid_smap in H_valid_smap.
      pose proof (eval_sstorage_succ (get_maxidx_smap m) (get_bindings_smap m) stk mem strg exts ops (u::sstrg) H_valid_u_sstrg H_valid_smap) as H_eval_sstorage_u_sstrg.
      destruct H_eval_sstorage_u_sstrg as [sstrg'' H_eval_sstorage_u_sstrg].
      exists sstrg''.
      exists sstrg''.
      repeat split; apply H_eval_sstorage_u_sstrg.
  Qed.
  
  Lemma not_eq_keys_snd:
    forall ctx skey skey' maxidx sbindings ops,
      valid_bindings maxidx sbindings ops ->
      valid_sstack_value maxidx skey ->
      valid_sstack_value maxidx skey' ->
      not_eq_keys ctx skey skey' maxidx sbindings ops = true ->
      forall model mem strg exts,
        is_model (ctx_cs ctx) model = true ->
        exists v1 v2,
        eval_sstack_val' (S maxidx) skey model mem strg exts maxidx sbindings ops = Some v1 /\
          eval_sstack_val' (S maxidx) skey' model mem strg exts maxidx sbindings ops = Some v2 /\
          weqb v1 v2 = false.
  Proof.
 
    intros ctx skey skey' maxidx sbindings ops.
    intros H_valid_bs H_valid_skey H_valid_skey' H_neq.
    unfold not_eq_keys in H_neq.
    destruct (follow_in_smap skey maxidx sbindings) as [skey_m|] eqn:E_follow_skey; try discriminate.
    destruct skey_m; try discriminate.
    destruct smv; try discriminate.


    destruct (follow_in_smap skey' maxidx sbindings) as [skey'_m|] eqn:E_follow_skey'; try discriminate.
    destruct skey'_m; try discriminate.
    destruct smv; try discriminate.

    destruct val; destruct val0; try discriminate.
    intros model mem strg exts.
    intros H_is_model.
    unfold eval_sstack_val' at 1.
    rewrite E_follow_skey.
    unfold eval_sstack_val' at 1.
    rewrite E_follow_skey'.
    exists val.
    exists val0.
    split; try split; try reflexivity.
    rewrite negb_true_iff in H_neq.
    rewrite H_neq.
    reflexivity.

    intros model mem strg exts H_is_model.
    pose proof (eval_sstack_val'_succ (S maxidx) skey model mem strg exts maxidx sbindings ops H_valid_skey H_valid_bs (gt_Sn_n maxidx)) as H_eval_skey.
    pose proof (eval_sstack_val'_succ (S maxidx) skey' model mem strg exts maxidx sbindings ops H_valid_skey' H_valid_bs (gt_Sn_n maxidx)) as H_eval_skey'.
    destruct H_eval_skey as [v_skey H_eval_skey].
    destruct H_eval_skey' as [v_skey' H_eval_skey'].
    exists v_skey.
    exists v_skey'.
    repeat split; try auto.
    unfold eval_sstack_val' in H_eval_skey.
    rewrite E_follow_skey in H_eval_skey.
    injection H_eval_skey as H_eval_skey.
    unfold eval_sstack_val' in H_eval_skey'.
    rewrite E_follow_skey' in H_eval_skey'.
    injection H_eval_skey' as H_eval_skey'.
            
    pose proof (chk_neq_wrt_ctx_snd ctx (Val val) (InVar var) H_neq model mem strg exts maxidx sbindings ops H_is_model) as H_chk_neq_wrt_ctx_snd.
    destruct H_chk_neq_wrt_ctx_snd as [v1 [v2 [H_chk_neq_wrt_ctx_snd_1 [H_chk_neq_wrt_ctx_snd_2 H_chk_neq_wrt_ctx_snd_3]]]].
    
    pose proof (eval_sstack_val_Val val model mem strg exts maxidx sbindings ops) as H_eval_val.
    rewrite H_eval_val in H_chk_neq_wrt_ctx_snd_1.
    injection H_chk_neq_wrt_ctx_snd_1 as H_chk_neq_wrt_ctx_snd_1.
    pose proof (eval_sstack_val_InVar var model mem strg exts maxidx sbindings ops) as H_eval_var.
    rewrite H_eval_var in H_chk_neq_wrt_ctx_snd_2.
    injection H_chk_neq_wrt_ctx_snd_2 as H_chk_neq_wrt_ctx_snd_2.

    rewrite <- H_eval_skey.
    rewrite <- H_eval_skey'.
    rewrite  H_chk_neq_wrt_ctx_snd_1.
    rewrite  H_chk_neq_wrt_ctx_snd_2.
    apply H_chk_neq_wrt_ctx_snd_3.


    intros model mem strg exts H_is_model.
    pose proof (eval_sstack_val'_succ (S maxidx) skey model mem strg exts maxidx sbindings ops H_valid_skey H_valid_bs (gt_Sn_n maxidx)) as H_eval_skey.
    pose proof (eval_sstack_val'_succ (S maxidx) skey' model mem strg exts maxidx sbindings ops H_valid_skey' H_valid_bs (gt_Sn_n maxidx)) as H_eval_skey'.
    destruct H_eval_skey as [v_skey H_eval_skey].
    destruct H_eval_skey' as [v_skey' H_eval_skey'].
    exists v_skey.
    exists v_skey'.
    repeat split; try auto.
    unfold eval_sstack_val' in H_eval_skey.
    rewrite E_follow_skey in H_eval_skey.
    injection H_eval_skey as H_eval_skey.
    unfold eval_sstack_val' in H_eval_skey'.
    rewrite E_follow_skey' in H_eval_skey'.
    injection H_eval_skey' as H_eval_skey'.
            
    pose proof (chk_neq_wrt_ctx_snd ctx (InVar var) (Val val) H_neq model mem strg exts maxidx sbindings ops H_is_model) as H_chk_neq_wrt_ctx_snd.
    destruct H_chk_neq_wrt_ctx_snd as [v1 [v2 [H_chk_neq_wrt_ctx_snd_1 [H_chk_neq_wrt_ctx_snd_2 H_chk_neq_wrt_ctx_snd_3]]]].
    
    pose proof (eval_sstack_val_Val val model mem strg exts maxidx sbindings ops) as H_eval_val.
    rewrite H_eval_val in H_chk_neq_wrt_ctx_snd_2.
    injection H_chk_neq_wrt_ctx_snd_2 as H_chk_neq_wrt_ctx_snd_2.
    pose proof (eval_sstack_val_InVar var model mem strg exts maxidx sbindings ops) as H_eval_var.
    rewrite H_eval_var in H_chk_neq_wrt_ctx_snd_1.
    injection H_chk_neq_wrt_ctx_snd_1 as H_chk_neq_wrt_ctx_snd_1.

    rewrite <- H_eval_skey.
    rewrite <- H_eval_skey'.
    rewrite  H_chk_neq_wrt_ctx_snd_1.
    rewrite  H_chk_neq_wrt_ctx_snd_2.
    apply H_chk_neq_wrt_ctx_snd_3.


    intros model mem strg exts H_is_model.
    pose proof (eval_sstack_val'_succ (S maxidx) skey model mem strg exts maxidx sbindings ops H_valid_skey H_valid_bs (gt_Sn_n maxidx)) as H_eval_skey.
    pose proof (eval_sstack_val'_succ (S maxidx) skey' model mem strg exts maxidx sbindings ops H_valid_skey' H_valid_bs (gt_Sn_n maxidx)) as H_eval_skey'.
    destruct H_eval_skey as [v_skey H_eval_skey].
    destruct H_eval_skey' as [v_skey' H_eval_skey'].
    exists v_skey.
    exists v_skey'.
    repeat split; try auto.
    unfold eval_sstack_val' in H_eval_skey.
    rewrite E_follow_skey in H_eval_skey.
    injection H_eval_skey as H_eval_skey.
    unfold eval_sstack_val' in H_eval_skey'.
    rewrite E_follow_skey' in H_eval_skey'.
    injection H_eval_skey' as H_eval_skey'.
            
    pose proof (chk_neq_wrt_ctx_snd ctx (InVar var) (InVar var0) H_neq model mem strg exts maxidx sbindings ops H_is_model) as H_chk_neq_wrt_ctx_snd.
    destruct H_chk_neq_wrt_ctx_snd as [v1 [v2 [H_chk_neq_wrt_ctx_snd_1 [H_chk_neq_wrt_ctx_snd_2 H_chk_neq_wrt_ctx_snd_3]]]].
    
    pose proof (eval_sstack_val_InVar var0 model mem strg exts maxidx sbindings ops) as H_eval_var0.
    rewrite H_eval_var0 in H_chk_neq_wrt_ctx_snd_2.
    injection H_chk_neq_wrt_ctx_snd_2 as H_chk_neq_wrt_ctx_snd_2.
    pose proof (eval_sstack_val_InVar var model mem strg exts maxidx sbindings ops) as H_eval_var.
    rewrite H_eval_var in H_chk_neq_wrt_ctx_snd_1.
    injection H_chk_neq_wrt_ctx_snd_1 as H_chk_neq_wrt_ctx_snd_1.

    rewrite <- H_eval_skey.
    rewrite <- H_eval_skey'.
    rewrite  H_chk_neq_wrt_ctx_snd_1.
    rewrite  H_chk_neq_wrt_ctx_snd_2.
    apply H_chk_neq_wrt_ctx_snd_3.

Qed.      

Lemma H_map_o_sstrg:
  forall ctx d model mem strg exts maxidx bs ops sstrg,
    valid_sstorage maxidx sstrg ->
    valid_bindings maxidx bs ops ->
    d > maxidx ->
    is_model (ctx_cs ctx) model = true ->
    exists v,
      map_option (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val' d sv model mem strg exts maxidx bs ops)) sstrg = Some v.
Proof.
induction sstrg as [|u sstrg' IHsstrg'].
+ intros. simpl. exists []. reflexivity.
+ intros H_valid_sstorage H_valid_bs H_d_gt_maxidx H_is_model.
  unfold map_option.
  rewrite <- map_option_ho.
  unfold instantiate_storage_update at 1.
  destruct u as [skey' svalue'].
                            
  unfold valid_sstorage in H_valid_sstorage. fold valid_sstorage in H_valid_sstorage.
  destruct H_valid_sstorage as [H_valid_sstorage_0 H_valid_sstorage_1].
  unfold valid_sstorage_update in H_valid_sstorage_0.
  destruct H_valid_sstorage_0 as [H_valid_sstorage_0_0 H_valid_sstorage_0_1].

  pose proof (eval_sstack_val'_succ d skey' model mem strg exts maxidx bs ops H_valid_sstorage_0_0 H_valid_bs H_d_gt_maxidx) as eval_sstack_val'_succ_0.
  
  destruct eval_sstack_val'_succ_0 as [v eval_sstack_val'_succ_0].
  rewrite eval_sstack_val'_succ_0.
  pose proof (eval_sstack_val'_succ d svalue' model mem strg exts maxidx bs ops H_valid_sstorage_0_1 H_valid_bs H_d_gt_maxidx) as eval_sstack_val'_succ_1.
  destruct eval_sstack_val'_succ_1 as [v' eval_sstack_val'_succ_1].
  rewrite eval_sstack_val'_succ_1.

  pose proof (IHsstrg' H_valid_sstorage_1 H_valid_bs H_d_gt_maxidx H_is_model) as IHsstrg'_0.
  destruct IHsstrg'_0 as [v'' IHsstrg'_0].
  rewrite IHsstrg'_0.
  exists (U_SSTORE EVMWord v v' :: v'').
  reflexivity.
  Qed.

Lemma ssload_sstore_same_address:
  forall strg addr value,
    (sload
       (sstore strg addr value) addr) = value.
Proof.
  intros strg addr value.
  unfold sstore.
  unfold sload.
  rewrite N.eqb_refl with (x:= (wordToN addr)).
  reflexivity.
Qed.  


Lemma eval_sstack_val'_immediate_fresh_var:
  forall d idx model mem strg exts value bs ops,
  eval_sstack_val' d (FreshVar idx) model mem strg exts (S idx) ((idx, SymBasicVal value) :: bs) ops =
    eval_sstack_val' d value model mem strg exts idx bs ops.
Proof.
  intros d idx model mem strg exts value bs ops.
  destruct d as [|d']; try reflexivity.
  destruct value as [v|i|i] eqn:E_value.
  + unfold eval_sstack_val'  at 1.
    fold eval_sstack_val'.
    rewrite follow_smap_first_match; try reflexivity.
    unfold eval_sstack_val'  at 1.
    fold eval_sstack_val'.
    rewrite follow_smap_V.
    reflexivity.
  + unfold eval_sstack_val'  at 1.
    fold eval_sstack_val'.
    rewrite follow_smap_first_match; try reflexivity.
    unfold eval_sstack_val'  at 1.
    fold eval_sstack_val'.
    rewrite follow_smap_InStackVar.
    reflexivity.
  + unfold eval_sstack_val'  at 1.
    fold eval_sstack_val'.
    unfold follow_in_smap.
    fold follow_in_smap.
    rewrite Nat.eqb_refl.
    unfold is_fresh_var_smv.
    unfold eval_sstack_val'  at 9.
    fold eval_sstack_val'.
    reflexivity.
Qed.    

Lemma basic_sload_solver_snd: sload_solver_ext_snd basic_sload_solver.
  Proof.
    unfold sload_solver_ext_snd.
    intros sstack_val_cmp H_sstack_val_cmp_snd.
    unfold sload_solver_snd.
    split.

    (* valid *)
    - unfold sload_solver_valid_res.      
      intros ctx m sstrg skey smv ops.
      induction sstrg as [|u sstrg' IH_sstrg'].
      + intros H_valid_sstrg H_valid_skey H_smv.
        simpl in H_smv.
        rewrite <- H_smv.
        simpl.
        auto.
      + intros H_valid_sstrg H_valid_skey H_smv.
        unfold basic_sload_solver in H_smv.
        fold basic_sload_solver in H_smv.
        destruct u as [skey' svalue] eqn:E_u.
        destruct (sstack_val_cmp (S (get_maxidx_smap m)) ctx skey skey' (get_maxidx_smap m) (get_bindings_smap m) (get_maxidx_smap m) (get_bindings_smap m) ops) eqn:H_sstack_val_cmp_skey_skey'.
        ++ rewrite <- H_smv.
           simpl.
           apply H_valid_sstrg.
        ++ simpl in H_valid_sstrg.
           destruct H_valid_sstrg as [ [H_valid_skey' H_valid_svalue] H_valid_sstrg'].
           destruct (not_eq_keys ctx skey skey' (get_maxidx_smap m) (get_bindings_smap m)) eqn:E_not_eq_keys.
           +++ pose proof (IH_sstrg' H_valid_sstrg' H_valid_skey H_smv) as IH_sstrg'_0.
               apply IH_sstrg'_0.
           +++ rewrite <- H_smv.
               simpl.
               auto.

    (* correcrt *)
    - unfold sload_solver_correct_res.
      intros ctx  m sstrg skey smv ops idx1 m1.
      intros H_valid_smap H_valid_sstrg H_valid_skey H_basic_sload_solver H_add_to_smap.
      induction sstrg as [| u sstrg' IH_sstrg'].
      + simpl in H_basic_sload_solver.
        rewrite <- H_basic_sload_solver in H_add_to_smap.
        exists idx1. exists m1.
        split; try auto.
        intros model mem strg exts H_is_model.
        pose proof (symsload_valid_smv (get_maxidx_smap m) skey [] ops H_valid_skey H_valid_sstrg) as H_valid_smv.
        pose proof (add_to_smap_valid_smap idx1 m m1 (SymSLOAD skey []) ops H_valid_smap H_valid_smv H_add_to_smap) as H_valid_m1.
        assert (H_add_to_smap' := H_add_to_smap).
        symmetry in H_add_to_smap'.
        pose proof (add_to_smap_key_lt_maxidx m m1 idx1 (SymSLOAD skey []) H_add_to_smap') as H_idx1_lt_maxidx_m1.
        pose proof (valid_sstack_val_freshvar (get_maxidx_smap m1) idx1 H_idx1_lt_maxidx_m1) as H_valid_fresh_idx1.
        unfold valid_smap in H_valid_m1.
        pose proof (eval_sstack_val_succ (get_bindings_smap m1) (FreshVar idx1) model mem strg exts (get_maxidx_smap m1) ops H_valid_fresh_idx1 H_valid_m1) as H_eval_sstack_val.
        destruct H_eval_sstack_val as [v H_eval_sstack_val].
        exists v.
        rewrite H_eval_sstack_val.
        split; reflexivity.
      + unfold basic_sload_solver in H_basic_sload_solver.
        destruct u.
        simpl in H_valid_sstrg.
        destruct H_valid_sstrg as [[H_valid_key H_valid_value] H_valid_sstrg'].
        destruct (sstack_val_cmp (S (get_maxidx_smap m)) ctx skey key (get_maxidx_smap m) (get_bindings_smap m) (get_maxidx_smap m) (get_bindings_smap m) ops) eqn:E_cmp_skey_key.
        
        * destruct m as [maxidx_m bs_m] eqn:E_m.
          exists maxidx_m.
          exists (SymMap (S maxidx_m) ((maxidx_m,(SymSLOAD skey (U_SSTORE sstack_val key value :: sstrg')))::bs_m)).
          split.
          ++ simpl. reflexivity.
          ++ intros model mem strg exts H_is_model.
             rewrite <- H_basic_sload_solver in H_add_to_smap.
             simpl in H_add_to_smap.
             injection H_add_to_smap as H_idx1 H_m1.
             rewrite <- H_idx1.
             rewrite <- H_m1.
             simpl.
             unfold eval_sstack_val.
             rewrite eval_sstack_val'_immediate_fresh_var.
             remember (S maxidx_m) as S_maxidx_m.
             unfold eval_sstack_val' at 2.
             fold eval_sstack_val'.
             rewrite HeqS_maxidx_m.
             rewrite follow_smap_first_match; try reflexivity.  (* the reflexivity is for is_fresh_var_smv *)

             unfold symbolic_state_cmp.SymbolicStateCmp.safe_sstack_val_cmp_ext_1 in H_sstack_val_cmp_snd.
             pose proof (H_sstack_val_cmp_snd (S maxidx_m)) as H_sstack_val_cmp_snd.
             unfold symbolic_state_cmp.SymbolicStateCmp.safe_sstack_val_cmp_ext_1_d in H_sstack_val_cmp_snd.
             pose proof (H_sstack_val_cmp_snd (S maxidx_m) (Nat.le_refl (S maxidx_m) )) as H_sstack_val_cmp_snd.
             unfold symbolic_state_cmp.SymbolicStateCmp.safe_sstack_val_cmp in H_sstack_val_cmp_snd.
             pose proof (H_sstack_val_cmp_snd ctx skey key maxidx_m bs_m maxidx_m bs_m ops H_valid_skey H_valid_key H_valid_smap H_valid_smap E_cmp_skey_key model mem strg exts H_is_model) as H_sstack_val_cmp_snd.
             destruct H_sstack_val_cmp_snd as [v [H_sstack_val_cmp_snd_1 H_sstack_val_cmp_snd_2]].
             unfold eval_sstack_val in H_sstack_val_cmp_snd_1.
             unfold eval_sstack_val in H_sstack_val_cmp_snd_2.

             pose proof (valid_sstorage_update_kv maxidx_m key value H_valid_key H_valid_value) as H_valid_update.
             pose proof (valid_sstorage_when_extended_with_valid_update maxidx_m (U_SSTORE sstack_val key value) sstrg' H_valid_update H_valid_sstrg') as H_valid_u_sstrg'.
             pose proof (H_map_o_sstrg ctx (S maxidx_m) model mem strg exts maxidx_m bs_m ops (U_SSTORE sstack_val key value :: sstrg') H_valid_u_sstrg' H_valid_smap (gt_Sn_n maxidx_m) H_is_model) as H_map_o_sstrg_0.
             destruct H_map_o_sstrg_0 as [v' H_map_o_sstrg_0].
             rewrite H_map_o_sstrg_0.
             rewrite H_sstack_val_cmp_snd_1.
             destruct v'.
             
             +++ pose proof (map_option_len (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val' (S maxidx_m) sv model mem strg exts maxidx_m bs_m ops)) (U_SSTORE sstack_val key value :: sstrg') [] H_map_o_sstrg_0) as H_l_len.
                 discriminate.
             +++ pose proof (map_option_hd (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val' (S maxidx_m) sv model mem strg exts maxidx_m bs_m ops)) sstrg' v' (U_SSTORE sstack_val key value) s H_map_o_sstrg_0) as H_map_o_sstrg_1.
                 destruct H_map_o_sstrg_1 as [H_map_o_sstrg_1_0 H_map_o_sstrg_1_1].

                 unfold instantiate_storage_update in H_map_o_sstrg_1_0.
                 rewrite H_sstack_val_cmp_snd_2 in H_map_o_sstrg_1_0.
                 destruct (eval_sstack_val' (S maxidx_m) value model mem strg exts maxidx_m bs_m ops) as [value_v|] eqn:E_eval_value; try discriminate.
                 pose proof (eval_sstack_val'_preserved_when_depth_extended_le (S maxidx_m) (S (S maxidx_m)) maxidx_m bs_m value value_v model mem strg exts ops (Nat.le_succ_diag_r (S maxidx_m)) E_eval_value) as E_eval_value_0.
                 rewrite E_eval_value_0.

                 injection H_map_o_sstrg_1_0 as H_map_o_sstrg_1_0.
                 rewrite <- H_map_o_sstrg_1_0.

                 simpl.
                
                 rewrite ssload_sstore_same_address.
                 exists value_v.
                 split; reflexivity.
      * fold basic_sload_solver in H_basic_sload_solver.
        destruct (not_eq_keys ctx skey key (get_maxidx_smap m) (get_bindings_smap m) ops) eqn:E_not_eq_keys.
        ** pose proof (IH_sstrg' H_valid_sstrg' H_basic_sload_solver) as IH_sstrg'_0.
           destruct IH_sstrg'_0 as [idx2 IH_sstrg'_0].
           destruct IH_sstrg'_0 as [m2 IH_sstrg'_0].
           destruct IH_sstrg'_0 as [IH_sstrg'_0_0 IH_sstrg'_0_1].
           destruct m eqn:E_m.
           simpl in IH_sstrg'_0_0.
           injection IH_sstrg'_0_0 as IH_sstrg'_0_0_0 IH_sstrg'_0_0_1.
           simpl.
           exists maxid.
           exists (SymMap (S maxid) ((maxid, SymSLOAD skey (U_SSTORE sstack_val key value :: sstrg')) :: bindings)).
           split; try reflexivity.
           intros model mem strg exts H_is_model.
           simpl in H_add_to_smap.
           injection H_add_to_smap as H_add_to_smap_0 H_add_to_smap_1.
           rewrite <- H_add_to_smap_1.
           rewrite <- H_add_to_smap_0.
           simpl.
           rewrite <- IH_sstrg'_0_0_1 in IH_sstrg'_0_1.
           rewrite <- H_add_to_smap_1 in IH_sstrg'_0_1.
           rewrite <- IH_sstrg'_0_0_0 in IH_sstrg'_0_1.
           rewrite <- H_add_to_smap_0 in IH_sstrg'_0_1.
           simpl in IH_sstrg'_0_1.
           unfold eval_sstack_val.
           unfold eval_sstack_val in IH_sstrg'_0_1.
           remember (S maxid) as S_maxid.
           unfold eval_sstack_val' at 2.
           fold eval_sstack_val'.
           rewrite HeqS_maxid.
           rewrite follow_smap_first_match; try reflexivity.

           pose proof (valid_sstorage_update_kv maxid key value H_valid_key H_valid_value) as H_valid_update.
           pose proof (valid_sstorage_when_extended_with_valid_update maxid (U_SSTORE sstack_val key value) sstrg' H_valid_update H_valid_sstrg') as H_valid_u_sstrg'.
           pose proof (H_map_o_sstrg ctx (S maxid) model mem strg exts maxid bindings ops (U_SSTORE sstack_val key value :: sstrg') H_valid_u_sstrg' H_valid_smap (gt_Sn_n maxid) H_is_model) as H_map_o_sstrg_0.
           destruct H_map_o_sstrg_0 as [v H_map_o_sstrg_0].
           rewrite H_map_o_sstrg_0.

           pose proof (IH_sstrg'_0_1 model mem strg exts H_is_model) as IH_sstrg'_0_1_0.
           destruct IH_sstrg'_0_1_0 as [v' IH_sstrg'_0_1_0].
           destruct IH_sstrg'_0_1_0 as [IH_sstrg'_0_1_0_0 IH_sstrg'_0_1_0_1].
           exists v'.
           split.
           *** rewrite <- HeqS_maxid.
               apply IH_sstrg'_0_1_0_0.
           *** pose proof (eval_sstack_val'_succ (S maxid) skey model mem strg exts maxid bindings ops H_valid_skey H_valid_smap (gt_Sn_n maxid)) as H_eval_skey.
               destruct H_eval_skey as [skey_v H_eval_skey].
               rewrite  H_eval_skey.
           
               destruct v.
             
             +++ pose proof (map_option_len (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val' (S maxid) sv model mem strg exts maxid bindings ops)) (U_SSTORE sstack_val key value :: sstrg') [] H_map_o_sstrg_0) as H_l_len.
                 discriminate.
             +++ pose proof (map_option_hd (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val' (S maxid) sv model mem strg exts maxid bindings ops)) sstrg' v (U_SSTORE sstack_val key value) s H_map_o_sstrg_0) as H_map_o_sstrg_1.
                 destruct H_map_o_sstrg_1 as [H_map_o_sstrg_1_0 H_map_o_sstrg_1_1].

                 unfold instantiate_storage_update in H_map_o_sstrg_1_0.

                 destruct (eval_sstack_val' (S maxid) key model mem strg exts maxid bindings ops) as [key_v|] eqn:E_eval_key; try discriminate.
                 destruct (eval_sstack_val' (S maxid) value model mem strg exts maxid bindings ops) as [value_v|] eqn:E_eval_value; try discriminate.
                 injection H_map_o_sstrg_1_0 as H_map_o_sstrg_1_0.
                 rewrite <- H_map_o_sstrg_1_0.

                 simpl.
                 remember (update_storage strg v) as strg_w_v.
                 unfold sstore.
                 unfold sload.

                 pose proof (not_eq_keys_snd ctx skey key maxid bindings ops H_valid_smap H_valid_skey H_valid_key E_not_eq_keys model mem strg exts H_is_model) as H_not_eq_keys_snd.
                 destruct H_not_eq_keys_snd as [v1 [v2 [not_eq_keys_snd_0 [not_eq_keys_snd_1 not_eq_keys_snd_3]]]].
                 rewrite H_eval_skey in not_eq_keys_snd_0.
                 injection not_eq_keys_snd_0 as not_eq_keys_snd_0.
                 rewrite not_eq_keys_snd_0.
                 rewrite E_eval_key in not_eq_keys_snd_1.
                 injection not_eq_keys_snd_1 as not_eq_keys_snd_1.
                 rewrite not_eq_keys_snd_1.

                 
                 assert( H_v1_neq_v2:  (wordToN v1 =? wordToN v2)%N = false ).
                 ++++ assert( (wordToNat v1) <> (wordToNat v2)).
                      +++++ apply wordToNat_neq1.
                            apply weqb_false.
                            apply not_eq_keys_snd_3.
                   
                      +++++ rewrite wordToN_nat.
                            rewrite wordToN_nat.
                            rewrite N.eqb_neq.
                            intuition.
                 ++++ rewrite H_v1_neq_v2.
                      unfold eval_sstack_val' in IH_sstrg'_0_1_0_1.
                      fold eval_sstack_val' in IH_sstrg'_0_1_0_1.
                      rewrite HeqS_maxid in IH_sstrg'_0_1_0_1.
                      rewrite follow_smap_first_match in IH_sstrg'_0_1_0_1; try reflexivity.
                      destruct (map_option (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val' (S maxid) sv model mem strg exts maxid bindings ops)) sstrg') eqn:E_map_op_sstrg'; try discriminate.
                      rewrite H_eval_skey in IH_sstrg'_0_1_0_1.
                      injection IH_sstrg'_0_1_0_1 as IH_sstrg'_0_1_0_1.
                      injection H_map_o_sstrg_1_1 as H_map_o_sstrg_1_1.
                      rewrite H_map_o_sstrg_1_1 in IH_sstrg'_0_1_0_1.
                      rewrite <- Heqstrg_w_v in IH_sstrg'_0_1_0_1.
                      unfold sload in IH_sstrg'_0_1_0_1.
                      rewrite not_eq_keys_snd_0 in IH_sstrg'_0_1_0_1.
                      rewrite IH_sstrg'_0_1_0_1.
                      reflexivity.
        ** rewrite <- H_basic_sload_solver in H_add_to_smap.
           exists idx1.
           exists m1.
           split.
           *** apply H_add_to_smap.
           *** intros model mem strg exts H_is_model.
               destruct m.
               simpl in H_add_to_smap.
               injection H_add_to_smap as H_idx1 H_m1.
               rewrite <- H_idx1.
               rewrite <- H_m1.
               simpl.
               unfold eval_sstack_val.

               assert(H_valid_ext_bindings: valid_bindings (S maxid) ((maxid, SymSLOAD skey (U_SSTORE sstack_val key value :: sstrg')) :: bindings) ops). simpl. split; auto.
               
               pose proof (eval_sstack_val'_succ (S (S maxid)) (FreshVar maxid) model mem strg exts (S maxid) ((maxid, SymSLOAD skey (U_SSTORE sstack_val key value :: sstrg')) :: bindings) ops (Nat.lt_succ_diag_r maxid) H_valid_ext_bindings (gt_Sn_n (S maxid))) as H_eval_FV_maxid.
               destruct  H_eval_FV_maxid as [v  H_eval_FV_maxid].
               exists v.
               rewrite H_eval_FV_maxid.
               split; reflexivity.
  Qed.

  Lemma basic_sstorage_updater_remove_dups_valid:
    forall sstack_val_cmp ctx skey m ops sstrg sstrg_r,
      symbolic_state_cmp.SymbolicStateCmp.safe_sstack_val_cmp_ext_1 sstack_val_cmp ->
      valid_sstack_value (get_maxidx_smap m) skey ->
      valid_sstorage (get_maxidx_smap m) sstrg ->
      basic_sstorage_updater_remove_dups sstack_val_cmp ctx skey sstrg m ops = sstrg_r ->
      valid_sstorage (get_maxidx_smap m) sstrg_r.
  Proof.
    intros sstack_val_cmp ctx skey m ops.
    induction sstrg as [| u sstrg' IHsstrg'].
    + intros sstrg_r H_sstack_val_cmp_snd H_valid_skey H_valid_sstrg H_basic_sstorage_updater_remove_dups.
      simpl in H_basic_sstorage_updater_remove_dups.
      rewrite <- H_basic_sstorage_updater_remove_dups.
      reflexivity.
    + intros sstrg_r H_sstack_val_cmp_snd H_valid_skey H_valid_sstrg H_basic_sstorage_updater_remove_dups.
      unfold basic_sstorage_updater_remove_dups in H_basic_sstorage_updater_remove_dups.
      fold basic_sstorage_updater_remove_dups in H_basic_sstorage_updater_remove_dups.
      destruct u as [skey' svalue] eqn:E_u.
      destruct (sstack_val_cmp (S (get_maxidx_smap m)) ctx skey skey' (get_maxidx_smap m) (get_bindings_smap m) (get_maxidx_smap m) (get_bindings_smap m) ops) eqn:E_cmp_skey_skey'.
      ++ apply IHsstrg'.
         +++ apply H_sstack_val_cmp_snd.
         +++ apply H_valid_skey.
         +++ apply H_valid_sstrg.
         +++ apply H_basic_sstorage_updater_remove_dups.
      ++  destruct sstrg_r as [|u_r sstrg_r']; try discriminate.
          injection H_basic_sstorage_updater_remove_dups as H_u_r H_sstrg_r'.
          simpl.
          split.
          +++ rewrite <- H_u_r.
              simpl.
              split; apply H_valid_sstrg.
          +++ apply IHsstrg'.
              ++++ apply H_sstack_val_cmp_snd.
              ++++ apply H_valid_skey.
              ++++ apply H_valid_sstrg.
              ++++ apply H_sstrg_r'.
  Qed.

    Lemma basic_sstorage_updater_valid: 
    forall (sstack_val_cmp : symbolic_state_cmp.SymbolicStateCmp.sstack_val_cmp_ext_1_t),
      symbolic_state_cmp.SymbolicStateCmp.safe_sstack_val_cmp_ext_1 sstack_val_cmp ->
      sstorage_updater_valid_res (basic_sstorage_updater sstack_val_cmp).
  Proof.
    intros sstack_val_cmp H_sstack_val_cmp_snd.
    unfold sstorage_updater_valid_res.
    intros ctx m sstrg sstrg' u ops.
    intros H_valid_sstrg H_valid_u H_basic_sstrg_updater.
    unfold basic_sstorage_updater in H_basic_sstrg_updater.
    destruct u as [skey svalue] eqn:E_u.
    destruct sstrg' as [|u' sstrg'']; try discriminate.
    injection H_basic_sstrg_updater as H_u' H_sstrg''.
    rewrite <- H_u'.
    simpl.
    split; try split; try apply H_valid_u.
    
    apply basic_sstorage_updater_remove_dups_valid in H_sstrg''.
    + apply H_sstrg''.
    + apply H_sstack_val_cmp_snd.
    + apply H_valid_u.
    + apply H_valid_sstrg.
   Qed. 

        
  Lemma basic_sstorage_updater_remove_dups_correct_eq_key:
    forall sstack_val_cmp ctx skey svalue model mem strg exts m ops sstrg sstrg_r strg1 strg2 v,
      symbolic_state_cmp.SymbolicStateCmp.safe_sstack_val_cmp_ext_1 sstack_val_cmp ->
      is_model (ctx_cs ctx) model = true ->
      valid_sstack_value (get_maxidx_smap m) skey ->
      valid_sstack_value (get_maxidx_smap m) svalue ->
      valid_smap (get_maxidx_smap m) (get_bindings_smap m) ops ->
      valid_sstorage (get_maxidx_smap m) sstrg ->
      basic_sstorage_updater_remove_dups sstack_val_cmp ctx skey sstrg m ops = sstrg_r ->
      eval_sstorage ((U_SSTORE sstack_val skey svalue)::sstrg) (get_maxidx_smap m) (get_bindings_smap m) model mem strg exts ops = Some strg1 ->
      eval_sstorage ((U_SSTORE sstack_val skey svalue)::sstrg_r) (get_maxidx_smap m) (get_bindings_smap m) model mem strg exts ops = Some strg2 ->        
      eval_sstack_val' (S (get_maxidx_smap m)) skey model mem strg exts (get_maxidx_smap m)  (get_bindings_smap m) ops = Some v ->
      strg1 (wordToN v) = strg2 (wordToN v).
  Proof.
    intros sstack_val_cmp ctx skey svalue model mem strg exts m ops.
    destruct sstrg as [|u' sstrg'].
    + intros sstrg_r strg1 strg2 v. 
      intros H_sstack_val_cmp_snd H_is_model H_valid_skey H_valid_svalue H_valid_smap H_valid_sstrg H_sstrg_r H_strg1 H_strg2 H_eval_skey.
      simpl in H_sstrg_r.
      rewrite <- H_sstrg_r in H_strg2.
      rewrite H_strg1 in H_strg2.
      injection H_strg2 as H_eq_strg1_strg2.
      rewrite H_eq_strg1_strg2.
      reflexivity.
    + intros sstrg_r strg1 strg2 v.
      intros H_sstack_val_cmp_snd H_is_model H_valid_skey H_valid_svalue H_valid_smap H_valid_sstrg H_sstrg_r H_strg1 H_strg2 H_eval_skey.
      unfold eval_sstorage in H_strg1.
      destruct (map_option (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: u' :: sstrg')) as [updates1|] eqn:H_mo_1; try discriminate.

      pose proof (map_option_len (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: u' :: sstrg') updates1 H_mo_1) as H_map_option_len_1.
      simpl in H_map_option_len_1.
      destruct updates1 as [|u1 updates1']; try discriminate.

      pose proof (map_option_hd (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (u' :: sstrg') updates1' (U_SSTORE sstack_val skey svalue) u1 H_mo_1) as  H_map_option_hd_1.
      destruct H_map_option_hd_1 as [H_map_option_hd_1_0 H_map_option_hd_1_1].
      simpl in H_map_option_hd_1_0.
      unfold eval_sstack_val at 1 in H_map_option_hd_1_0.
      rewrite H_eval_skey in  H_map_option_hd_1_0.
      destruct (eval_sstack_val svalue model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops) as [svalue_v|] eqn:E_eval_svalue; try discriminate.
      
      injection H_map_option_hd_1_0 as H_u1.


      unfold eval_sstorage in H_strg2.
      destruct (map_option (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: sstrg_r)) as [updates2|] eqn:H_mo_2; try discriminate.

      pose proof (map_option_len (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: sstrg_r) updates2 H_mo_2) as H_map_option_len_2.
      simpl in H_map_option_len_2.
      destruct updates2 as [|u2 updates2']; try discriminate.

      pose proof (map_option_hd (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) sstrg_r updates2' (U_SSTORE sstack_val skey svalue) u2 H_mo_2) as  H_map_option_hd_2.
      
      destruct H_map_option_hd_2 as [H_map_option_hd_2_0 H_map_option_hd_2_1].
      simpl in H_map_option_hd_2_0.
      unfold eval_sstack_val at 1 in H_map_option_hd_2_0.
      rewrite H_eval_skey in  H_map_option_hd_2_0.
      rewrite E_eval_svalue in H_map_option_hd_2_0.
      
      injection H_map_option_hd_2_0 as H_u2.

      rewrite <- H_u1 in H_strg1.
      injection H_strg1 as H_strg1.
      rewrite <- H_u2 in H_strg2.
      injection H_strg2 as H_strg2.
      rewrite <-  H_strg1.
      rewrite <-  H_strg2.

      unfold sstore.
      rewrite N.eqb_refl.
      reflexivity.
  Qed.


  
Lemma eval_sstorage_eq_key_key':
forall sstack_val_cmp ctx model mem strg exts ops maxidx bs skey svalue skey' sstrg strg',
  symbolic_state_cmp.SymbolicStateCmp.safe_sstack_val_cmp_ext_1 sstack_val_cmp ->
  valid_sstack_value maxidx skey ->
  valid_sstack_value maxidx svalue ->
  valid_sstack_value maxidx skey' ->
  valid_bindings maxidx bs ops ->
  is_model (ctx_cs ctx) model = true ->
  sstack_val_cmp (S maxidx) ctx skey skey' maxidx bs maxidx bs ops = true ->
  eval_sstorage (U_SSTORE sstack_val skey svalue :: sstrg) maxidx bs model mem strg exts ops = Some strg' ->
  eval_sstorage (U_SSTORE sstack_val skey' svalue :: sstrg) maxidx bs model mem strg exts ops = Some strg'.
Proof.
  intros sstack_val_cmp ctx model mem strg exts ops maxidx bs skey svalue skey' sstrg strg'.
  intros H_sstack_val_cmp_snd H_valid_skey H_valid_svalue H_valid_skey' H_valid_bs H_is_model H_cmp_skey_skey' H_eval_u1_u2_sstrg.

  unfold eval_sstorage in H_eval_u1_u2_sstrg.
  destruct (map_option (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts maxidx bs ops)) (U_SSTORE sstack_val skey svalue :: sstrg)) as [updates1|] eqn:E_mo_1; try discriminate.
  
  pose proof (map_option_len (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts maxidx bs ops)) (U_SSTORE sstack_val skey svalue :: sstrg) updates1 E_mo_1) as H_map_option_len_1.
  simpl in H_map_option_len_1.
  destruct updates1 as [|u1 updates1']; try discriminate.

  pose proof (map_option_hd (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts maxidx bs ops))   sstrg  updates1' (U_SSTORE sstack_val skey svalue) u1 E_mo_1) as  H_map_option_hd_1.
  
  destruct H_map_option_hd_1 as [H_map_option_hd_1_0 H_map_option_hd_1_1].
  simpl in H_map_option_hd_1_0.
  destruct (eval_sstack_val skey model mem strg exts maxidx bs ops) as [skey_v|] eqn:E_eval_skey; try discriminate.
  destruct (eval_sstack_val svalue model mem strg exts maxidx bs ops) as [svalue_v|] eqn:E_eval_svalue; try discriminate.
  injection H_map_option_hd_1_0 as H_u1.

  unfold eval_sstack_val in E_eval_skey.
  unfold eval_sstack_val in E_eval_svalue.
  
  unfold symbolic_state_cmp.SymbolicStateCmp.safe_sstack_val_cmp_ext_1 in H_sstack_val_cmp_snd.
  
  pose proof (H_sstack_val_cmp_snd (S maxidx)) as H_sstack_val_cmp_snd.
  unfold symbolic_state_cmp.SymbolicStateCmp.safe_sstack_val_cmp_ext_1_d in H_sstack_val_cmp_snd.
  pose proof (H_sstack_val_cmp_snd (S maxidx) (Nat.le_refl (S maxidx) )) as H_sstack_val_cmp_snd.
  unfold symbolic_state_cmp.SymbolicStateCmp.safe_sstack_val_cmp in H_sstack_val_cmp_snd.
  pose proof (H_sstack_val_cmp_snd ctx skey skey' maxidx bs maxidx bs ops H_valid_skey H_valid_skey' H_valid_bs H_valid_bs H_cmp_skey_skey' model mem strg exts H_is_model) as H_sstack_val_cmp_snd.
  destruct H_sstack_val_cmp_snd as [v [H_sstack_val_cmp_snd_1 H_sstack_val_cmp_snd_2]].
  unfold eval_sstack_val in H_sstack_val_cmp_snd_1.
  unfold eval_sstack_val in H_sstack_val_cmp_snd_2.

  unfold eval_sstorage.
  
  unfold map_option.
  rewrite <- map_option_ho.

  rewrite H_map_option_hd_1_1.
  
  unfold instantiate_storage_update.
  unfold eval_sstack_val at 1.
  rewrite H_sstack_val_cmp_snd_2.
  unfold eval_sstack_val at 1.
  rewrite E_eval_svalue.

  injection H_eval_u1_u2_sstrg as H_eval_u1_u2_sstrg.
  rewrite <- H_eval_u1_u2_sstrg.
  rewrite <- H_u1.
  
  rewrite H_sstack_val_cmp_snd_1 in E_eval_skey.
  injection E_eval_skey as E_eval_skey.
  rewrite E_eval_skey.
  reflexivity.
Qed.


    
Lemma eval_sstorage_immediate_dup_key:
forall sstack_val_cmp ctx model mem strg exts ops maxidx bs skey svalue skey' svalue' sstrg strg',
  symbolic_state_cmp.SymbolicStateCmp.safe_sstack_val_cmp_ext_1 sstack_val_cmp ->
  valid_sstack_value maxidx skey ->
  valid_sstack_value maxidx svalue ->
  valid_sstack_value maxidx skey' ->
  valid_sstack_value maxidx svalue' ->
  valid_bindings maxidx bs ops ->
  is_model (ctx_cs ctx) model = true ->

  sstack_val_cmp (S maxidx) ctx skey skey' maxidx bs maxidx bs ops = true ->
  eval_sstorage (U_SSTORE sstack_val skey svalue :: U_SSTORE sstack_val skey' svalue' :: sstrg) maxidx bs model mem strg exts ops = Some strg' ->
  eval_sstorage (U_SSTORE sstack_val skey svalue :: sstrg) maxidx bs model mem strg exts ops = Some strg'.
Proof.
  intros sstack_val_cmp ctx model mem strg exts ops maxidx bs skey svalue skey' svalue' sstrg strg'.
  intros H_sstack_val_cmp_snd H_valid_skey H_valid_svalue H_valid_skey' H_valid_svalue' H_valid_bs H_is_model H_cmp_skey_skey' H_eval_u1_u2_sstrg.
  unfold eval_sstorage in H_eval_u1_u2_sstrg.
  destruct (map_option (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts maxidx bs ops)) (U_SSTORE sstack_val skey svalue :: U_SSTORE sstack_val skey' svalue' :: sstrg)) as [updates1|] eqn:E_mo_1; try discriminate.
  
  pose proof (map_option_len (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts maxidx bs ops)) (U_SSTORE sstack_val skey svalue :: U_SSTORE sstack_val skey' svalue' :: sstrg) updates1 E_mo_1) as H_map_option_len_1.
  simpl in H_map_option_len_1.
  destruct updates1 as [|u1 updates1']; try discriminate.

  pose proof (map_option_hd (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts maxidx bs ops))  (U_SSTORE sstack_val skey' svalue' :: sstrg)  updates1' (U_SSTORE sstack_val skey svalue) u1 E_mo_1) as  H_map_option_hd_1.
  
  destruct H_map_option_hd_1 as [H_map_option_hd_1_0 H_map_option_hd_1_1].
  simpl in H_map_option_hd_1_0.
  destruct (eval_sstack_val skey model mem strg exts maxidx bs ops) as [skey_v|] eqn:E_eval_skey; try discriminate.
  destruct (eval_sstack_val svalue model mem strg exts maxidx bs ops) as [svalue_v|] eqn:E_eval_svalue; try discriminate.
      
  injection H_map_option_hd_1_0 as H_u1.

  pose proof (map_option_len (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts maxidx bs ops)) (U_SSTORE sstack_val skey' svalue' :: sstrg) updates1' H_map_option_hd_1_1) as H_map_option_len_2.
  simpl in H_map_option_len_2.
  destruct updates1' as [|u1' updates1'']; try discriminate.

  pose proof (map_option_hd (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts maxidx bs ops))  sstrg  updates1'' (U_SSTORE sstack_val skey' svalue') u1' H_map_option_hd_1_1) as  H_map_option_hd_2.
  
  destruct H_map_option_hd_2 as [H_map_option_hd_2_0 H_map_option_hd_2_1].
  simpl in H_map_option_hd_2_0.
  destruct (eval_sstack_val skey' model mem strg exts maxidx bs ops) as [skey_v'|] eqn:E_eval_skey'; try discriminate.
  destruct (eval_sstack_val svalue' model mem strg exts maxidx bs ops) as [svalue_v'|] eqn:E_eval_svalue'; try discriminate.
      
  injection H_map_option_hd_2_0 as H_u1'.

  unfold symbolic_state_cmp.SymbolicStateCmp.safe_sstack_val_cmp_ext_1 in H_sstack_val_cmp_snd.
  
  pose proof (H_sstack_val_cmp_snd (S maxidx)) as H_sstack_val_cmp_snd.
  unfold symbolic_state_cmp.SymbolicStateCmp.safe_sstack_val_cmp_ext_1_d in H_sstack_val_cmp_snd.
  pose proof (H_sstack_val_cmp_snd (S maxidx) (Nat.le_refl (S maxidx) )) as H_sstack_val_cmp_snd.
  unfold symbolic_state_cmp.SymbolicStateCmp.safe_sstack_val_cmp in H_sstack_val_cmp_snd.
  pose proof (H_sstack_val_cmp_snd ctx skey skey' maxidx bs maxidx bs ops H_valid_skey H_valid_skey' H_valid_bs H_valid_bs H_cmp_skey_skey' model mem strg exts H_is_model) as H_sstack_val_cmp_snd.
  destruct H_sstack_val_cmp_snd as [v [H_sstack_val_cmp_snd_1 H_sstack_val_cmp_snd_2]].
  unfold eval_sstack_val in H_sstack_val_cmp_snd_1.
  unfold eval_sstack_val in H_sstack_val_cmp_snd_2.
  
  unfold eval_sstorage.
  
  unfold map_option.
  rewrite <- map_option_ho.

  rewrite H_map_option_hd_2_1.
  
  unfold instantiate_storage_update.
  unfold eval_sstack_val at 1.
  rewrite H_sstack_val_cmp_snd_1.
  rewrite E_eval_svalue.

  injection H_eval_u1_u2_sstrg as H_eval_u1_u2_sstrg.
  rewrite <- H_eval_u1_u2_sstrg.
  rewrite <- H_u1.
  rewrite <- H_u1'.
  unfold eval_sstack_val in E_eval_skey.
  rewrite H_sstack_val_cmp_snd_1 in E_eval_skey.
  injection E_eval_skey as E_eval_skey.
  rewrite <- E_eval_skey.
  
  unfold eval_sstack_val in E_eval_skey'.
  rewrite H_sstack_val_cmp_snd_2 in E_eval_skey'.
  injection E_eval_skey' as E_eval_skey'.
  rewrite <- E_eval_skey'.

  
  simpl.
  unfold sstore.

  assert(H: forall (g : N -> EVMWord) (v1:N) (w1 w2 : EVMWord) x,
    ( (fun key : N => if (key =? v1)%N then w1 else g key) x)
    =
      ( (fun key : N => if (key =? v1)%N then w1 else if (key =? v1)%N then w2 else g key) x)).
  + intros.
    destruct ((x =? v1)%N) eqn:E_v1; try reflexivity.
  + pose proof (functional_extensionality (fun key' : N => if (key' =? wordToN v)%N then svalue_v else update_storage strg updates1'' key') (fun key' : N => if (key' =? wordToN v)%N then svalue_v else if (key' =? wordToN v)%N then svalue_v' else update_storage strg updates1'' key') (H (update_storage strg updates1'') (wordToN v) svalue_v svalue_v')).
    rewrite H0.
  reflexivity.
Qed.

  Lemma basic_sstorage_updater_remove_dups_correct_neq_key:
    forall sstack_val_cmp ctx model mem strg exts m ops sstrg sstrg_r skey svalue strg1 strg2 v w,
      symbolic_state_cmp.SymbolicStateCmp.safe_sstack_val_cmp_ext_1 sstack_val_cmp ->
      is_model (ctx_cs ctx) model = true ->
      valid_sstack_value (get_maxidx_smap m) skey ->
      valid_sstack_value (get_maxidx_smap m) svalue ->
      valid_smap (get_maxidx_smap m) (get_bindings_smap m) ops ->
      valid_sstorage (get_maxidx_smap m) sstrg ->
      basic_sstorage_updater_remove_dups sstack_val_cmp ctx skey sstrg m ops = sstrg_r ->
      eval_sstorage ((U_SSTORE sstack_val skey svalue)::sstrg) (get_maxidx_smap m) (get_bindings_smap m) model mem strg exts ops = Some strg1 ->
      eval_sstorage ((U_SSTORE sstack_val skey svalue)::sstrg_r) (get_maxidx_smap m) (get_bindings_smap m) model mem strg exts ops = Some strg2 ->        
      eval_sstack_val' (S (get_maxidx_smap m)) skey model mem strg exts (get_maxidx_smap m)  (get_bindings_smap m) ops = Some v ->
      (w =? wordToN v)%N = false ->
      strg1 w = strg2 w.
      Proof.
    intros sstack_val_cmp ctx model mem strg exts m ops.
    induction sstrg as [|u' sstrg' IHsstrg'].
    + intros sstrg_r skey svalue strg1 strg2 v w.
      intros H_sstack_val_cmp_snd H_is_model H_valid_skey H_valid_svalue H_valid_smap H_valid_sstrg H_sstrg_r H_strg1 H_strg2 H_eval_skey H_neq_v_w.
      simpl in H_sstrg_r.
      rewrite <- H_sstrg_r in H_strg2.
      rewrite H_strg1 in H_strg2.
      injection H_strg2 as H_eq_strg1_strg2.
      rewrite H_eq_strg1_strg2.
      reflexivity.
    + intros sstrg_r skey svalue strg1 strg2 v w.
      intros H_sstack_val_cmp_snd H_is_model H_valid_skey H_valid_svalue H_valid_smap H_valid_sstrg H_sstrg_r H_strg1 H_strg2 H_eval_skey H_neq_v_w.
 
      unfold basic_sstorage_updater_remove_dups in H_sstrg_r.
      fold basic_sstorage_updater_remove_dups in H_sstrg_r.
      destruct u' as [skey' svalue'] eqn:E_u'.

      destruct (sstack_val_cmp (S (get_maxidx_smap m)) ctx skey skey' (get_maxidx_smap m) (get_bindings_smap m) (get_maxidx_smap m) (get_bindings_smap m) ops) eqn:E_cmp_skey_skey'.


         assert(H_valid_sstrg' := H_valid_sstrg).
         simpl in H_valid_sstrg'.
         destruct H_valid_sstrg' as [ [H_valid_sstrg'_0 H_valid_sstrg'_1] H_valid_sstrg'_2].
      
      ++ pose proof (eval_sstorage_immediate_dup_key sstack_val_cmp ctx model mem strg exts ops (get_maxidx_smap m) (get_bindings_smap m) skey svalue skey' svalue' sstrg' strg1 H_sstack_val_cmp_snd H_valid_skey H_valid_svalue H_valid_sstrg'_0 H_valid_sstrg'_1 H_valid_smap H_is_model E_cmp_skey_skey' H_strg1) as H_strg1_red.

       
         pose proof (IHsstrg' sstrg_r skey svalue strg1 strg2 v w H_sstack_val_cmp_snd H_is_model H_valid_skey H_valid_svalue H_valid_smap H_valid_sstrg'_2 H_sstrg_r H_strg1_red H_strg2 H_eval_skey) as IHsstrg'_0.

         assert( H_strg1_red' := H_strg1_red).

         unfold eval_sstorage in H_strg1_red.
        
         destruct (map_option (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: sstrg')) as [updates1|] eqn:H_mo_1; try discriminate.

         pose proof (map_option_len (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: sstrg') updates1 H_mo_1) as H_map_option_len_1.
         
         simpl in H_map_option_len_1.
         destruct updates1 as [|u1 updates1']; try discriminate.
    
         pose proof (map_option_hd (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) sstrg' updates1' (U_SSTORE sstack_val skey svalue) u1 H_mo_1) as  H_map_option_hd_1.
          
         destruct H_map_option_hd_1 as [H_map_option_hd_1_0 H_map_option_hd_1_1].
         simpl in H_map_option_hd_1_0.
         unfold eval_sstack_val at 1 in H_map_option_hd_1_0.

         rewrite H_eval_skey in  H_map_option_hd_1_0.

         destruct (eval_sstack_val svalue model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops) as [svalue_v|] eqn:E_eval_svalue; try discriminate.
         
         injection H_map_option_hd_1_0 as H_u1.
         injection H_strg1_red as H_strg1_red.
         
         unfold eval_sstorage in H_strg2.
         destruct (map_option (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: sstrg_r)) as [updates2|] eqn:H_mo_2; try discriminate.
         pose proof (map_option_len (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: sstrg_r) updates2 H_mo_2) as H_map_option_len_2.
         
         simpl in H_map_option_len_2.
         destruct updates2 as [|u2 updates2']; try discriminate.
    
         pose proof (map_option_hd (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) sstrg_r updates2' (U_SSTORE sstack_val skey svalue) u2 H_mo_2) as  H_map_option_hd_2.
         
         destruct H_map_option_hd_2 as [H_map_option_hd_2_0 H_map_option_hd_2_1].
         simpl in H_map_option_hd_2_0.
         unfold eval_sstack_val at 1 in H_map_option_hd_2_0.

         rewrite H_eval_skey in  H_map_option_hd_2_0.
         rewrite E_eval_svalue in  H_map_option_hd_2_0.
                  
         injection H_map_option_hd_2_0 as H_u2.
         injection H_strg2 as H_strg2.

         rewrite <- H_strg1_red.
         rewrite <- H_strg2.

         unfold update_storage'.
         rewrite <- H_u1.
         rewrite <- H_u2.

         unfold sstore.
 
         destruct (w =? wordToN v)%N eqn:E_w_v; try reflexivity.
         pose proof (IHsstrg'_0 H_neq_v_w) as IHsstrg'_1.

         
         pose proof (basic_sstorage_updater_valid sstack_val_cmp H_sstack_val_cmp_snd ctx m sstrg' sstrg_r) as H_valid_sstrg_r.
         unfold  sstorage_updater_valid_res in H_valid_sstrg_r.

         rewrite <- H_strg1_red in IHsstrg'_1.
         rewrite <- H_strg2 in IHsstrg'_1.
         unfold update_storage' in IHsstrg'_1.
         rewrite <- H_u1 in IHsstrg'_1.
         rewrite <- H_u2 in IHsstrg'_1.
         unfold sstore in IHsstrg'_1.
         rewrite E_w_v in IHsstrg'_1.
         apply IHsstrg'_1.
      ++ destruct sstrg_r as [|u1 sstrg_r'] eqn:E_sstrg_r; try discriminate.
         injection H_sstrg_r as H_sstrg_r_0 H_sstrg_r_1.
         rewrite <- H_sstrg_r_0 in H_strg2.
         
         unfold eval_sstorage in H_strg1.
         destruct (map_option (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: U_SSTORE sstack_val skey' svalue' :: sstrg')) as [updates1|] eqn:E_mo_1; try discriminate.
         
         unfold eval_sstorage in H_strg2.
         destruct (map_option (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: U_SSTORE sstack_val skey' svalue' :: sstrg_r')) as [updates2|] eqn:E_mo_2; try discriminate.
         
         pose proof (map_option_len (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: U_SSTORE sstack_val skey' svalue' :: sstrg') updates1 E_mo_1) as H_map_option_len_1.
         
         simpl in H_map_option_len_1.
         destruct updates1 as [|u1' updates1']; try discriminate.
         
         pose proof (map_option_hd (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey' svalue' :: sstrg') updates1' (U_SSTORE sstack_val skey svalue) u1' E_mo_1) as  H_map_option_hd_1.
         
         destruct H_map_option_hd_1 as [H_map_option_hd_1_0 H_map_option_hd_1_1].
         simpl in H_map_option_hd_1_0.
         unfold eval_sstack_val at 1 in H_map_option_hd_1_0.
         rewrite H_eval_skey in H_map_option_hd_1_0.
         
         destruct (eval_sstack_val svalue model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops) as [svalue_v|] eqn:E_eval_svalue; try discriminate.
         
         pose proof (map_option_len (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey' svalue' :: sstrg') updates1' H_map_option_hd_1_1) as H_map_option_len_1_1.
         simpl in H_map_option_len_1_1.
         destruct updates1' as [|u1'' updates1'']; try discriminate.
         
         pose proof (map_option_hd (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) sstrg' updates1'' (U_SSTORE sstack_val skey' svalue') u1'' H_map_option_hd_1_1) as  H_map_option_hd_1_2.
         
         destruct H_map_option_hd_1_2 as [H_map_option_hd_1_2_0 H_map_option_hd_1_2_1].
         simpl in H_map_option_hd_1_2_0.
         unfold eval_sstack_val at 1 in H_map_option_hd_1_2_0.
         
         destruct (eval_sstack_val' (S (get_maxidx_smap m)) skey' model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops) as [skey'_v|] eqn:E_eval_skey'; try discriminate.
         destruct (eval_sstack_val svalue' model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops) as [svalue'_v|] eqn:E_eval_svalue'; try discriminate.
         injection H_map_option_hd_1_2_0 as H_map_option_hd_1_2_0.
         
         pose proof (map_option_len (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: U_SSTORE sstack_val skey' svalue' :: sstrg_r') updates2 E_mo_2) as H_map_option_len_2.
         
         simpl in H_map_option_len_2.
         destruct updates2 as [|u2' updates2']; try discriminate.
         
         pose proof (map_option_hd (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey' svalue' :: sstrg_r') updates2' (U_SSTORE sstack_val skey svalue) u2' E_mo_2) as  H_map_option_hd_2.
         
         destruct H_map_option_hd_2 as [H_map_option_hd_2_0 H_map_option_hd_2_1].
         simpl in H_map_option_hd_2_0.
         unfold eval_sstack_val at 1 in H_map_option_hd_2_0.
         rewrite H_eval_skey in H_map_option_hd_2_0.
         rewrite E_eval_svalue in H_map_option_hd_2_0.
         
         pose proof (map_option_len (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey' svalue' :: sstrg_r') updates2' H_map_option_hd_2_1) as H_map_option_len_2_1.
         simpl in H_map_option_len_2_1.
         destruct updates2' as [|u2'' updates2'']; try discriminate.
         
         pose proof (map_option_hd (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) sstrg_r' updates2'' (U_SSTORE sstack_val skey' svalue') u2'' H_map_option_hd_2_1) as  H_map_option_hd_2_2.
           
         destruct H_map_option_hd_2_2 as [H_map_option_hd_2_2_0 H_map_option_hd_2_2_1].
         simpl in H_map_option_hd_2_2_0.
         unfold eval_sstack_val at 1 in H_map_option_hd_2_2_0.
         rewrite E_eval_skey' in H_map_option_hd_2_2_0.
         rewrite E_eval_svalue' in H_map_option_hd_2_2_0.
         
         injection H_map_option_hd_2_2_0 as H_map_option_hd_2_2_0.
         
         injection H_strg1 as H_strg1.
         injection H_strg2 as H_strg2.
         rewrite <- H_strg1.
         rewrite <- H_strg2.
         
         injection H_map_option_hd_1_0 as H_map_option_hd_1_0.
         injection H_map_option_hd_2_0 as H_map_option_hd_2_0.
         
         rewrite <- H_map_option_hd_1_0.
         rewrite <- H_map_option_hd_2_0.
         
         rewrite <- H_map_option_hd_2_2_0.
         rewrite <- H_map_option_hd_1_2_0.
         simpl.
         
         unfold sstore.
         
         rewrite H_neq_v_w.
         
         destruct ((w =? wordToN skey'_v)%N) eqn:E_e_skey'_v; try reflexivity.
         
         
         simpl in H_valid_sstrg.
         destruct H_valid_sstrg as [ [H_valid_sstrg_0 H_valid_sstrg_1] H_valid_sstrg_2].
         
         pose proof (valid_sstorage_when_extended_with_valid_update (get_maxidx_smap m) (U_SSTORE sstack_val skey svalue) sstrg'  (valid_sstorage_update_kv (get_maxidx_smap m) skey svalue H_valid_skey H_valid_svalue) H_valid_sstrg_2) as H_valid_u'_sstrg'.
         
         pose proof (eval_sstorage_succ (get_maxidx_smap m) (get_bindings_smap m) model mem strg exts ops (U_SSTORE sstack_val skey svalue :: sstrg') H_valid_u'_sstrg' H_valid_smap) as H_eval_sstorage_u'_sstrg'.
         
         pose proof (basic_sstorage_updater_remove_dups_valid sstack_val_cmp ctx skey m ops sstrg' sstrg_r' H_sstack_val_cmp_snd H_valid_skey H_valid_sstrg_2 H_sstrg_r_1) as H_valid_sstrg_r'.
         
         pose proof (valid_sstorage_when_extended_with_valid_update (get_maxidx_smap m) (U_SSTORE sstack_val skey svalue) sstrg_r'  (valid_sstorage_update_kv (get_maxidx_smap m) skey svalue H_valid_skey H_valid_svalue) H_valid_sstrg_r') as H_valid_u'_sstrg_r'.
             
         pose proof (eval_sstorage_succ (get_maxidx_smap m) (get_bindings_smap m) model mem strg exts ops (U_SSTORE sstack_val skey svalue :: sstrg_r') H_valid_u'_sstrg_r' H_valid_smap) as H_eval_sstorage_u'_sstrg_r'.

         destruct H_eval_sstorage_u'_sstrg' as [strg1' H_eval_sstorage_u'_sstrg'].
         destruct H_eval_sstorage_u'_sstrg_r' as [strg2' H_eval_sstorage_u'_sstrg_r'].
         
               
         pose proof (IHsstrg' sstrg_r' skey svalue strg1' strg2' v w H_sstack_val_cmp_snd H_is_model H_valid_skey H_valid_svalue H_valid_smap H_valid_sstrg_2 H_sstrg_r_1 H_eval_sstorage_u'_sstrg' H_eval_sstorage_u'_sstrg_r' H_eval_skey H_neq_v_w) as IHsstrg'_0.

         unfold eval_sstorage in H_eval_sstorage_u'_sstrg'.
         
         destruct (map_option (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: sstrg')) as [updates_3|] eqn:E_mo_3; try discriminate.
         
         unfold eval_sstorage in H_eval_sstorage_u'_sstrg_r'.
             
         destruct (map_option (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: sstrg_r')) as [updates_4|] eqn:E_mo_4; try discriminate.
         
         injection H_eval_sstorage_u'_sstrg' as H_eval_sstorage_u'_sstrg'.
         injection H_eval_sstorage_u'_sstrg_r' as H_eval_sstorage_u'_sstrg_r'.
         
         pose proof (map_option_len (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: sstrg') updates_3 E_mo_3) as H_map_option_len_3.
         
         simpl in H_map_option_len_3.
         destruct updates_3 as [|u3 updates_3']; try discriminate.
         
         pose proof (map_option_hd (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) sstrg' updates_3' (U_SSTORE sstack_val skey svalue) u3 E_mo_3) as  H_map_option_hd_3.
         destruct H_map_option_hd_3 as [H_map_option_hd_3_0 H_map_option_hd_3_1].
         simpl in H_map_option_hd_3_0.
         unfold eval_sstack_val at 1 in H_map_option_hd_3_0.
         rewrite H_eval_skey in  H_map_option_hd_3_0.           
         rewrite E_eval_svalue in  H_map_option_hd_3_0.
         injection H_map_option_hd_3_0 as H_u3.
         
         pose proof (map_option_len (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: sstrg_r') updates_4 E_mo_4) as H_map_option_len_4.

         simpl in H_map_option_len_4.
         destruct updates_4 as [|u4 updates_4']; try discriminate.
         
         pose proof (map_option_hd (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) sstrg_r' updates_4' (U_SSTORE sstack_val skey svalue) u4 E_mo_4) as  H_map_option_hd_4.
         destruct H_map_option_hd_4 as [H_map_option_hd_4_0 H_map_option_hd_4_1].
         simpl in H_map_option_hd_4_0.
         unfold eval_sstack_val at 1 in H_map_option_hd_4_0.
         rewrite H_eval_skey in  H_map_option_hd_4_0.           
         rewrite E_eval_svalue in  H_map_option_hd_4_0.
         injection H_map_option_hd_4_0 as H_u4.
         
         rewrite H_map_option_hd_3_1 in H_map_option_hd_1_2_1.
         injection H_map_option_hd_1_2_1 as H_map_option_hd_1_2_1.
         
         rewrite H_map_option_hd_4_1 in H_map_option_hd_2_2_1.
         injection H_map_option_hd_2_2_1 as H_map_option_hd_2_2_1.
         
         rewrite <- H_map_option_hd_1_2_1.
         rewrite <- H_map_option_hd_2_2_1.
         
         rewrite <- H_eval_sstorage_u'_sstrg' in IHsstrg'_0.
         rewrite <- H_eval_sstorage_u'_sstrg_r' in IHsstrg'_0.
         
         rewrite <- H_u3 in IHsstrg'_0.
         rewrite <- H_u4 in IHsstrg'_0.
         
         unfold update_storage in IHsstrg'_0.
         fold update_storage in IHsstrg'_0.
         
         unfold update_storage' in IHsstrg'_0.
         unfold sstore in IHsstrg'_0.
         rewrite H_neq_v_w in  IHsstrg'_0.
         apply IHsstrg'_0.
      Qed.
             
           
  Lemma basic_sstorage_updater_remove_dups_correct:
    forall sstack_val_cmp ctx skey svalue model mem strg exts m ops,
      symbolic_state_cmp.SymbolicStateCmp.safe_sstack_val_cmp_ext_1 sstack_val_cmp ->
      is_model (ctx_cs ctx) model = true ->
      valid_sstack_value (get_maxidx_smap m) skey ->
      valid_sstack_value (get_maxidx_smap m) svalue ->
      valid_smap (get_maxidx_smap m) (get_bindings_smap m) ops ->
      forall sstrg sstrg',
      valid_sstorage (get_maxidx_smap m) sstrg ->
      basic_sstorage_updater_remove_dups sstack_val_cmp ctx skey sstrg m ops = sstrg' ->
      exists strg1 strg2,
        eval_sstorage (U_SSTORE sstack_val skey svalue :: sstrg) (get_maxidx_smap m) (get_bindings_smap m) model mem strg exts ops =
          Some strg1 /\
          eval_sstorage (U_SSTORE sstack_val skey svalue :: sstrg') (get_maxidx_smap m) (get_bindings_smap m) model mem strg exts ops = Some strg2 /\
          forall w, strg1 w = strg2 w.
  Proof.
    intros sstack_val_cmp ctx skey svalue model mem strg exts m ops.
    intros H_sstack_val_cmp_snd H_is_model H_valid_skey H_valid_svalue H_valid_smap.
    intros sstrg sstrg' H_valid_sstrg H_sstrg'.
    
    pose proof (valid_sstorage_when_extended_with_valid_update (get_maxidx_smap m) (U_SSTORE sstack_val skey svalue) sstrg (valid_sstorage_update_kv (get_maxidx_smap m) skey svalue H_valid_skey H_valid_svalue) H_valid_sstrg) as H_valid_u_sstrg.

    pose proof (eval_sstorage_succ (get_maxidx_smap m) (get_bindings_smap m) model mem strg exts ops (U_SSTORE sstack_val skey svalue :: sstrg) H_valid_u_sstrg H_valid_smap) as H_eval_sstorage_succ_0.
    destruct H_eval_sstorage_succ_0 as [strg1 H_strg1].

    pose proof (basic_sstorage_updater_remove_dups_valid sstack_val_cmp ctx skey m ops sstrg sstrg' H_sstack_val_cmp_snd H_valid_skey H_valid_sstrg H_sstrg') as H_valid_sstrg'.
    
    pose proof (valid_sstorage_when_extended_with_valid_update (get_maxidx_smap m) (U_SSTORE sstack_val skey svalue) sstrg' (valid_sstorage_update_kv (get_maxidx_smap m) skey svalue H_valid_skey H_valid_svalue) H_valid_sstrg') as H_valid_u_sstrg'.

    pose proof (eval_sstorage_succ (get_maxidx_smap m) (get_bindings_smap m) model mem strg exts ops (U_SSTORE sstack_val skey svalue :: sstrg') H_valid_u_sstrg' H_valid_smap) as H_eval_sstorage_succ_1.
    destruct H_eval_sstorage_succ_1 as [strg2 H_strg2].

    exists strg1.
    exists strg2.
    repeat split; try (apply H_strg1 || apply H_strg2).


    assert(H_strg1_aux := H_strg1).
    unfold eval_sstorage in H_strg1.
    destruct (map_option (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: sstrg)) as [updates1|] eqn:H_mo_1; try discriminate.

    pose proof (map_option_len (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: sstrg) updates1 H_mo_1) as H_map_option_len_1.
    simpl in H_map_option_len_1.
    destruct updates1 as [|u1 updates1']; try discriminate.
    
    pose proof (map_option_hd (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) sstrg updates1' (U_SSTORE sstack_val skey svalue) u1 H_mo_1) as  H_map_option_hd_1.
    destruct H_map_option_hd_1 as [H_map_option_hd_1_0 H_map_option_hd_1_1].
    simpl in H_map_option_hd_1_0.
    unfold eval_sstack_val at 1 in H_map_option_hd_1_0.

    pose proof (eval_sstack_val'_succ (S (get_maxidx_smap m)) skey model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops H_valid_skey H_valid_smap (gt_Sn_n (get_maxidx_smap m))) as H_eval_skey.
    destruct H_eval_skey as [v H_eval_skey].
    rewrite H_eval_skey in  H_map_option_hd_1_0.
    destruct (eval_sstack_val svalue model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops) as [svalue_v|] eqn:E_eval_svalue; try discriminate.
    injection H_map_option_hd_1_0 as H_u1.
    injection H_strg1 as H_strg1.
    
    assert(H_strg2_aux := H_strg2).
    unfold eval_sstorage in H_strg2.
    destruct (map_option (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: sstrg')) as [updates2|] eqn:H_mo_2; try discriminate.

    pose proof (map_option_len (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) (U_SSTORE sstack_val skey svalue :: sstrg') updates2 H_mo_2) as H_map_option_len_2.
    simpl in H_map_option_len_2.
    destruct updates2 as [|u2 updates2']; try discriminate.
     
    pose proof (map_option_hd (storage_update sstack_val) (storage_update EVMWord) (instantiate_storage_update (fun sv : sstack_val => eval_sstack_val sv model mem strg exts (get_maxidx_smap m) (get_bindings_smap m) ops)) sstrg' updates2' (U_SSTORE sstack_val skey svalue) u2 H_mo_2) as  H_map_option_hd_2.
    destruct H_map_option_hd_2 as [H_map_option_hd_2_0 H_map_option_hd_2_1].
    simpl in H_map_option_hd_2_0.
    unfold eval_sstack_val at 1 in H_map_option_hd_2_0.
    rewrite H_eval_skey in  H_map_option_hd_2_0.
    rewrite E_eval_svalue in  H_map_option_hd_2_0.
    injection H_map_option_hd_2_0 as H_u2.
    injection H_strg2 as H_strg2.
 
    unfold update_storage' in H_strg1.
    rewrite <- H_u1 in H_strg1.
    unfold sstore in H_strg1.

    unfold update_storage' in H_strg2.
    rewrite <- H_u2 in H_strg2.
    unfold sstore in H_strg2.
    
    intro w.


    rewrite <- H_strg1.
    rewrite <- H_strg2.

    destruct ((w =? wordToN v)%N) eqn:E_w_v; try reflexivity.

    pose proof (basic_sstorage_updater_remove_dups_correct_neq_key sstack_val_cmp ctx model mem strg exts m ops  sstrg sstrg' skey svalue strg1 strg2 v w H_sstack_val_cmp_snd H_is_model H_valid_skey H_valid_svalue H_valid_smap H_valid_sstrg H_sstrg' H_strg1_aux H_strg2_aux H_eval_skey E_w_v) as H_neq_key.
    
    rewrite <- H_strg1 in H_neq_key.
    rewrite <- H_strg2 in H_neq_key.
    rewrite E_w_v in H_neq_key.
    apply H_neq_key.
  Qed.


    
  Lemma basic_sstorage_updater_snd: sstorage_updater_ext_snd basic_sstorage_updater.
    unfold sstorage_updater_ext_snd.
    intros sstack_val_cmp H_sstack_val_cmp_snd.
    unfold sstorage_updater_snd.
    split.
    (* Validity *)
    + apply basic_sstorage_updater_valid.
      apply H_sstack_val_cmp_snd. 
    + unfold sstorage_updater_correct_res.
      intros ctx m sstrg sstrg' u ops H_valid_smap H_valid_sstrg H_valid_u H_basic_sstrg_updater.
      intros model mem strg exts H_is_model.
      unfold basic_sstorage_updater in H_basic_sstrg_updater.
      destruct u as [skey svalue] eqn:E_u.
      simpl in H_valid_u.
      destruct H_valid_u as [H_valid_skey H_valid_svalue].
      destruct sstrg' as [|u' sstrg'']; try discriminate.
      injection H_basic_sstrg_updater as H_u' H_sstrg''.
      pose proof (basic_sstorage_updater_remove_dups_correct sstack_val_cmp ctx skey svalue model mem strg exts m ops H_sstack_val_cmp_snd H_is_model H_valid_skey H_valid_svalue H_valid_smap sstrg sstrg''  H_valid_sstrg H_sstrg'') as H_basic_sstorage_updater_remove_dups_correct.
      destruct H_basic_sstorage_updater_remove_dups_correct as [strg1 [strg2 H_basic_sstorage_updater_remove_dups_correct]].
      destruct H_basic_sstorage_updater_remove_dups_correct as [H_strg1 [H_strg2 H_eq_strg1_strg2]].
      rewrite <- H_u'.
      rewrite H_strg1.
      rewrite H_strg2.
      exists strg1.
      exists strg2.
      repeat split; try reflexivity.
      unfold eq_storage.
      apply H_eq_strg1_strg2.
  Qed.
  
End StorageOpsSolversImplSoundness.

