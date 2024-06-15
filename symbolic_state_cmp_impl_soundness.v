Require Import Arith.
Require Import Nat.
Require Import Bool.
Require Import bbv.Word.
Require Import Coq.NArith.NArith.
Require Import List.
Import ListNotations.

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


Require Import FORVES2.valid_symbolic_state.
Import ValidSymbolicState.

Require Import FORVES2.valid_symbolic_state.
Import ValidSymbolicState.

Require Import FORVES2.symbolic_state_cmp.
Import SymbolicStateCmp.

Require Import FORVES2.symbolic_state_cmp_impl.
Import SymbolicStateCmpImpl.

Require Import FORVES2.eval_common.
Import EvalCommon.

Require Import FORVES2.constraints.
Import Constraints.

Require Import FORVES2.context.
Import Context.

Module SymbolicStateCmpImplSoundness.

  Lemma sstack_cmp_snd:
    forall sstack_val_cmp ctx sstk1 sstk2 maxidx1 sb1 maxidx2 sb2 ops,
      valid_sstack maxidx1 sstk1 ->
      valid_sstack maxidx2 sstk2 ->
      valid_bindings maxidx1 sb1 ops ->
      valid_bindings maxidx2 sb2 ops ->
      safe_sstack_val_cmp sstack_val_cmp ->
      fold_right_two_lists (fun e1 e2 : sstack_val => sstack_val_cmp ctx e1 e2 maxidx1 sb1 maxidx2 sb2 ops) sstk1 sstk2 = true ->
      forall model mem strg exts,
        is_model (ctx_cs ctx) model = true ->
        exists v,
          eval_sstack sstk1 maxidx1 sb1 model mem strg exts ops = Some v /\
            eval_sstack sstk2 maxidx2 sb2 model mem strg exts ops = Some v.

  Proof.
    intro sstack_val_cmp.
    induction sstk1 as [|sv1 sstk1' IHsstk1'].
    - intros.
      destruct sstk2.
      + simpl. exists []. split; reflexivity.
      + discriminate.
    - intros sstk2 maxidx1 sb1 maxidx2 sb2 ops H_valid_sstk1 H_valid_sstk2 H_valid_sb1 H_valid_sb2 H_safe_sstack_val_cmp H_fold.

      intros model mem strg exts H_is_model.

      destruct sstk2 as [|sv2 sstk2']; try discriminate.
      simpl in H_fold.
      destruct (sstack_val_cmp ctx sv1 sv2 maxidx1 sb1 maxidx2 sb2 ops) eqn:E_cmp_sv1_sv2; try discriminate.


      assert (H_safe_sstack_val_cmp' := H_safe_sstack_val_cmp).
      unfold safe_sstack_val_cmp in H_safe_sstack_val_cmp'.
      simpl in H_valid_sstk1.
      destruct H_valid_sstk1 as [H_valid_sv1 H_valid_sstk1'].
      
      simpl in H_valid_sstk2.
      destruct H_valid_sstk2 as [H_valid_sv2 H_valid_sstk2'].

      pose proof (H_safe_sstack_val_cmp' ctx sv1 sv2 maxidx1 sb1 maxidx2 sb2 ops H_valid_sv1 H_valid_sv2 H_valid_sb1 H_valid_sb2 E_cmp_sv1_sv2 model mem strg exts H_is_model) as H_safe_sstack_val_cmp'.
      destruct H_safe_sstack_val_cmp' as [v [H_eval_sv1 H_eval_sv2]].
      pose proof (IHsstk1' sstk2' maxidx1 sb1 maxidx2 sb2 ops H_valid_sstk1' H_valid_sstk2' H_valid_sb1 H_valid_sb2 H_safe_sstack_val_cmp H_fold model mem strg exts H_is_model) as IHsstk1'_0.
      destruct IHsstk1'_0 as [l [H_eval_sstk1' H_eval_sstk2']].
      simpl eval_sstack.
      rewrite H_eval_sv1.
      rewrite H_eval_sv2.
      rewrite H_eval_sstk1'.
      rewrite H_eval_sstk2'.
      exists  (v :: l).
      split; reflexivity.
  Qed.

      
    
                                                                     
  Lemma sstate_cmp_snd:
    forall sstack_val_cmp smemory_cmp sstorage_cmp,
      safe_sstack_val_cmp sstack_val_cmp ->
      safe_smemory_cmp smemory_cmp ->
      safe_sstorage_cmp sstorage_cmp ->
      symbolic_state_cmp_snd (sstate_cmp sstack_val_cmp smemory_cmp sstorage_cmp).
  Proof.
    intros sstack_val_cmp smemory_cmp sstorage_cmp H_safe_sstack_val_cmp H_safe_smemory_cmp H_safe_sstorage_cmp.
    unfold symbolic_state_cmp_snd.
    intros ctx sst1 sst2 ops H_valid_sst1 H_valid_sst2 H_sstate_cmp mem strg exts model H_is_model.

    unfold sstate_cmp in H_sstate_cmp.
    
    destruct (compare_sstack sstack_val_cmp ctx (get_stack_sst sst1) (get_stack_sst sst2) (get_maxidx_smap (get_smap_sst sst1)) (get_bindings_smap (get_smap_sst sst1)) (get_maxidx_smap (get_smap_sst sst2)) (get_bindings_smap (get_smap_sst sst2)) ops) eqn:E_sstack_cmp; try discriminate.

    destruct (compare_smemory smemory_cmp ctx (get_memory_sst sst1) (get_memory_sst sst2) (get_maxidx_smap (get_smap_sst sst1)) (get_bindings_smap (get_smap_sst sst1)) (get_maxidx_smap (get_smap_sst sst2)) (get_bindings_smap (get_smap_sst sst2)) ops) eqn:E_smemory_cmp; try discriminate.

    destruct (compare_sstorage sstorage_cmp ctx (get_storage_sst sst1) (get_storage_sst sst2) (get_maxidx_smap (get_smap_sst sst1)) (get_bindings_smap (get_smap_sst sst1)) (get_maxidx_smap (get_smap_sst sst2)) (get_bindings_smap (get_smap_sst sst2)) ops) eqn:E_sstorage_cmp; try discriminate.

    unfold valid_sstate in H_valid_sst1.
    unfold valid_smap in H_valid_sst1.
    destruct H_valid_sst1 as [H_valid_sst1_sb [H_valid_sstack_sst1 [H_valid_smemory_sst1 H_valid_sstorage_sst1]]].

    unfold valid_sstate in H_valid_sst2.
    unfold valid_smap in H_valid_sst2.
    destruct H_valid_sst2 as [H_valid_sst2_sb [H_valid_sstack_sst2 [H_valid_smemory_sst2 H_valid_sstorage_sst2]]].

    unfold eval_sstate.

    (* storage *)
    unfold compare_sstorage in E_sstorage_cmp.
    unfold safe_sstorage_cmp in H_safe_sstorage_cmp.
    pose proof (H_safe_sstorage_cmp ctx (get_storage_sst sst1) (get_storage_sst sst2) (get_maxidx_smap (get_smap_sst sst1)) (get_bindings_smap (get_smap_sst sst1)) (get_maxidx_smap (get_smap_sst sst2)) (get_bindings_smap (get_smap_sst sst2)) ops H_valid_sst1_sb H_valid_sst2_sb H_valid_sstorage_sst1 H_valid_sstorage_sst2 E_sstorage_cmp) as H_safe_sstorage_cmp.

    pose proof (H_safe_sstorage_cmp model mem strg exts H_is_model) as H_safe_sstorage_cmp.
    destruct H_safe_sstorage_cmp as [strg' [H_safe_sstorage_cmp_0 H_safe_sstorage_cmp_1]].
    rewrite H_safe_sstorage_cmp_0.
    rewrite H_safe_sstorage_cmp_1.
    
    (* memory *)
    unfold compare_smemory in E_smemory_cmp.
    unfold safe_smemory_cmp in H_safe_smemory_cmp.
    pose proof (H_safe_smemory_cmp ctx (get_memory_sst sst1) (get_memory_sst sst2) (get_maxidx_smap (get_smap_sst sst1)) (get_bindings_smap (get_smap_sst sst1)) (get_maxidx_smap (get_smap_sst sst2)) (get_bindings_smap (get_smap_sst sst2)) ops H_valid_sst1_sb H_valid_sst2_sb H_valid_smemory_sst1 H_valid_smemory_sst2 E_smemory_cmp) as H_safe_smemory_cmp.

    pose proof (H_safe_smemory_cmp model mem strg exts H_is_model) as H_safe_smemory_cmp.
    destruct H_safe_smemory_cmp as [mem' [H_safe_smemory_cmp_0 H_safe_smemory_cmp_1]].
    rewrite H_safe_smemory_cmp_0.
    rewrite H_safe_smemory_cmp_1.

    (* stack *)
    unfold compare_sstack in E_sstack_cmp.

    pose proof (sstack_cmp_snd sstack_val_cmp ctx (get_stack_sst sst1) (get_stack_sst sst2) (get_maxidx_smap (get_smap_sst sst1)) (get_bindings_smap (get_smap_sst sst1)) (get_maxidx_smap (get_smap_sst sst2)) (get_bindings_smap (get_smap_sst sst2)) ops H_valid_sstack_sst1 H_valid_sstack_sst2 H_valid_sst1_sb H_valid_sst2_sb H_safe_sstack_val_cmp E_sstack_cmp) as H_sstack_cmp_snd.
      
    pose proof (H_sstack_cmp_snd model mem strg exts H_is_model) as H_sstack_cmp_snd.
    destruct H_sstack_cmp_snd as [v [H_eval_sstk1 H_eval_sstk2]].
    rewrite H_eval_sstk1.
    rewrite H_eval_sstk2.
    
    exists (make_st v mem' strg' exts).
    split; reflexivity.
Qed.
    

End SymbolicStateCmpImplSoundness.
