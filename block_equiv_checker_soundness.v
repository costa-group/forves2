Require Import Bool.
Require Import List.

Require Import FORVES2.program.
Import Program.

Require Import FORVES2.stack_operation_instructions.
Import StackOpInstrs.

Require Import FORVES2.execution_state.
Import ExecutionState.

Require Import FORVES2.execution_state_facts.
Import ExecutionStateFacts.

Require Import FORVES2.concrete_interpreter.
Import ConcreteInterpreter.

Require Import FORVES2.optimizations_def.
Import Optimizations_Def.

Require Import FORVES2.symbolic_execution.
Import SymbolicExecution.

Require Import FORVES2.storage_ops_solvers.
Import StorageOpsSolvers.

Require Import FORVES2.storage_ops_solvers_impl.
Import StorageOpsSolversImpl.

Require Import FORVES2.memory_ops_solvers.
Import MemoryOpsSolvers.

Require Import FORVES2.memory_ops_solvers_impl.
Import MemoryOpsSolversImpl.

Require Import FORVES2.symbolic_state_cmp.
Import SymbolicStateCmp.

Require Import FORVES2.valid_symbolic_state.
Import ValidSymbolicState.

Require Import FORVES2.symbolic_execution_soundness.
Import SymbolicExecutionSoundness.

Require Import FORVES2.symbolic_state_eval.
Import SymbolicStateEval.

Require Import FORVES2.symbolic_state.
Import SymbolicState.

Require Import FORVES2.symbolic_state_cmp_impl.
Import SymbolicStateCmpImpl.

Require Import FORVES2.sstack_val_cmp_impl.
Import SStackValCmpImpl.

Require Import FORVES2.sstack_val_cmp_impl_soundness.
Import SStackValCmpImplSoundness.

Require Import FORVES2.sha3_cmp_impl.
Import SHA3CmpImpl.

Require Import FORVES2.sha3_cmp_impl_soundness.
Import SHA3CmpImplSoundness.

Require Import FORVES2.storage_cmp_impl.
Import StorageCmpImpl.

Require Import FORVES2.storage_cmp_impl_soundness.
Import StorageCmpImplSoundness.


Require Import FORVES2.memory_cmp_impl.
Import MemoryCmpImpl.

Require Import FORVES2.memory_cmp_impl_soundness.
Import MemoryCmpImplSoundness.

Require Import FORVES2.storage_ops_solvers_impl.
Import StorageOpsSolversImpl.

Require Import FORVES2.storage_ops_solvers_impl_soundness.
Import StorageOpsSolversImplSoundness.

Require Import FORVES2.memory_ops_solvers_impl.
Import MemoryOpsSolversImpl.

Require Import FORVES2.memory_ops_solvers_impl_soundness.
Import MemoryOpsSolversImplSoundness.

Require Import FORVES2.symbolic_state_cmp_impl_soundness.
Import SymbolicStateCmpImplSoundness.

Require Import FORVES2.misc.
Import Misc.

Require Import FORVES2.block_equiv_checker.
Import BlockEquivChecker.


Require Import FORVES2.constraints.
Import Constraints.

Require Import FORVES2.context.
Import Context.

From Coq Require Import Lists.List. Import ListNotations.

Module BlockEquivCheckerSoundness.

Lemma evm_eq_block_chkr'_snd: forall
    (memory_updater: smemory_updater_ext_type) 
    (storage_updater: sstorage_updater_ext_type)
    (mload_solver: mload_solver_ext_type) 
    (sload_solver: sload_solver_ext_type)
    (sstack_value_cmp_ext: sstack_val_cmp_ext_2_t)
    (smemory_cmp_ext: smemory_cmp_ext_t)
    (sstorage_cmp_ext: sstorage_cmp_ext_t)
    (sha3_cmp_ext: sha3_cmp_ext_t)
    (imp_chkr: imp_checker)
    (opt_pipeline: opt_pipeline)
    (opt_step_rep: nat)
    (opt_pipeline_rep: nat),
    smemory_updater_ext_snd memory_updater ->
    sstorage_updater_ext_snd storage_updater ->
    mload_solver_ext_snd mload_solver ->
    sload_solver_ext_snd sload_solver ->
    sstack_val_cmp_fail_for_d_eq_0 sstack_value_cmp_ext ->
    safe_smemory_cmp_ext_wrt_sstack_value_cmp smemory_cmp_ext ->
    safe_sstorage_cmp_ext_wrt_sstack_value_cmp sstorage_cmp_ext ->
    safe_sha3_cmp_ext_wrt_sstack_value_cmp sha3_cmp_ext ->
    safe_sstack_value_cmp_wrt_others sstack_value_cmp_ext ->

    eq_block_chkr_snd (evm_eq_block_chkr' memory_updater storage_updater mload_solver sload_solver sstack_value_cmp_ext smemory_cmp_ext sstorage_cmp_ext sha3_cmp_ext imp_chkr opt_pipeline opt_step_rep opt_pipeline_rep).
Proof.
  intros memory_updater storage_updater mload_solver sload_solver sstack_value_cmp_ext smemory_cmp_ext sstorage_cmp_ext sha3_cmp_ext imp_chkr opt_pipeline opt_step_rep opt_pipeline_rep H_smemory_updater_ext_snd H_sstorage_updater_ext_snd H_mload_solver_ext_snd H_sload_solver_ext_snd H_sstack_val_cmp_fail_for_d_eq_0 H_safe_smemory_cmp_ext_wrt_sstack_value_cmp H_safe_sstorage_cmp_ext_wrt_sstack_value_cmp H_safe_sha3_cmp_ext_wrt_sstack_value_cmp H_safe_sstack_value_cmp_wrt_others.

  (* combining the comparators results in a sound one *)
  pose proof (safe_all_cmp smemory_cmp_ext sstorage_cmp_ext sha3_cmp_ext sstack_value_cmp_ext H_sstack_val_cmp_fail_for_d_eq_0 H_safe_smemory_cmp_ext_wrt_sstack_value_cmp H_safe_sstorage_cmp_ext_wrt_sstack_value_cmp H_safe_sha3_cmp_ext_wrt_sstack_value_cmp H_safe_sstack_value_cmp_wrt_others) as H_safe_all_cmp.

  unfold eq_block_chkr_snd.
  intros p1 p2 cs sst H_evm_eq_block_chkr'.

  unfold evm_eq_block_chkr' in H_evm_eq_block_chkr'.
 

  destruct (chk_valid_sstate sst evm_stack_opm) eqn:E_valid_sst_b; try discriminate.
  
  pose proof (chk_valid_sstate_snd sst evm_stack_opm E_valid_sst_b) as H_valid_sst.
  
  remember (sstack_value_cmp_ext smemory_cmp_ext sstorage_cmp_ext sha3_cmp_ext) as sstack_value_cmp_1.
  remember (memory_updater sstack_value_cmp_1) as memory_updater'.

  remember (storage_updater sstack_value_cmp_1) as storage_updater'.
  remember (mload_solver sstack_value_cmp_1) as mload_solver'.
  remember (sload_solver sstack_value_cmp_1) as sload_solver'.
  remember (mk_ctx imp_chkr cs) as ctx.


  destruct (evm_exec_block_s memory_updater' storage_updater' mload_solver' sload_solver' p1 ctx sst evm_stack_opm) as [sst_opt|] eqn:E_sym_exec_p1; try discriminate.

  destruct (evm_exec_block_s memory_updater' storage_updater' mload_solver' sload_solver' p2 ctx sst evm_stack_opm) as [sst_p|] eqn:E_sym_exec_p2; try discriminate.

  remember (S (max (get_maxidx_smap (get_smap_sst sst_opt)) (get_maxidx_smap (get_smap_sst sst_p)))) as maxid.
  remember (sstack_value_cmp_1 maxid) as sstack_value_cmp.
  remember (apply_opt_n_times_pipeline_k opt_pipeline sstack_value_cmp opt_step_rep opt_pipeline_rep) as opt.

  destruct (opt ctx sst_opt) as [sst_opt' aux_bool_opt1] eqn:H_sst_opt_apply_op.
  destruct (opt ctx sst_p) as [sst_p' aux_bool_opt2] eqn:H_sst_p_apply_op.

  remember (smemory_cmp_ext sstack_value_cmp) as smemory_cmp.
  remember (sstorage_cmp_ext sstack_value_cmp) as sstorage_cmp.

  pose proof (safe_ext_all_cmp smemory_cmp_ext sstorage_cmp_ext sha3_cmp_ext sstack_value_cmp_ext H_sstack_val_cmp_fail_for_d_eq_0 H_safe_smemory_cmp_ext_wrt_sstack_value_cmp H_safe_sstorage_cmp_ext_wrt_sstack_value_cmp H_safe_sha3_cmp_ext_wrt_sstack_value_cmp H_safe_sstack_value_cmp_wrt_others) as [H_sstack_value_cmp_ext [H_smemory_cmp_ext [H_sstorage_cmp_ext H_sha3_cmp_ext ]]].


  assert (H_sstack_value_cmp_ext_1: forall d, safe_sstack_val_cmp_ext_1_d sstack_value_cmp_1 d).
  (* proof of assert *)
  rewrite Heqsstack_value_cmp_1.
  intros.
  apply safe_ext_2_implies_safe_ext_1.
  apply H_sstack_value_cmp_ext.
  (* end of proof of assert *)
  
  assert (H_sstack_value_cmp_ext_1': safe_sstack_val_cmp_ext_1 sstack_value_cmp_1).
  (* proof of assert *)
  unfold safe_sstack_val_cmp_ext_1.
  apply H_sstack_value_cmp_ext_1.
  (* end of proof of assert *)

  
  assert (H_memory_updater'_snd: smemory_updater_snd memory_updater').
  (* proof of assert *)
  unfold safe_sstack_val_cmp_ext_2 in H_sstack_value_cmp_ext.
  unfold smemory_updater_ext_snd in H_smemory_updater_ext_snd.
  pose proof (H_smemory_updater_ext_snd sstack_value_cmp_1 H_sstack_value_cmp_ext_1') as H_smemory_updater_ext_snd'.
  rewrite <- Heqmemory_updater' in H_smemory_updater_ext_snd'.
  apply H_smemory_updater_ext_snd'.
  (* end of proof of assert *)


  assert (H_storage_updater'_snd: sstorage_updater_snd storage_updater').
  (* proof of assert *)
  unfold safe_sstack_val_cmp_ext_2 in H_sstack_value_cmp_ext.
  unfold sstorage_updater_ext_snd in H_sstorage_updater_ext_snd.
  pose proof (H_sstorage_updater_ext_snd sstack_value_cmp_1 H_sstack_value_cmp_ext_1') as H_sstorage_updater_ext_snd'.
  rewrite <- Heqstorage_updater' in H_sstorage_updater_ext_snd'.
  apply H_sstorage_updater_ext_snd'.
  (* end of proof of assert *)

  assert (H_mload_solver'_snd: mload_solver_snd mload_solver').
  (* proof of assert *)
  unfold safe_sstack_val_cmp_ext_2 in H_sstack_value_cmp_ext.
  unfold mload_solver_ext_snd in H_mload_solver_ext_snd.
  pose proof (H_mload_solver_ext_snd sstack_value_cmp_1 H_sstack_value_cmp_ext_1') as H_mload_solver_ext_snd'.
  rewrite <- Heqmload_solver' in H_mload_solver_ext_snd'.
  apply H_mload_solver_ext_snd'.
  (* end of proof of assert *)

  assert (H_sload_solver'_snd: sload_solver_snd sload_solver').
  (* proof of assert *)
  unfold safe_sstack_val_cmp_ext_2 in H_sstack_value_cmp_ext.
  unfold sload_solver_ext_snd in H_sload_solver_ext_snd.
  pose proof (H_sload_solver_ext_snd sstack_value_cmp_1 H_sstack_value_cmp_ext_1') as H_sload_solver_ext_snd'.
  rewrite <- Heqsload_solver' in H_sload_solver_ext_snd'.
  apply H_sload_solver_ext_snd'.
  (* end of proof of assert *)

  (* soundness of symbolic execution of p1 *)
  pose proof (symbolic_exec_snd memory_updater' storage_updater' mload_solver' sload_solver' p1 ctx sst sst_opt evm_stack_opm H_valid_sst H_memory_updater'_snd H_storage_updater'_snd H_mload_solver'_snd H_sload_solver'_snd E_sym_exec_p1) as [H_sym_exc_snd_p1_1 H_sym_exc_snd_p1_2].

  (* soundness of symbolic execution of p2 *)
  pose proof (symbolic_exec_snd memory_updater' storage_updater' mload_solver' sload_solver' p2 ctx sst sst_p evm_stack_opm H_valid_sst H_memory_updater'_snd H_storage_updater'_snd H_mload_solver'_snd H_sload_solver'_snd E_sym_exec_p2) as [H_sym_exc_snd_p2_1  H_sym_exc_snd_p2_2].

  assert (H_safe_sstack_value_cmp: safe_sstack_val_cmp sstack_value_cmp).
  (* proof of assert *)
  unfold  safe_sstack_val_cmp_ext_1 in H_sstack_value_cmp_ext_1'.
  pose proof (H_sstack_value_cmp_ext_1 maxid) as H_sstack_value_cmp_ext_1'_maxid.
  unfold safe_sstack_val_cmp_ext_1_d in H_sstack_value_cmp_ext_1'_maxid.
  pose proof (H_sstack_value_cmp_ext_1'_maxid maxid (PeanoNat.Nat.le_refl maxid)) as H_sstack_value_cmp_ext_1'_maxid.
  rewrite Heqsstack_value_cmp.
  apply H_sstack_value_cmp_ext_1'_maxid.
  (* end of proof of assert *)

  (* opt that is generated by the pipeline is sound *)
  pose proof (apply_opt_n_times_pipeline_k_snd opt_pipeline sstack_value_cmp opt_step_rep opt_pipeline_rep H_safe_sstack_value_cmp) as H_safe_opt.
  rewrite <- Heqopt in H_safe_opt.

  assert (H_safe_smemory_cmp: safe_smemory_cmp smemory_cmp).
  (* proof of assert *)
  rewrite <- Heqsstack_value_cmp_1 in H_smemory_cmp_ext.
  unfold safe_smemory_cmp_ext in H_smemory_cmp_ext.
  pose proof (H_smemory_cmp_ext maxid) as H_smemory_cmp_ext.
  unfold safe_smemory_cmp_ext_d in H_smemory_cmp_ext.
  pose proof (H_smemory_cmp_ext maxid (PeanoNat.Nat.le_refl maxid)) as H_smemory_cmp_ext_maxid.
  rewrite <- Heqsstack_value_cmp in H_smemory_cmp_ext_maxid.
  rewrite <- Heqsmemory_cmp in H_smemory_cmp_ext_maxid.
  apply H_smemory_cmp_ext_maxid.
  (* end of proof of assert *)
  
  assert (H_safe_sstorage_cmp: safe_sstorage_cmp sstorage_cmp).
  (* proof of assert *)
  rewrite <- Heqsstack_value_cmp_1 in H_sstorage_cmp_ext.
  unfold safe_sstorage_cmp_ext in H_sstorage_cmp_ext.
  pose proof (H_sstorage_cmp_ext maxid) as H_sstorage_cmp_ext.
  unfold safe_sstorage_cmp_ext_d in H_sstorage_cmp_ext.
  pose proof (H_sstorage_cmp_ext maxid (PeanoNat.Nat.le_refl maxid)) as H_sstorage_cmp_ext_maxid.
  rewrite <- Heqsstack_value_cmp in H_sstorage_cmp_ext_maxid.
  rewrite <- Heqsstorage_cmp in H_sstorage_cmp_ext_maxid.
  apply H_sstorage_cmp_ext_maxid.
  (* end of proof of assert *)
 
  pose proof (sstate_cmp_snd sstack_value_cmp smemory_cmp sstorage_cmp H_safe_sstack_value_cmp H_safe_smemory_cmp H_safe_sstorage_cmp) as H_sstate_cmp_snd.
  
  unfold sem_eq_blocks.
  intros mem strg exts in_st model H_is_model H_in_st_is_instance_of_sst.

  assert (H_ctx_cs: (ctx_cs ctx) = cs). rewrite Heqctx. simpl. reflexivity.
  rewrite <- H_ctx_cs in H_is_model.

  pose proof (H_sym_exc_snd_p1_2 mem strg exts in_st model H_is_model H_in_st_is_instance_of_sst) as H_sym_exc_snd_p1_2.
  destruct H_sym_exc_snd_p1_2 as [st'_1 [H_sym_exc_snd_p1_2_1 H_sym_exc_snd_p1_2_2]].
  
  pose proof (H_sym_exc_snd_p2_2  mem strg exts in_st model H_is_model H_in_st_is_instance_of_sst) as H_sym_exc_snd_p2_2.
  destruct H_sym_exc_snd_p2_2 as [st'_2 [H_sym_exc_snd_p2_2_1 H_sym_exc_snd_p2_2_2]].

  exists st'_1. exists st'_2.
  split; try split; try apply H_sym_exc_snd_p1_2_1; try apply H_sym_exc_snd_p2_2_1.

  unfold optim_snd in H_safe_opt.

  
  pose proof (H_safe_opt ctx sst_opt sst_opt' aux_bool_opt1 H_sym_exc_snd_p1_1 H_sst_opt_apply_op) as [H_optim_snd_1_1 H_optim_snd_1_2].
 
  pose proof (H_safe_opt ctx sst_p sst_p' aux_bool_opt2 H_sym_exc_snd_p2_1 H_sst_p_apply_op) as [H_optim_snd_2_1 H_optim_snd_2_2].
 
  unfold st_is_instance_of_sst in H_sym_exc_snd_p1_2_2.
  destruct H_sym_exc_snd_p1_2_2 as [st1' [H_sym_exc_snd_p1_2_2_0 H_sym_exc_snd_p1_2_2_1]].


  unfold eq_execution_states in H_sym_exc_snd_p1_2_2_1.

  
  unfold st_is_instance_of_sst in H_sym_exc_snd_p2_2_2.
  destruct H_sym_exc_snd_p2_2_2 as [st2' [H_sym_exc_snd_p2_2_2_0 H_sym_exc_snd_p2_2_2_1]].

  pose proof (H_optim_snd_1_2 model mem strg exts st1' H_is_model H_sym_exc_snd_p1_2_2_0 ) as H_optim_snd_1_2_0.
  pose proof (H_optim_snd_2_2 model mem strg exts st2' H_is_model H_sym_exc_snd_p2_2_2_0 ) as H_optim_snd_2_2_0.


  unfold eq_execution_states in H_sym_exc_snd_p2_2_2_1.

  unfold symbolic_state_cmp_snd in H_sstate_cmp_snd.

  pose proof (H_sstate_cmp_snd ctx sst_p' sst_opt' evm_stack_opm H_optim_snd_2_1 H_optim_snd_1_1 H_evm_eq_block_chkr' mem strg exts model H_is_model) as H_sstate_cmp_snd_1.
  
  destruct H_sstate_cmp_snd_1 as [st' [H_sstate_cmp_snd_1_0 H_sstate_cmp_snd_1_1]].
  
  rewrite H_sstate_cmp_snd_1_0 in H_optim_snd_2_2_0.
  rewrite H_sstate_cmp_snd_1_1 in H_optim_snd_1_2_0.
  rewrite  H_optim_snd_2_2_0 in H_optim_snd_1_2_0.
  injection H_optim_snd_1_2_0 as H_optim_snd_1_2_0.

  rewrite H_optim_snd_1_2_0 in H_sym_exc_snd_p2_2_2_1.
  
  destruct H_sym_exc_snd_p1_2_2_1 as [H_sym_exc_snd_p1_2_2_1_stk [H_sym_exc_snd_p1_2_2_1_mem [H_sym_exc_snd_p1_2_2_1_strg H_sym_exc_snd_p1_2_2_1_exts]]].
  
  destruct H_sym_exc_snd_p2_2_2_1 as [H_sym_exc_snd_p2_2_2_1_stk [H_sym_exc_snd_p2_2_2_1_mem [H_sym_exc_snd_p2_2_2_1_strg H_sym_exc_snd_p2_2_2_1_exts]]].

  unfold eq_execution_states.

  repeat split.
  + unfold eq_stack.
    unfold eq_stack in H_sym_exc_snd_p1_2_2_1_stk.
    unfold eq_stack in H_sym_exc_snd_p2_2_2_1_stk.
    rewrite H_sym_exc_snd_p1_2_2_1_stk.
    rewrite H_sym_exc_snd_p2_2_2_1_stk.
    reflexivity.
  + unfold eq_memory.
    unfold eq_memory in H_sym_exc_snd_p1_2_2_1_mem.
    unfold eq_memory in H_sym_exc_snd_p2_2_2_1_mem.
    intro w.
    rewrite H_sym_exc_snd_p1_2_2_1_mem.
    rewrite H_sym_exc_snd_p2_2_2_1_mem.
    reflexivity.
  + unfold eq_storage.
    unfold eq_storage in H_sym_exc_snd_p1_2_2_1_strg.
    unfold eq_storage in H_sym_exc_snd_p2_2_2_1_strg.
    intro w.
    rewrite H_sym_exc_snd_p1_2_2_1_strg.
    rewrite H_sym_exc_snd_p2_2_2_1_strg.
    reflexivity.
  + unfold eq_externals.
    unfold eq_externals in H_sym_exc_snd_p1_2_2_1_exts.
    unfold eq_externals in H_sym_exc_snd_p2_2_2_1_exts.
    rewrite H_sym_exc_snd_p1_2_2_1_exts.
    rewrite H_sym_exc_snd_p2_2_2_1_exts.
    reflexivity.
Qed.

Lemma evm_eq_block_chkr_lazy_snd:
  forall (memory_updater_tag: available_smemory_updaters) (storage_updater_tag: available_sstorage_updaters) (mload_solver_tag: available_mload_solvers) 
  (sload_solver_tag: available_sload_solvers) (sstack_value_cmp_tag: available_sstack_val_cmp) (memory_cmp_tag: available_memory_cmp)
  (storage_cmp_tag: available_storage_cmp) (sha3_cmp_tag: available_sha3_cmp) (imp_chkr_tag: available_imp_chkr) (optimization_steps: list_opt_steps) (opt_step_rep: nat) (opt_pipeline_rep: nat) (chkr: checker_type),
    evm_eq_block_chkr_lazy memory_updater_tag storage_updater_tag mload_solver_tag sload_solver_tag sstack_value_cmp_tag memory_cmp_tag storage_cmp_tag sha3_cmp_tag imp_chkr_tag optimization_steps opt_step_rep opt_pipeline_rep = chkr ->
    eq_block_chkr_snd chkr.
Proof.
  intros memory_updater_tag storage_updater_tag mload_solver_tag sload_solver_tag sstack_value_cmp_tag memory_cmp_tag storage_cmp_tag sha3_cmp_tag imp_chkr_tag optimization_steps opt_step_rep opt_pipeline_rep chkr H_chkr.

  unfold evm_eq_block_chkr_lazy in H_chkr.
  destruct (get_smemory_updater memory_updater_tag) as [smemory_updater H_smemory_updater_snd].
  destruct (get_sstorage_updater storage_updater_tag) as [sstorage_updater H_sstorage_updater_snd].
  destruct (get_mload_solver mload_solver_tag) as [mload_solver H_mload_solver_snd].
  destruct (get_sload_solver sload_solver_tag) as [sload_solver H_sload_solver_snd].
  destruct (get_sstack_val_cmp sstack_value_cmp_tag) as [sstack_value_cmp H_sstack_value_cmp_snd  H_sstack_value_cmp_snd_d0].
  destruct (get_memory_cmp memory_cmp_tag) as [smemory_cmp H_smemory_cmp_snd].
  destruct (get_storage_cmp storage_cmp_tag) as [sstorage_cmp H_sstorage_cmp_snd].
  destruct (get_sha3_cmp sha3_cmp_tag) as [ssha3_cmp H_ssha3_cmp_snd].

  unfold eq_block_chkr_snd.
  intros p1 p2 cs sst H_apply_chkr.
  rewrite <- H_chkr in H_apply_chkr.
  remember (get_impl_chkr imp_chkr_tag cs) as imp_chkr.
  
  pose proof (evm_eq_block_chkr'_snd smemory_updater sstorage_updater mload_solver sload_solver sstack_value_cmp smemory_cmp sstorage_cmp ssha3_cmp imp_chkr (get_pipeline optimization_steps) opt_step_rep opt_pipeline_rep H_smemory_updater_snd H_sstorage_updater_snd H_mload_solver_snd H_sload_solver_snd H_sstack_value_cmp_snd_d0 H_smemory_cmp_snd H_sstorage_cmp_snd H_ssha3_cmp_snd H_sstack_value_cmp_snd) as H_evm_eq_block_chkr'_snd.
  unfold eq_block_chkr_snd in H_evm_eq_block_chkr'_snd.
  apply H_evm_eq_block_chkr'_snd.
  apply H_apply_chkr.
Qed.


Lemma evm_eq_block_chkr_snd:
  forall (memory_updater_tag: available_smemory_updaters) (storage_updater_tag: available_sstorage_updaters) (mload_solver_tag: available_mload_solvers) 
  (sload_solver_tag: available_sload_solvers) (sstack_value_cmp_tag: available_sstack_val_cmp) (memory_cmp_tag: available_memory_cmp)
  (storage_cmp_tag: available_storage_cmp) (sha3_cmp_tag: available_sha3_cmp)  (imp_chkr_tag: available_imp_chkr) (optimization_steps: list_opt_steps) (opt_step_rep: nat) (opt_pipeline_rep: nat),
    eq_block_chkr_snd (evm_eq_block_chkr memory_updater_tag storage_updater_tag mload_solver_tag sload_solver_tag sstack_value_cmp_tag memory_cmp_tag storage_cmp_tag sha3_cmp_tag imp_chkr_tag optimization_steps opt_step_rep opt_pipeline_rep).
Proof.
  intros.  
  unfold eq_block_chkr_snd.
  unfold evm_eq_block_chkr.
  remember (evm_eq_block_chkr_lazy memory_updater_tag storage_updater_tag mload_solver_tag sload_solver_tag sstack_value_cmp_tag memory_cmp_tag storage_cmp_tag sha3_cmp_tag imp_chkr_tag optimization_steps opt_step_rep opt_pipeline_rep) as chkr.
  symmetry in Heqchkr.

  pose proof (evm_eq_block_chkr_lazy_snd memory_updater_tag storage_updater_tag mload_solver_tag sload_solver_tag sstack_value_cmp_tag memory_cmp_tag storage_cmp_tag sha3_cmp_tag imp_chkr_tag optimization_steps opt_step_rep opt_pipeline_rep chkr Heqchkr) as H_evm_eq_block_chkr_lazy_snd.
  apply H_evm_eq_block_chkr_lazy_snd.
  
Qed.


End BlockEquivCheckerSoundness.
