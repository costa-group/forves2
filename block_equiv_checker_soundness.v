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

Require Import FORVES2.tools_types.
Import ToolsTypes.

From Coq Require Import Lists.List. Import ListNotations.

Module BlockEquivCheckerSoundness.

  Lemma evm_eq_block_chkr'_snd: forall
    (tools: Tools.tools_t)
    (imp_chkr: imp_checker)
    (opt_pipeline: opt_pipeline)
    (opt_step_rep: nat)
    (opt_pipeline_rep: nat),

    eq_block_chkr_snd (evm_eq_block_chkr' tools imp_chkr opt_pipeline opt_step_rep opt_pipeline_rep).
Proof.
  intros tools imp_chkr opt_pipeline opt_step_rep opt_pipeline_rep.
  destruct tools eqn:H_tools.
  rewrite <- H_tools.

  unfold eq_block_chkr_snd.
  
  intros p1 p2 cs sst H_evm_eq_block_chkr'.

  unfold evm_eq_block_chkr' in H_evm_eq_block_chkr'.

  destruct (chk_valid_sstate sst evm_stack_opm) eqn:E_valid_sst_b; try discriminate.

  pose proof (chk_valid_sstate_snd sst evm_stack_opm E_valid_sst_b) as H_valid_sst.
  
  unfold evm_eq_block_chkr'.
 
  rewrite H_tools in H_evm_eq_block_chkr'.
  unfold Tools.smemory_updater in H_evm_eq_block_chkr'.
  unfold Tools.sstorage_updater in H_evm_eq_block_chkr'.
  unfold Tools.mload_solver in H_evm_eq_block_chkr'.
  unfold Tools.sload_solver in H_evm_eq_block_chkr'.

  remember (mk_ctx imp_chkr cs) as ctx.


  destruct (evm_exec_block_s smemory_updater sstorage_updater mload_solver sload_solver p1 ctx sst evm_stack_opm) as [sst_opt|] eqn:E_sym_exec_p1; try discriminate.

  destruct (evm_exec_block_s smemory_updater sstorage_updater mload_solver sload_solver p2 ctx sst evm_stack_opm) as [sst_p|] eqn:E_sym_exec_p2; try discriminate.

  remember (S (max (get_maxidx_smap (get_smap_sst sst_opt)) (get_maxidx_smap (get_smap_sst sst_p)))) as maxid.

  rewrite <- H_tools in H_evm_eq_block_chkr'.

  remember (mk_tools_1 tools maxid) as tools_1.
    
  remember (apply_opt_n_times_pipeline_k opt_pipeline tools_1 opt_step_rep opt_pipeline_rep) as opt.

  destruct (opt ctx sst_opt) as [sst_opt' aux_bool_opt1] eqn:H_sst_opt_apply_op.
  destruct (opt ctx sst_p) as [sst_p' aux_bool_opt2] eqn:H_sst_p_apply_op.

  destruct tools_1 eqn:E_tools_1.
  simpl in H_evm_eq_block_chkr'.
  
  pose proof (sstate_cmp_snd sstack_val_cmp smemory_cmp sstorage_cmp H_sstack_val_cmp_snd H_smemory_cmp_snd H_sstorage_cmp_snd) as H_sstate_cmp_snd.

  unfold sem_eq_blocks.
  intros mem strg exts in_st model H_is_model H_in_st_is_instance_of_sst.

  assert (H_ctx_cs: (ctx_cs ctx) = cs). rewrite Heqctx. simpl. reflexivity.
  rewrite <- H_ctx_cs in H_is_model.

  (* soundness of symbolic execution of p1 *)
  pose proof (symbolic_exec_snd smemory_updater sstorage_updater mload_solver sload_solver p1 ctx sst sst_opt evm_stack_opm H_valid_sst H_smemory_updater_snd H_sstorage_updater_snd H_mload_solver_snd H_sload_solver_snd E_sym_exec_p1) as [H_sym_exc_snd_p1_1 H_sym_exc_snd_p1_2].

  (* soundness of symbolic execution of p2 *)
  pose proof (symbolic_exec_snd smemory_updater sstorage_updater mload_solver sload_solver p2 ctx sst sst_p evm_stack_opm H_valid_sst H_smemory_updater_snd H_sstorage_updater_snd H_mload_solver_snd H_sload_solver_snd E_sym_exec_p2) as [H_sym_exc_snd_p2_1  H_sym_exc_snd_p2_2].

  pose proof (H_sym_exc_snd_p1_2 mem strg exts in_st model H_is_model H_in_st_is_instance_of_sst) as H_sym_exc_snd_p1_2.
  destruct H_sym_exc_snd_p1_2 as [st'_1 [H_sym_exc_snd_p1_2_1 H_sym_exc_snd_p1_2_2]].
  
  pose proof (H_sym_exc_snd_p2_2  mem strg exts in_st model H_is_model H_in_st_is_instance_of_sst) as H_sym_exc_snd_p2_2.
  destruct H_sym_exc_snd_p2_2 as [st'_2 [H_sym_exc_snd_p2_2_1 H_sym_exc_snd_p2_2_2]].

  exists st'_1. exists st'_2.
  split; try split; try apply H_sym_exc_snd_p1_2_1; try apply H_sym_exc_snd_p2_2_1.

  (* opt that is generated by the pipeline is sound *)
  pose proof (apply_opt_n_times_pipeline_k_snd opt_pipeline tools_1 opt_step_rep opt_pipeline_rep) as H_safe_opt.

  rewrite <- E_tools_1 in Heqopt.
  rewrite <- Heqopt in H_safe_opt.

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

  remember (mk_tools sstack_value_cmp_tag memory_cmp_tag storage_cmp_tag sha3_cmp_tag mload_solver_tag sload_solver_tag memory_updater_tag storage_updater_tag) as tools.

  unfold eq_block_chkr_snd.
  intros p1 p2 cs sst H_apply_chkr.
  rewrite <- H_chkr in H_apply_chkr.
  remember (get_impl_chkr imp_chkr_tag cs) as imp_chkr.
  
  pose proof (evm_eq_block_chkr'_snd tools imp_chkr (get_pipeline optimization_steps) opt_step_rep opt_pipeline_rep) as H_evm_eq_block_chkr'_snd.
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
