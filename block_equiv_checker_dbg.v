Require Import Bool.
Require Import List.
Require Import Coq.NArith.NArith.
Require Import bbv.Word.
 
Require Import FORVES2.program.
Import Program.

Require Import FORVES2.stack_operation_instructions.
Import StackOpInstrs.

Require Import FORVES2.execution_state.
Import ExecutionState.

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

Require Import FORVES2.constraints.
Import Constraints.

Require Import FORVES2.context.
Import Context.

Require Import FORVES2.tools_types.
Import ToolsTypes.

Require Import FORVES2.block_equiv_checker.
Import BlockEquivChecker.

From Coq Require Import Strings.String.

From Coq Require Import Lists.List. Import ListNotations.


Module BlockEquivCheckerDbg.


(**************************************************************)
(*** Versions of the datatypes easily readable for debugging **)

(* symbolic stack *)
Inductive sstack_val' : Type :=
| Val' (val: N)
| InVar' (var: nat)
| FreshVar' (var: nat).

Definition sstack' : Type := list sstack_val'.


(* Symbolic memory *)
Definition smemory' : Type := memory_updates sstack_val'.

(* Symbolic storage *)
Definition sstorage' : Type := storage_updates sstack_val'.


(* Symbolic map: type, constructor, getters and setters *)

Inductive smap_value' : Type :=
| SymBasicVal' (val: sstack_val')
| SymMETAPUSH' (cat val: N)
| SymOp' (label : stack_op_instr) (args : list sstack_val')
| SymMLOAD' (offset: sstack_val') (smem : smemory')
| SymSLOAD' (key: sstack_val') (sstrg : sstorage')
| SymSHA3' (offset: sstack_val') (size: sstack_val') (smem : smemory').

Definition sbinding' : Type := nat*smap_value'.
Definition sbindings' : Type := list sbinding'.
Inductive smap' := SymMap' (maxid : nat) (bindings: sbindings').

(* Symbolic state: type, constructor, getters and setters *)

Inductive sstate' :=
| SymExState' (sstk: sstack') (smem: smemory') (sstg: sstorage') (sexts : sexternals) (sm: smap').

Definition empty_sst' : sstate' :=
  SymExState' [] [] [] SymExts (SymMap' 0 []).


Definition sstack_val_to_sstack_val' (sv: sstack_val) :  sstack_val' :=
  match sv with 
  | Val v => Val' (wordToN v)
  | InVar v => InVar' v
  | FreshVar v => FreshVar' v
  end.

Definition sstack_to_sstack' (s: sstack) : sstack' :=
  map sstack_val_to_sstack_val' s.

Definition memory_update_adapt {A B: Type} (f: A -> B) (mu: memory_update A) : memory_update B :=
  match mu with 
  | U_MSTORE _ offset value => U_MSTORE B (f offset) (f value)
  | U_MSTORE8 _ offset value => U_MSTORE8 B (f offset) (f value)
  end.

Definition smemory_to_smemory' (s: smemory) : smemory' :=
    map (memory_update_adapt sstack_val_to_sstack_val') s.

Definition storage_update_adapt {A B: Type} (f: A -> B) (su: storage_update A) : storage_update B :=
  match su with
  | U_SSTORE _ k v => U_SSTORE B (f k) (f v)
  end.

Definition sstorage_to_sstorage' (s: sstorage) : sstorage' :=
  map (storage_update_adapt sstack_val_to_sstack_val') s.

Definition smap_value_to_smap_value' (smv: smap_value) : smap_value' :=
  match smv with
  | SymBasicVal val => SymBasicVal' (sstack_val_to_sstack_val' val)
  | SymMETAPUSH cat val => SymMETAPUSH' cat val
  | SymOp label args => SymOp' label (sstack_to_sstack' args)
  | SymMLOAD offset smem => SymMLOAD' (sstack_val_to_sstack_val' offset)
                                      (smemory_to_smemory' smem)
  | SymSLOAD key sstrg => SymSLOAD' (sstack_val_to_sstack_val' key) 
                                    (sstorage_to_sstorage' sstrg)
  | SymSHA3 offset size smem => SymSHA3' (sstack_val_to_sstack_val' offset)
                                         (sstack_val_to_sstack_val' size)
                                         (smemory_to_smemory' smem)
  end.

Definition sbinding_to_sbinding' (s: sbinding) : sbinding' :=
  match s with
  | (n, smv) => (n, smap_value_to_smap_value' smv)
  end.

Definition sbindings_to_sbindings' (sb: sbindings) : sbindings' :=
  map sbinding_to_sbinding' sb.

Definition smap_to_smap' (sm : smap) : smap' :=
  match sm with
  | SymMap maxid bindings => SymMap' maxid (sbindings_to_sbindings' bindings)
  end.

Definition sstate_to_sstate' (sst : sstate) : sstate' :=
  match sst with
  | SymExState sstk smem sstg sexts sm => 
      SymExState' (sstack_to_sstack' sstk) 
                  (smemory_to_smemory' smem) 
                  (sstorage_to_sstorage' sstg) 
                  sexts
                  (smap_to_smap' sm)
  end.                                      
  
(**************************************************************)

Definition evm_eq_block_chkr'_dbg
  (tools: Tools.tools_t)
  (imp_chkr: imp_checker)
  (opt_pipeline: opt_pipeline)
  (opt_step_rep: nat)
  (opt_pipeline_rep: nat)
  (***)
  (cs : constraints)
  (init_sst : sstate) 
  (opt_p p: block)
  : bool * sstate' * sstate' * string:=
  if (chk_valid_sstate init_sst evm_stack_opm) then
    let memory_updater' := Tools.smemory_updater tools in
    let storage_updater' := Tools.sstorage_updater tools in
    let mload_solver' := Tools.mload_solver tools in
    let sload_solver' := Tools.sload_solver tools in
    let ctx := mk_ctx imp_chkr cs in
    match evm_exec_block_s memory_updater' storage_updater' mload_solver' sload_solver' opt_p ctx init_sst evm_stack_opm with
    | None => (false, empty_sst', empty_sst', "Unable to execute p1"%string)
    | Some sst_opt => 
        match evm_exec_block_s memory_updater' storage_updater' mload_solver' sload_solver' p ctx init_sst evm_stack_opm with 
        | None => (false, sstate_to_sstate' sst_opt, empty_sst', "Unable to execute p2"%string)
        | Some sst_p => (* Builds optimization *)
            let maxid := S (max (get_maxidx_smap (get_smap_sst sst_opt)) (get_maxidx_smap (get_smap_sst sst_p))) in
            let tools_1 := mk_tools_1 tools maxid in
            let sstack_value_cmp := Tools_1.sstack_val_cmp tools_1 in
            let opt := apply_opt_n_times_pipeline_k opt_pipeline tools_1 opt_step_rep opt_pipeline_rep in            
            let (sst_opt', _) := opt ctx sst_opt in 
            let (sst_p',   _) := opt ctx sst_p in
            let smemory_cmp := Tools_1.smemory_cmp tools_1 in
            let sstorage_cmp := Tools_1.sstorage_cmp tools_1 in
              (sstate_cmp sstack_value_cmp smemory_cmp sstorage_cmp ctx sst_p' sst_opt' evm_stack_opm, 
               sstate_to_sstate' sst_opt',
               sstate_to_sstate' sst_p',
               "All optimizations applied"%string)

        end
    end
  else (false, empty_sst', empty_sst', "Invalid init sstate"%string).
  

Definition evm_eq_block_chkr_lazy_dbg
  (memory_updater_tag: available_smemory_updaters) 
  (storage_updater_tag: available_sstorage_updaters)
  (mload_solver_tag: available_mload_solvers) 
  (sload_solver_tag: available_sload_solvers)
  (sstack_val_cmp_tag: available_sstack_val_cmp)
  (memory_cmp_tag: available_memory_cmp)
  (storage_cmp_tag: available_storage_cmp)
  (sha3_cmp_tag: available_sha3_cmp)
  (imp_chkr_tag: available_imp_chkr)
  
  (*(opt: optim)*)
  (optimization_steps: list_opt_steps)
  (opt_step_rep: nat)
  (opt_pipeline_rep: nat) :=
    let opt_pipeline := get_pipeline optimization_steps in
    let tools := mk_tools sstack_val_cmp_tag memory_cmp_tag storage_cmp_tag sha3_cmp_tag mload_solver_tag sload_solver_tag memory_updater_tag storage_updater_tag in 
    fun (cs : constraints) (init_sst : sstate) (opt_p p: block) =>
                                         let imp_chkr := get_impl_chkr imp_chkr_tag cs in
                                         evm_eq_block_chkr'_dbg tools imp_chkr opt_pipeline opt_step_rep opt_pipeline_rep cs init_sst opt_p p.


Definition evm_eq_block_chkr_dbg
  (memory_updater_tag: available_smemory_updaters) 
  (storage_updater_tag: available_sstorage_updaters)
  (mload_solver_tag: available_mload_solvers) 
  (sload_solver_tag: available_sload_solvers)
  (sstack_val_cmp_tag: available_sstack_val_cmp)
  (memory_cmp_tag: available_memory_cmp)
  (storage_cmp_tag: available_storage_cmp)
  (sha3_cmp_tag: available_sha3_cmp)
  (imp_chkr_tag: available_imp_chkr)

  (opt_pipeline: list_opt_steps)
  (opt_step_rep: nat)
  (opt_pipeline_rep: nat)
  
  (ctx : constraints)
  (init_sst : sstate) 
  (opt_p p: block) : bool * sstate' * sstate' * string :=
  let chkr := evm_eq_block_chkr_lazy_dbg memory_updater_tag storage_updater_tag mload_solver_tag sload_solver_tag sstack_val_cmp_tag memory_cmp_tag storage_cmp_tag sha3_cmp_tag imp_chkr_tag opt_pipeline opt_step_rep opt_pipeline_rep in
  chkr ctx init_sst opt_p p.


End BlockEquivCheckerDbg.

