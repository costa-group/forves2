Require Import Arith.  
Require Import Nat.
Require Import Bool.
Require Import bbv.Word.
Require Import Coq.NArith.NArith.
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

Require Import FORVES2.valid_symbolic_state.
Import ValidSymbolicState.

Require Import FORVES2.symbolic_state_cmp.
Import SymbolicStateCmp.

Require Import FORVES2.constraints.
Import Constraints.

Require Import FORVES2.context.
Import Context.

Module MemoryOpsSolvers.

(* ctx sv smem m ops -> smap_value *)
Definition mload_solver_type := ctx_t -> sstack_val -> smemory -> smap -> stack_op_instr_map -> smap_value.

Definition mload_solver_ext_type := sstack_val_cmp_ext_1_t -> mload_solver_type.

Definition mload_solver_valid_res (mload_solver: mload_solver_type) :=
  forall ctx m smem soffset smv ops,
    valid_smemory (get_maxidx_smap m) smem -> (* The memory is valid *)
    valid_sstack_value (get_maxidx_smap m) soffset -> (* The offset is valid *)    
    mload_solver ctx soffset smem m ops = smv ->
    valid_smap_value (get_maxidx_smap m) ops smv.

Definition mload_solver_correct_res (mload_solver: mload_solver_type) :=
  forall ctx m smem soffset smv ops idx1 m1,
    valid_smap (get_maxidx_smap m) (get_bindings_smap m) ops -> (* The smap is valid *)
    valid_smemory (get_maxidx_smap m) smem -> (* The memory is valid *)
    valid_sstack_value (get_maxidx_smap m) soffset -> (* The offset is valid *)    
    mload_solver ctx soffset smem m ops = smv -> (* The value was resolved *)
    add_to_smap m smv = (idx1, m1) ->
    exists idx2 m2,
      add_to_smap m (SymMLOAD soffset smem) = (idx2, m2) /\
        forall model mem strg exts,
          is_model (ctx_cs ctx) model = true ->
          exists v,
            eval_sstack_val(FreshVar idx1) model mem strg exts (get_maxidx_smap m1) (get_bindings_smap m1) ops = Some v /\
              eval_sstack_val(FreshVar idx2) model mem strg exts (get_maxidx_smap m2) (get_bindings_smap m2) ops = Some v.

Definition mload_solver_snd (mload_solver: mload_solver_type) :=
  mload_solver_valid_res mload_solver /\ mload_solver_correct_res mload_solver.

Definition mload_solver_ext_snd (mload_solver: mload_solver_ext_type) :=
  forall sstack_val_cmp,
    safe_sstack_val_cmp_ext_1 sstack_val_cmp ->
    mload_solver_snd (mload_solver sstack_val_cmp).


(* ctx u smem m ops -> smem' *)
Definition smemory_updater_type := ctx_t -> memory_update sstack_val -> smemory -> smap -> stack_op_instr_map -> smemory.

Definition smemory_updater_ext_type := sstack_val_cmp_ext_1_t -> smemory_updater_type.


Definition smemory_updater_valid_res (smemory_updater: smemory_updater_type) :=
  forall ctx m smem smem' u ops,
    valid_smemory (get_maxidx_smap m) smem -> (* The memory is valid *)
    valid_smemory_update (get_maxidx_smap m) u -> (* The update is valid *)    
    smemory_updater ctx u smem m ops = smem' ->
    valid_smemory (get_maxidx_smap m) smem'. (* The new memory is valid *)

Definition smemory_updater_correct_res (smemory_updater: smemory_updater_type) :=
  forall ctx m smem smem' u ops,
    valid_smap (get_maxidx_smap m) (get_bindings_smap m) ops -> (* The smap is valid *)
    valid_smemory (get_maxidx_smap m) smem -> (* The memory is valid *)
    valid_smemory_update (get_maxidx_smap m) u -> (* The update is valid *)    
    smemory_updater ctx u smem m ops = smem' ->
    forall model mem strg exts,
      is_model (ctx_cs ctx) model = true ->
      exists mem1 mem2,
        eval_smemory (u::smem) (get_maxidx_smap m) (get_bindings_smap m) model mem strg exts ops = Some mem1 /\
          eval_smemory smem' (get_maxidx_smap m) (get_bindings_smap m) model mem strg exts ops = Some mem2 /\
          eq_memory mem1 mem2.

Definition smemory_updater_snd (smemory_updater: smemory_updater_type) :=
  smemory_updater_valid_res smemory_updater /\ smemory_updater_correct_res smemory_updater.

Definition smemory_updater_ext_snd (smemory_updater: smemory_updater_ext_type) :=
  forall sstack_val_cmp,
    safe_sstack_val_cmp_ext_1 sstack_val_cmp ->
    smemory_updater_snd (smemory_updater sstack_val_cmp).

End MemoryOpsSolvers.
