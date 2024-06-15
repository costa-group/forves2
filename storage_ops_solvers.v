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

Require Import FORVES2.valid_symbolic_state.
Import ValidSymbolicState.

Require Import FORVES2.symbolic_state_cmp.
Import SymbolicStateCmp.

Require Import FORVES2.constraints.
Import Constraints.

Require Import FORVES2.context.
Import Context.

Module StorageOpsSolvers.



(* ctx sv smem m ops -> load_res *)
Definition sload_solver_type := ctx_t -> sstack_val -> sstorage -> smap -> stack_op_instr_map -> smap_value.

Definition sload_solver_ext_type := sstack_val_cmp_ext_1_t -> sload_solver_type.

Definition sload_solver_valid_res (sload_solver: sload_solver_type) :=
  forall ctx m sstrg skey smv ops,
    valid_sstorage (get_maxidx_smap m) sstrg -> (* The storage is valid *)
    valid_sstack_value (get_maxidx_smap m) skey -> (* The key is valid *)    
    sload_solver ctx skey sstrg m ops = smv ->
    valid_smap_value (get_maxidx_smap m) ops smv.

Definition sload_solver_correct_res (sload_solver: sload_solver_type) :=
  forall ctx m sstrg skey smv ops idx1 m1,
    valid_smap (get_maxidx_smap m) (get_bindings_smap m) ops -> (* The smap is valid *)
    valid_sstorage (get_maxidx_smap m) sstrg -> (* The storage is valid *)
    valid_sstack_value (get_maxidx_smap m) skey -> (* The key is valid *)    
    sload_solver ctx skey sstrg m ops = smv -> (* The value was resolved *)
    add_to_smap m smv = (idx1, m1) ->
    exists idx2 m2,
      add_to_smap m (SymSLOAD skey sstrg) = (idx2, m2) /\
        forall model mem strg exts,
          is_model (ctx_cs ctx) model = true ->
          exists v,
            eval_sstack_val(FreshVar idx1) model mem strg exts (get_maxidx_smap m1) (get_bindings_smap m1) ops = Some v /\
              eval_sstack_val(FreshVar idx2) model mem strg exts (get_maxidx_smap m2) (get_bindings_smap m2) ops = Some v.

Definition sload_solver_snd (sload_solver: sload_solver_type) :=
  sload_solver_valid_res sload_solver /\ sload_solver_correct_res sload_solver.

Definition sload_solver_ext_snd (sload_solver: sload_solver_ext_type) :=
  forall sstack_val_cmp,
    safe_sstack_val_cmp_ext_1 sstack_val_cmp ->
    sload_solver_snd (sload_solver sstack_val_cmp).

(* ctx u sstrg m ops -> strg' *)
Definition sstorage_updater_type := ctx_t -> storage_update sstack_val -> sstorage -> smap -> stack_op_instr_map -> sstorage.
Definition sstorage_updater_ext_type := sstack_val_cmp_ext_1_t -> sstorage_updater_type.

Definition sstorage_updater_valid_res (sstorage_updater: sstorage_updater_type) :=
  forall ctx m sstrg sstrg' u ops,
    valid_sstorage (get_maxidx_smap m) sstrg -> (* The storage is valid *)
    valid_sstorage_update (get_maxidx_smap m) u -> (* The update is valid *)    
    sstorage_updater ctx u sstrg m ops = sstrg' ->
    valid_sstorage (get_maxidx_smap m) sstrg'. (* The new storage is valid *)

Definition sstorage_updater_correct_res (sstorage_updater: sstorage_updater_type) :=
  forall ctx m sstrg sstrg' u ops,
    valid_smap (get_maxidx_smap m) (get_bindings_smap m) ops -> (* The smap is valid *)
    valid_sstorage (get_maxidx_smap m) sstrg -> (* The storage is valid *)
    valid_sstorage_update (get_maxidx_smap m) u -> (* The update is valid *)    
    sstorage_updater ctx u sstrg m ops = sstrg' ->
    forall model mem strg exts,
      is_model (ctx_cs ctx) model = true ->
      exists strg1 strg2,
        eval_sstorage (u::sstrg) (get_maxidx_smap m) (get_bindings_smap m) model mem strg exts ops = Some strg1 /\
          eval_sstorage sstrg' (get_maxidx_smap m) (get_bindings_smap m) model mem strg exts ops = Some strg2 /\
          eq_storage strg1 strg2.

Definition sstorage_updater_snd (sstorage_updater: sstorage_updater_type) :=
  sstorage_updater_valid_res sstorage_updater /\ sstorage_updater_correct_res sstorage_updater.
  
Definition sstorage_updater_ext_snd (sstorage_updater: sstorage_updater_ext_type) :=
  forall sstack_val_cmp,
    safe_sstack_val_cmp_ext_1 sstack_val_cmp ->
    sstorage_updater_snd (sstorage_updater sstack_val_cmp).
  
  

End StorageOpsSolvers.
