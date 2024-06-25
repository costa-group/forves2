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

Require Import FORVES2.storage_ops_solvers.
Import StorageOpsSolvers.

Require Import FORVES2.symbolic_state_cmp.
Import SymbolicStateCmp.

Require Import FORVES2.constraints.
Import Constraints.

Require Import FORVES2.context.
Import Context.

Module StorageOpsSolversImpl.

 
(* Basic/trivial solvers *)  

(* Doesn't check the storage for the value, just returns an abstract load *)
Definition trivial_sload_solver (sstack_val_cmp: sstack_val_cmp_ext_1_t) (ctx: ctx_t) (skey: sstack_val) (sstrg: sstorage) (m: smap) (ops: stack_op_instr_map) :=
  SymSLOAD skey sstrg.


(* Doesn't check the storage, just appends the abstract store *)
Definition trivial_sstorage_updater (sstack_val_cmp: sstack_val_cmp_ext_1_t) (ctx: ctx_t) (update: storage_update sstack_val) (sstrg: sstorage) (m: smap) (ops: stack_op_instr_map) :=
  (update::sstrg).



Definition not_eq_keys (ctx: ctx_t) (skey skey': sstack_val) (maxidx: nat) (sb: sbindings) (ops: stack_op_instr_map) : bool :=
  match follow_in_smap skey maxidx sb with
  | Some (FollowSmapVal smv1 _ _) =>
      match smv1 with
      | SymBasicVal sv1 =>
          match follow_in_smap skey' maxidx sb with
          | Some (FollowSmapVal smv2 _ _) =>
              match smv2 with
              | SymBasicVal sv2 =>
                  match sv1, sv2 with
                  | Val v1, Val v2 => negb (weqb v1 v2)
                  | _, _ => chk_neq_wrt_ctx ctx sv1 sv2
                  end
              | _ => false
              end
          | _ => false
          end
      | _ => false
      end
  | _ => false
  end.

Fixpoint basic_sload_solver (sstack_val_cmp: sstack_val_cmp_ext_1_t) (ctx: ctx_t) (skey: sstack_val) (sstrg: sstorage) (m: smap) (ops: stack_op_instr_map) :=
  match sstrg with
  | [] => SymSLOAD skey []
  | (U_SSTORE _ skey' svalue)::sstrg' =>
      if sstack_val_cmp (S (get_maxidx_smap m)) ctx skey skey' (get_maxidx_smap m) (get_bindings_smap m) (get_maxidx_smap m) (get_bindings_smap m) ops then
        SymBasicVal svalue
      else
        if not_eq_keys ctx skey skey' (get_maxidx_smap m) (get_bindings_smap m) ops then
          basic_sload_solver sstack_val_cmp ctx skey sstrg' m ops
        else
          SymSLOAD skey sstrg
  end.

Fixpoint basic_sstorage_updater_remove_dups (sstack_val_cmp: sstack_val_cmp_ext_1_t) (ctx: ctx_t) (skey: sstack_val) (sstrg: sstorage) (m: smap) (ops: stack_op_instr_map) :=
  match sstrg with
  | [] => []
  | (U_SSTORE _ skey' svalue)::sstrg' =>
      if sstack_val_cmp (S (get_maxidx_smap m)) ctx skey skey' (get_maxidx_smap m) (get_bindings_smap m) (get_maxidx_smap m) (get_bindings_smap m) ops then
        basic_sstorage_updater_remove_dups sstack_val_cmp ctx skey sstrg' m ops (* we can also stop, since we will have at most one duplicate *)
      else (* if not_eq_keys skey skey' (get_maxidx_smap m) (get_bindings_smap m) instk_height ops then *)
        (U_SSTORE sstack_val skey' svalue)::(basic_sstorage_updater_remove_dups sstack_val_cmp ctx skey sstrg' m ops)
  end.
                                      
Definition basic_sstorage_updater (sstack_val_cmp: sstack_val_cmp_ext_1_t) (ctx: ctx_t) (update: storage_update sstack_val) (sstrg: sstorage) (m: smap) (ops: stack_op_instr_map) :=
  match update with
  | U_SSTORE _ skey _ =>
      update::(basic_sstorage_updater_remove_dups sstack_val_cmp ctx skey sstrg m ops)
  end.

End StorageOpsSolversImpl.
