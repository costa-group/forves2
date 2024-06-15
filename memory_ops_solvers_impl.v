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

Require Import FORVES2.memory_ops_solvers.
Import MemoryOpsSolvers.

Require Import FORVES2.symbolic_state_cmp.
Import SymbolicStateCmp.

Require Import FORVES2.constraints.
Import Constraints.

Require Import FORVES2.context.
Import Context.


Module MemoryOpsSolversImpl.

(* Doesn't check the memory for the value, just returns an abstract load *)
  Definition trivial_mload_solver (sstack_val_cmp: sstack_val_cmp_ext_1_t) (ctx: ctx_t) (soffset: sstack_val) (smem: smemory) (m: smap) (ops: stack_op_instr_map) :=
    SymMLOAD soffset smem.

(* Doesn't check the memory, just appends the abstract store *)
  Definition trivial_smemory_updater (sstack_val_cmp: sstack_val_cmp_ext_1_t) (ctx: ctx_t) (update: memory_update sstack_val) (smem: smemory) (m: smap) (ops: stack_op_instr_map) :=
      (update::smem).


  
  (* [soffset,soffset+size] does not overlap with [soffset',soffset'+size'] --- closed intervals *)
  (* We will mainly use it with size=31 or size=0 *)
  Definition memory_slots_do_not_overlap  (ctx: ctx_t) (soffset soffset': sstack_val) (size size':N) (maxidx: nat) (sb: sbindings) (ops: stack_op_instr_map): bool :=
    match follow_in_smap soffset maxidx sb, follow_in_smap soffset' maxidx sb with
    | Some (FollowSmapVal (SymBasicVal (Val v1)) _ _), Some (FollowSmapVal (SymBasicVal (Val v2)) _ _) => 
        let addr := (wordToN v1) in
        let addr' := (wordToN v2) in
        orb (addr+size <? addr')%N (addr'+size' <? addr)%N
    | _, _ => false
    end.
  
 
  Fixpoint basic_mload_solver (sstack_val_cmp: sstack_val_cmp_ext_1_t) (ctx: ctx_t) (soffset: sstack_val) (smem: smemory) (m: smap) (ops: stack_op_instr_map) :=
    match smem with
    | [] => SymMLOAD soffset []
    | (U_MSTORE _ soffset' svalue)::smem' =>
        if sstack_val_cmp (S (get_maxidx_smap m)) ctx soffset soffset' (get_maxidx_smap m) (get_bindings_smap m) (get_maxidx_smap m) (get_bindings_smap m) ops then
          SymBasicVal svalue
        else
          if memory_slots_do_not_overlap ctx soffset soffset' 31 31 (get_maxidx_smap m) (get_bindings_smap m)  ops then
            basic_mload_solver sstack_val_cmp ctx soffset smem' m ops
          else
            SymMLOAD soffset smem
    | (U_MSTORE8 _ soffset' svalue)::smem' =>
        if memory_slots_do_not_overlap ctx soffset soffset' 31 0 (get_maxidx_smap m) (get_bindings_smap m) ops then
          basic_mload_solver sstack_val_cmp ctx soffset smem' m ops
        else
          SymMLOAD soffset smem             
    end.

  (* mstore8 soffset_mstore8 is includes in soffset_mstore *)
  Definition mstore8_is_included_in_mstore (sstack_val_cmp: sstack_val_cmp_ext_1_t) (ctx: ctx_t) (soffset_mstore8 soffset_mstore: sstack_val) (maxidx: nat) (sb: sbindings) (ops: stack_op_instr_map): bool :=
    match follow_in_smap soffset_mstore8 maxidx sb, follow_in_smap soffset_mstore maxidx sb with
    | Some (FollowSmapVal (SymBasicVal (Val v1)) _ _), Some (FollowSmapVal (SymBasicVal (Val v2)) _ _) => 
        let addr_mstore8 := (wordToN v1) in
        let addr_mstore := (wordToN v2) in
        andb (addr_mstore <=? addr_mstore8 )%N (addr_mstore8 <=? addr_mstore+31)%N
    | _, _ => false
    end.

  Fixpoint basic_smemory_updater_remove_mstore_dups (sstack_val_cmp: sstack_val_cmp_ext_1_t) (ctx: ctx_t) (soffset_mstore: sstack_val) (smem: smemory) (m: smap) (ops: stack_op_instr_map) :=
    match smem with
    | [] => []
    | (U_MSTORE _ soffset' svalue)::smem' =>
        if sstack_val_cmp (S (get_maxidx_smap m)) ctx soffset_mstore soffset' (get_maxidx_smap m) (get_bindings_smap m) (get_maxidx_smap m) (get_bindings_smap m) ops then
          basic_smemory_updater_remove_mstore_dups sstack_val_cmp ctx soffset_mstore smem' m ops (* we can also stop, since we will have at most one duplicate *)
        else
          (U_MSTORE sstack_val soffset' svalue)::(basic_smemory_updater_remove_mstore_dups sstack_val_cmp ctx soffset_mstore smem' m ops)
    | (U_MSTORE8 _ soffset' svalue)::smem' =>
        if mstore8_is_included_in_mstore sstack_val_cmp ctx soffset' soffset_mstore (get_maxidx_smap m) (get_bindings_smap m) ops then
          basic_smemory_updater_remove_mstore_dups sstack_val_cmp ctx soffset_mstore smem' m ops (* we can also stop, since we will have at most one duplicate *)
        else
          (U_MSTORE8 sstack_val soffset' svalue)::(basic_smemory_updater_remove_mstore_dups sstack_val_cmp ctx soffset_mstore smem' m ops)
    end.
  
  Fixpoint basic_smemory_updater_remove_mstore8_dups (sstack_val_cmp: sstack_val_cmp_ext_1_t) (ctx: ctx_t) (soffset_mstore8: sstack_val) (smem: smemory) (m: smap) (ops: stack_op_instr_map) :=
    match smem with
    | [] => []
    | (U_MSTORE8 _ soffset' svalue)::smem' =>
        if sstack_val_cmp (S (get_maxidx_smap m)) ctx soffset_mstore8 soffset' (get_maxidx_smap m) (get_bindings_smap m) (get_maxidx_smap m) (get_bindings_smap m) ops then
          basic_smemory_updater_remove_mstore8_dups sstack_val_cmp ctx soffset_mstore8 smem' m ops (* we can also stop, since we will have at most one duplicate *)
        else
          (U_MSTORE8 sstack_val soffset' svalue)::(basic_smemory_updater_remove_mstore8_dups sstack_val_cmp ctx soffset_mstore8 smem' m ops)
    | (U_MSTORE _ soffset' svalue)::smem' =>
        (U_MSTORE sstack_val soffset' svalue)::(basic_smemory_updater_remove_mstore8_dups sstack_val_cmp ctx soffset_mstore8 smem' m ops)          
    end.

  Definition basic_smemory_updater (sstack_val_cmp: sstack_val_cmp_ext_1_t) (ctx: ctx_t) (update: memory_update sstack_val) (smem: smemory) (m: smap) (ops: stack_op_instr_map) :=
    match update with
    | U_MSTORE _ soffset _ =>
        update::(basic_smemory_updater_remove_mstore_dups sstack_val_cmp ctx soffset smem m ops)
    | U_MSTORE8 _ soffset _ =>
        update::(basic_smemory_updater_remove_mstore8_dups sstack_val_cmp ctx soffset smem m ops)
    end.
  

End MemoryOpsSolversImpl.
