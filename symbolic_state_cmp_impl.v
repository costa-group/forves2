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

Require Import FORVES2.eval_common.
Import EvalCommon.

Require Import FORVES2.constraints.
Import Constraints.

Module SymbolicStateCmpImpl.

Definition compare_sstack (sstack_val_cmp: sstack_val_cmp_t) (ctx: constraints)  (sstk1 sstk2: sstack) (maxidx1: nat) (sb1: sbindings) (maxidx2: nat) (sb2: sbindings) (ops: stack_op_instr_map) : bool :=
  fold_right_two_lists (fun e1 e2 => sstack_val_cmp ctx e1 e2 maxidx1 sb1 maxidx2 sb2 ops) sstk1 sstk2.

Definition compare_smemory (smemory_cmp: smemory_cmp_t) (ctx: constraints)  (smem1 smem2: smemory) (maxidx1: nat) (sb1: sbindings) (maxidx2: nat) (sb2: sbindings) (ops: stack_op_instr_map) : bool :=
  smemory_cmp ctx smem1 smem2 maxidx1 sb1 maxidx2 sb2 ops.

Definition compare_sstorage (sstorage_cmp: sstorage_cmp_t) (ctx: constraints) (sstrg1 sstrg2: sstorage) (maxidx1: nat) (sb1: sbindings) (maxidx2: nat) (sb2: sbindings) (ops: stack_op_instr_map) : bool :=
      sstorage_cmp ctx sstrg1 sstrg2 maxidx1 sb1 maxidx2 sb2 ops.


Definition sstate_cmp (sstack_val_cmp: sstack_val_cmp_t) (smemory_cmp: smemory_cmp_t) (sstorage_cmp: sstorage_cmp_t) (ctx: constraints) (sst1 sst2: sstate) (ops: stack_op_instr_map) : bool :=
  let sstk1 := get_stack_sst sst1 in
  let smem1 := get_memory_sst sst1 in 
  let sstrg1 := get_storage_sst sst1 in
  let m1 := get_smap_sst sst1 in
  let maxidx1 := get_maxidx_smap m1 in
  let sb1 := get_bindings_smap m1 in
  let sstk2 := get_stack_sst sst2 in
  let smem2 := get_memory_sst sst2 in 
  let sstrg2 := get_storage_sst sst2 in
  let m2 := get_smap_sst sst2 in
  let maxidx2 := get_maxidx_smap m2 in
  let sb2 := get_bindings_smap m2 in
  if compare_sstack sstack_val_cmp ctx sstk1 sstk2 maxidx1 sb1 maxidx2 sb2 ops then
    if compare_smemory smemory_cmp ctx smem1 smem2 maxidx1 sb1 maxidx2 sb2 ops then
      if compare_sstorage sstorage_cmp ctx sstrg1 sstrg2 maxidx1 sb1 maxidx2 sb2 ops then
        true
      else false
    else false
  else false.
         
End SymbolicStateCmpImpl.
