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

Require Import FORVES2.smemory_cmp_impl.
Import SMemoryCmpImpl.

Require Import FORVES2.eval_common.
Import EvalCommon.

Require Import FORVES2.constraints.
Import Constraints.

Module SMemoryCmpImplSoundness.

  Theorem trivial_memory_cmp_snd:
    safe_smemory_cmp_ext_wrt_sstack_value_cmp trivial_memory_cmp.
  Proof.
    unfold safe_smemory_cmp_ext_wrt_sstack_value_cmp.
    unfold safe_sstack_val_cmp_ext_1_d.
    unfold safe_smemory_cmp_ext_d.
    unfold safe_smemory_cmp.
    unfold trivial_memory_cmp.
    intros.
    destruct smem1; destruct smem2; try discriminate.
    exists mem.
    auto.
  Qed.
  

  Theorem basic_memory_cmp_snd:
    safe_smemory_cmp_ext_wrt_sstack_value_cmp basic_memory_cmp.
  Proof.
  Admitted.
  
  Theorem po_memory_cmp_snd:
    safe_smemory_cmp_ext_wrt_sstack_value_cmp po_memory_cmp.
  Proof.
  Admitted.


End SMemoryCmpImplSoundness.
