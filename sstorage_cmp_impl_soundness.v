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

Require Import FORVES2.sstorage_cmp_impl.
Import SStorageCmpImpl.

Require Import FORVES2.eval_common.
Import EvalCommon.

Module StorageCmpImplSoundness.

  Theorem trivial_storage_cmp_snd:
    safe_sstorage_cmp_ext_wrt_sstack_value_cmp trivial_storage_cmp.
  Proof.
    unfold safe_sstorage_cmp_ext_wrt_sstack_value_cmp.
    unfold safe_sstack_val_cmp_ext_1_d.
    unfold safe_sstorage_cmp_ext_d.
    unfold safe_sstorage_cmp.
    unfold trivial_storage_cmp.
    intros.
    destruct sstrg1; destruct sstrg2; try discriminate.
    exists strg.
    auto.
  Qed.
  

  Theorem basic_storage_cmp_snd:
    safe_sstorage_cmp_ext_wrt_sstack_value_cmp basic_storage_cmp.
  Proof.
  Admitted.
  
  Theorem po_storage_cmp_snd:
    safe_sstorage_cmp_ext_wrt_sstack_value_cmp po_storage_cmp.
  Proof.
  Admitted.


End StorageCmpImplSoundness.
