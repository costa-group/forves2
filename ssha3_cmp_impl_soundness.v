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

Require Import FORVES2.ssha3_cmp_impl.
Import SSHA3CmpImpl.

Require Import FORVES2.eval_common.
Import EvalCommon.

Module SSHA3CmpImplSoundness.

  Theorem trivial_sha3_cmp_snd:
    safe_sha3_cmp_ext_wrt_sstack_value_cmp trivial_sha3_cmp.
  Proof.
    unfold safe_sha3_cmp_ext_wrt_sstack_value_cmp.
    unfold safe_sha3_cmp_ext_d.
    unfold safe_sha3_cmp.
    unfold trivial_sha3_cmp.
    intros.
    discriminate.
  Qed.

End SSHA3CmpImplSoundness.
