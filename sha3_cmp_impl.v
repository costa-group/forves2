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

Require Import FORVES2.smemory_cmp_impl.
Import SMemoryCmpImpl.

Require Import FORVES2.constraints.
Import Constraints.

Module SHA3CmpImpl.


Definition trivial_sha3_cmp (sstack_val_cmp: sstack_val_cmp_t) (ctx: constraints) (soffset1 ssize1: sstack_val) (smem1 :smemory) (soffset2 ssize2: sstack_val) (smem2 :smemory) (maxidx1: nat) (sb1: sbindings) (maxidx2: nat) (sb2: sbindings) (ops: stack_op_instr_map) : bool :=
  false.



End SHA3CmpImpl.
