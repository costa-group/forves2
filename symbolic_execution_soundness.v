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

Require Import FORVES2.symbolic_execution.
Import SymbolicExecution.

Require Import FORVES2.symbolic_state_eval.
Import SymbolicStateEval.
 
Require Import FORVES2.symbolic_state_eval_facts.
Import SymbolicStateEvalFacts.

Require Import FORVES2.valid_symbolic_state.
Import ValidSymbolicState.

Require Import FORVES2.concrete_interpreter.
Import ConcreteInterpreter.

Require Import FORVES2.memory_ops_solvers.
Import MemoryOpsSolvers.

Require Import FORVES2.storage_ops_solvers.
Import StorageOpsSolvers.

Require Import FORVES2.constraints.
Import Constraints.

Module SymbolicExecutionSoundness.



Definition st_is_instance_of_sst (st: state) (ctx: constraints) (sst: sstate) (ops: stack_op_instr_map) : Prop :=
  exists model mem strg exts st',
    eval_sstate sst model mem strg exts ops = Some st' /\
    eq_execution_states st st'.


(* A state transformer _tr_ and a symbolic state transformer _str_ are
equivalent, if when _str_ transforms _sst_ to _sst'_, then for any
initial state _init_st_ and a state _st_ such that _st_ is an instance
of _sst_ wrt _init_st_, _tr_ transformes from _st_ to _st'_ such that
_st'_ is an instance of _sst'_ wrt _init_st_. In addition, sst is
supposed to be valid, and sst' must be valid. *)

Definition snd_state_transformer ( tr : state -> stack_op_instr_map -> option state ) (symtr : constraints -> sstate ->  stack_op_instr_map -> option sstate )  : Prop :=
  forall (ctx: constraints) (sst sst': sstate) (ops : stack_op_instr_map),
    is_sat ctx ->
    valid_sstate sst ops ->
    symtr ctx sst ops = Some sst' ->
    valid_sstate sst' ops /\
      forall (st: state),
        st_is_instance_of_sst st ctx sst ops ->
        exists (st': state),
          tr st ops = Some st' /\ st_is_instance_of_sst st' ctx sst' ops.


End SymbolicExecutionSoundness.

