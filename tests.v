Require Import List. 
Require Import bbv.Word.

Require Import Coq.NArith.NArith.

Require Import FORVES2.constants.
Import Constants.

Require Import FORVES2.program.
Import Program.

Require Import FORVES2.block_equiv_checker.
Import BlockEquivChecker.

Require Import FORVES2.symbolic_state.
Import SymbolicState.

Require Import FORVES2.stack_operation_instructions.
Import StackOpInstrs.

Require Import FORVES2.execution_state.
Import ExecutionState.

Require Import FORVES2.concrete_interpreter.
Import ConcreteInterpreter.

Require Import FORVES2.parser.
Import Parser.

Require Import FORVES2.context.
Import Context.

Require Import FORVES2.constraints.
Import Constraints.

From Coq Require Import Strings.String.

From Coq Require Import Lists.List. Import ListNotations.


Module Tests.

(* string to block that always succeed *)
Definition str2block (s : string) : block :=
  match parse_block s with
  | None => []
  | Some b => b
  end.
    


  

Compute 
  let b1 := str2block "PUSH1 0x01 ADD" in
  let b2 := str2block "SWAP1 PUSH1 0x01 ADD" in
  let init_state := (parse_init_state "2") in
  let cs := [[C_EQ (C_VAR 0) (C_VAR 1)]] in
  match init_state with
  | Some (_,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_Basic SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

Compute 
  let b1 := str2block "PUSH1 0x01" in
  let b2 := str2block "SWAP1 PUSH1 0x01" in
  let init_state := (parse_init_state "2") in
  let cs := [[C_EQ (C_VAR 0) (C_VAR 1)]] in
  match init_state with
  | Some (_,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_Basic SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

Compute 
  let b1 := str2block "ADD" in
  let b2 := str2block "POP" in
  let init_state := (parse_init_state "2") in
  let cs := [[C_EQ (C_VAR 0) (C_VAL 0)]] in
  match init_state with
  | Some (_,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_Basic SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

Compute 
  let b1 := str2block "ADD" in
  let b2 := str2block "SWAP1 POP" in
  let init_state := (parse_init_state "2") in
  let cs := [[C_EQ (C_VAR 1) (C_VAL 0)]] in
  match init_state with
  | Some (_,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_Basic SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

End Tests.
