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

Compute 
  let b1 := str2block "MUL" in
  let b2 := str2block "POP" in
  let init_state := (parse_init_state "2") in
  let cs := [[C_EQ (C_VAR 0) (C_VAL 1)]] in
  match init_state with
  | Some (_,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_Basic SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

Compute 
  let b1 := str2block "MUL" in
  let b2 := str2block "POP POP PUSH1 0x0" in
  let init_state := (parse_init_state "2") in
  let cs := [[C_EQ (C_VAR 2) (C_VAL 0); C_EQ (C_VAR 2) (C_VAR 1)]] in
  match init_state with
  | Some (_,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_Basic SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.


Compute 
  let b1 := str2block "DUP2 SWAP1 DUP1 SSTORE SSTORE" in
  let b2 := str2block "SWAP1 DUP2 SWAP1 DUP1 SSTORE SSTORE" in
  let init_state := (parse_init_state "2") in
  let cs := [[C_LT (C_VAR 0) (C_VAR 2); C_LT (C_VAR 2) (C_VAR 1)];[C_LE (C_VAR_DELTA 0 1) (C_VAR 1)]] in
  match init_state with
  | Some (_,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.


(* JUMPI with constant condition 1 <> 0 *)
Eval cbv in 
  let b1 := str2block "PUSH1 0x1 PUSH1 0x10 JUMPI" in
  let b2 := str2block "PUSH1 0x10" in
  let init_state := (parse_init_state "0") in
  let cs := [] in
  match init_state with
  | Some (_,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

(* JUMPI with condition 0 < C_VAR 0 *)
Compute
  let b1 := str2block "PUSH1 0x10 JUMPI" in
  let b2 := str2block "POP PUSH1 0x10" in
  let init_state := (parse_init_state "1") in
  let cs := [[C_LT (C_VAL 0) (C_VAR 0)]] in
  match init_state with
  | Some (_,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

  
(* LT(X, Y) with ctx *)
Compute
  let b1 := str2block "LT" in
  let b2 := str2block "POP POP PUSH1 0x1" in
  let init_state := (parse_init_state "2") in
  let cs := [[C_LT (C_VAR 0) (C_VAR 1)]] in
  match init_state with
  | Some (_,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

(* LT(X, Y) with ctx. We know 10 < X and optimize the LT(5,X) *)
Compute
  let b1 := str2block "PUSH1 0x5 LT" in
  let b2 := str2block "POP PUSH1 0x1" in
  let init_state := (parse_init_state "1") in
  let cs := [[C_LT (C_VAL 10) (C_VAR 0)]] in
  match init_state with
  | Some (_,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

(* LT(X, Y) with ctx. We know X < 10 and optimize the LT(X,20) *)
Compute
let b1 := str2block "PUSH1 0x20 SWAP1 LT" in
let b2 := str2block "POP PUSH1 0x1" in
let init_state := (parse_init_state "1") in
let cs := [[C_LT (C_VAR 0) (C_VAL 10)]] in
match init_state with
| Some (_,sst) =>
    (evm_eq_block_chkr_lazy
       SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
       all_optimization_steps 10 10
       cs sst b1 b2)
| None => false
end.  
  


  End Tests.
