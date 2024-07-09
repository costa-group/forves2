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
  let init_state := (parse_init_state "2 [[v0=v1]]") in
  match init_state with
  | Some (cs,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_Basic SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

Compute 
  let b1 := str2block "PUSH1 0x01" in
  let b2 := str2block "SWAP1 PUSH1 0x01" in
  let init_state := (parse_init_state "2 [[v0=v1]]") in
  match init_state with
  | Some (cs,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_Basic SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

Compute 
  let b1 := str2block "ADD" in
  let b2 := str2block "POP" in
  let init_state := (parse_init_state "2 [[v0=0]]") in
  match init_state with
  | Some (cs,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_Basic SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

Compute 
  let b1 := str2block "ADD" in
  let b2 := str2block "SWAP1 POP" in
  let init_state := (parse_init_state "2 [[v0=0]]") in
  match init_state with
  | Some (cs,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_Basic SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

Compute 
  let b1 := str2block "MUL" in
  let b2 := str2block "POP" in
  let init_state := (parse_init_state "2 [[v0=1]]") in
  match init_state with
  | Some (cs,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_Basic SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

Compute 
  let b1 := str2block "MUL" in
  let b2 := str2block "POP POP PUSH1 0x0" in
  let init_state := (parse_init_state "2 [[v2=0,v2=v2]]") in
  match init_state with
  | Some (cs,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_Basic SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.


Compute 
  let b1 := str2block "DUP2 SWAP1 DUP1 SSTORE SSTORE" in
  let b2 := str2block "SWAP1 DUP2 SWAP1 DUP1 SSTORE SSTORE" in
  let init_state := (parse_init_state "2 [[v0<v2,v2<v1],[v0+1<=v1]]") in
  match init_state with
  | Some (cs,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

Compute 
  let b1 := str2block "ADD" in
  let b2 := str2block "POP" in
  let init_state := (parse_init_state "[0x0,v1] [] [] [] []") in
  match init_state with
  | Some (cs,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

Compute 
  let b1 := str2block "DUP1 MLOAD PUSH1 0x1 ADD MSTORE" in
  let b2 := str2block "PUSH1 0x11 MSTORE" in
  let init_state := (parse_init_state "[v1] [MSTORE v1 0x10] [] [] []") in
  match init_state with
  | Some (cs,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

Compute 
  let b1 := str2block "DUP1 MLOAD PUSH1 0x1 ADD SWAP1 MSTORE" in
  let b2 := str2block "PUSH1 0x11 SWAP1 MSTORE" in
  let init_state := (parse_init_state "[v1] [MSTORE v2 0x10] [] [] [[v2=v1]]") in
  match init_state with
  | Some (cs,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

Compute 
  let b1 := str2block "DUP1 SLOAD PUSH1 0x1 ADD SWAP1 SSTORE" in
  let b2 := str2block "PUSH1 0x11 SWAP1 SSTORE" in
  let init_state := (parse_init_state "[v1] [] [SSTORE v2 0x10] [] [[v2=v1]]") in
  match init_state with
  | Some (cs,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

Compute 
  let b1 := str2block "ADD" in
  let b2 := str2block "POP" in
  let init_state := (parse_init_state "[e0,v1] [] [] [ 0 = OP ADD [v2,0x0]] [[v2=0]]") in
  match init_state with
  | Some (cs,sst) =>
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
  let init_state := (parse_init_state "1 [[0 < v0]]") in
  match init_state with
  | Some (cs,sst) =>
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
  let init_state := (parse_init_state "2 [[v0 < v1]]") in
  match init_state with
  | Some (cs,sst) =>
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
  let init_state := (parse_init_state "1 [[10 < v0]]") in
  match init_state with
  | Some (cs,sst) =>
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
let init_state := (parse_init_state "1 [[v0 < 10]]") in
match init_state with
| Some (cs,sst) =>
    (evm_eq_block_chkr_lazy
       SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
       all_optimization_steps 10 10
       cs sst b1 b2)
| None => false
end.
  

(* LT(X, Y) with ctx when we know Y <= X *)
Compute
  let b1 := str2block "LT" in
  let b2 := str2block "POP POP PUSH1 0x0" in
  let init_state := (parse_init_state "2 [[v1 <= v0]]") in
  match init_state with
  | Some (cs,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.


(* LT(X, Y) with ctx when we know Y <= X *)
Compute
let b1 := str2block "LT ISZERO" in
let b2 := str2block "POP POP PUSH1 0x1" in
let init_state := (parse_init_state "2 [[v1 <= v0]]") in
match init_state with
| Some (cs,sst) =>
    (evm_eq_block_chkr_lazy
       SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
       all_optimization_steps 10 10
       cs sst b1 b2)
| None => false
end.


(* GT(X, Y) with ctx *)
Compute
  let b1 := str2block "GT" in
  let b2 := str2block "POP POP PUSH1 0x1" in
  let init_state := (parse_init_state "2 [[v1 < v0]]") in
  match init_state with
  | Some (cs,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

(* GT(X, Y) with ctx when we know Y <= Y *)
Compute
  let b1 := str2block "GT" in
  let b2 := str2block "POP POP PUSH1 0x0" in
  let init_state := (parse_init_state "2 [[v0 <= v1]]") in
  match init_state with
  | Some (cs,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.


(* GT(X, Y) with ctx when we know X <= Y *)
Compute
let b1 := str2block "GT ISZERO" in
let b2 := str2block "POP POP PUSH1 0x1" in
let init_state := (parse_init_state "2 [[v0 <= v1]]") in
match init_state with
| Some (cs,sst) =>
    (evm_eq_block_chkr_lazy
       SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
       all_optimization_steps 10 10
       cs sst b1 b2)
| None => false
end.


(* EQ(X, Y) with ctx *)
Compute
  let b1 := str2block "EQ" in
  let b2 := str2block "POP POP PUSH1 0x1" in
  let init_state := (parse_init_state "2 [[v1 = v0]]") in
  match init_state with
  | Some (cs,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

(* EQ(X, Y) with ctx when we know X < Y *)
Compute
  let b1 := str2block "EQ" in
  let b2 := str2block "POP POP PUSH1 0x0" in
  let init_state := (parse_init_state "2 [[v0 < v1]]") in
  match init_state with
  | Some (cs,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

  
(* EQ(X, Y) with ctx when we know Y < X *)
Compute
  let b1 := str2block "EQ" in
  let b2 := str2block "POP POP PUSH1 0x0" in
  let init_state := (parse_init_state "2 [[v1 < v0]]") in
  match init_state with
  | Some (cs,sst) =>
      (evm_eq_block_chkr_lazy
         SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
         all_optimization_steps 10 10
         cs sst b1 b2)
  | None => false
  end.

(* EQ(X, Y) with ctx when we know X < Y *)
Compute
let b1 := str2block "EQ ISZERO" in
let b2 := str2block "POP POP PUSH1 0x1" in
let init_state := (parse_init_state "2 [[v0 < v1]]") in
match init_state with
| Some (cs,sst) =>
    (evm_eq_block_chkr_lazy
       SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
       all_optimization_steps 10 10
       cs sst b1 b2)
| None => false
end.


(* EVAL with EQ constants in constraints. MUST RETURN FALSE *)
Compute
let b1 := str2block "ADD" in
let b2 := str2block "POP POP PUSH1 0x4" in
let init_state := (parse_init_state "2 [[v0 = 2, v1 = 2]]") in
match init_state with
| Some (cs,sst) =>
    (evm_eq_block_chkr_lazy
       SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
       all_optimization_steps 10 10
       cs sst b1 b2)
| None => false
end.


(* EVAL with EQ constants in stack. MUST RETURN TRUE *)
Eval cbv in
let b1 := str2block "ADD" in
let b2 := str2block "POP POP PUSH1 0x4" in
let init_state := (parse_init_state "[0x2,0x2] [] [] [] []") in
match init_state with
| Some (cs,sst) =>
    (evm_eq_block_chkr_lazy
       SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
       all_optimization_steps 10 10
       cs sst b1 b2)
| None => false
end.


(* SUB(X,X) with EQ constants in constraints. *)
Compute
let b1 := str2block "SUB" in
let b2 := str2block "POP POP PUSH1 0x0" in
let init_state := (parse_init_state "2 [[v0=v1,v0<v1],[v0=v1,v1<v0]]") in
match init_state with
| Some (cs,sst) =>
    (evm_eq_block_chkr_lazy
       SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
       all_optimization_steps 10 10
       cs sst b1 b2)
| None => false
end.


(* DIV(X,X) with constants <> 0*)
Eval cbv in
let b1 := str2block "DIV" in
let b2 := str2block "POP POP PUSH1 0x1" in
let init_state := (parse_init_state "[0x2,0x2] [] [] [] []") in
match init_state with
| Some (cs,sst) =>
    (evm_eq_block_chkr_lazy
       SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
       all_optimization_steps 10 10
       cs sst b1 b2)
| None => false
end.

(* DIV(X,X) with constants = 0*)
Eval cbv in
let b1 := str2block "DIV" in
let b2 := str2block "POP POP PUSH1 0x0" in
let init_state := (parse_init_state "[0x0,0x0] [] [] [] []") in
match init_state with
| Some (cs,sst) =>
    (evm_eq_block_chkr_lazy
       SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
       all_optimization_steps 10 10
       cs sst b1 b2)
| None => false
end.


(* DIV(X,0) with constraints *)
Compute
let b1 := str2block "DIV" in
let b2 := str2block "POP POP PUSH1 0x0" in
let init_state := (parse_init_state "2 [[v0=v1,v0=0]]") in
match init_state with
| Some (cs,sst) =>
    (evm_eq_block_chkr_lazy
       SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
       all_optimization_steps 10 10
       cs sst b1 b2)
| None => false
end.


(* DIV(X,x) with X > 0 in constraints *)
Eval cbv in
let b1 := str2block "DIV" in
let b2 := str2block "POP POP PUSH1 0x1" in
let init_state := (parse_init_state "2 [[v0=v1,0<v1]]") in
match init_state with
| Some (cs,sst) =>
    (evm_eq_block_chkr_lazy
       SMemUpdater_Basic SStrgUpdater_Basic MLoadSolver_Basic SLoadSolver_Basic SStackValCmp_Basic SMemCmp_PO SStrgCmp_PO SHA3Cmp_Basic ImpChkr_Oct 
       all_optimization_steps 10 10
       cs sst b1 b2)
| None => false
end.



End Tests.
