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

Module SStorageCmpImpl.



  (* just handles the case of empty storage updates *)
  Definition trivial_storage_cmp (sstack_val_cmp : sstack_val_cmp_t) (ctx: constraints) (sstrg1 sstrg2 :sstorage) (maxidx1: nat) (sb1: sbindings) (maxidx2: nat) (sb2: sbindings) (ops: stack_op_instr_map) : bool :=
  match sstrg1,sstrg2 with
  | [], [] => true
  | _, _ =>  false
  end.

  (* identical storage updates *)
  Fixpoint basic_storage_cmp (sstack_val_cmp : sstack_val_cmp_t) (ctx: constraints) (sstrg1 sstrg2 :sstorage) (maxidx1: nat) (sb1: sbindings) (maxidx2: nat) (sb2: sbindings) (ops: stack_op_instr_map) : bool :=
  match sstrg1,sstrg2 with
  | [], [] => true
  | (U_SSTORE _ skey1 svalue1)::sstrg1', (U_SSTORE _ skey2 svalue2)::sstrg2' =>
      if sstack_val_cmp ctx skey1 skey2 maxidx1 sb1 maxidx2 sb2 ops then 
        if sstack_val_cmp ctx svalue1 svalue2 maxidx1 sb1 maxidx2 sb2 ops then
          basic_storage_cmp sstack_val_cmp ctx sstrg1' sstrg2' maxidx1 sb1 maxidx2 sb2 ops
        else
          false
      else
        false
  | _, _ => false
  end.

  
  Definition swap_storage_update (ctx: constraints) (u1 u2 : storage_update sstack_val) (maxid: nat) (sb: sbindings) : bool :=
    match u1, u2 with
    | U_SSTORE _ key1 _, U_SSTORE _ key2 _ => 
        match follow_in_smap key1 maxid sb, follow_in_smap key2 maxid sb with
        | Some (FollowSmapVal (SymBasicVal (Val v1)) _ _), Some (FollowSmapVal (SymBasicVal (Val v2)) _ _) => ((wordToN v2) <? (wordToN v1))%N
        | _, _ => false
        end
    end.
  
  Fixpoint reorder_updates' (d : nat) (ctx: constraints) (sstrg :sstorage) (maxid: nat) (sb: sbindings) : bool * sstorage :=
    match d with
    | O => (false,sstrg)
    | S d' =>
        match sstrg with
        | u1::u2::sstrg' =>
            if swap_storage_update ctx u1 u2 maxid sb then
              match reorder_updates' d' ctx (u1::sstrg') maxid sb with
                (_,sstrg'') => (true,u2::sstrg'')
              end
            else
              match reorder_updates' d' ctx (u2::sstrg') maxid sb with
                (r,sstrg'') => (r,u1::sstrg'')
              end
        | _ => (false,sstrg)
        end
    end.

  (* n is basically the length of sstrg, we pass it as a parameter to
  avoid computing *)
  Fixpoint reorder_storage_updates (d n: nat) (ctx: constraints) (sstrg :sstorage) (maxid: nat) (sb: sbindings) : sstorage :=
    match d with
    | O => sstrg
    | S d' =>
        match reorder_updates' n ctx sstrg maxid sb with
        |  (changed,sstrg') =>
             if changed then
               reorder_storage_updates d' n ctx sstrg' maxid sb
             else
               sstrg'
        end
    end.


  Definition po_storage_cmp (sstack_val_cmp : sstack_val_cmp_t) (ctx: constraints)  (sstrg1 sstrg2 :sstorage) (maxidx1: nat) (sb1: sbindings) (maxidx2: nat) (sb2: sbindings) (ops: stack_op_instr_map) : bool :=
    let n1 := length sstrg1 in
    let n2 := length sstrg2 in
    if (n1 =? n2) then 
      let sstrg1' := reorder_storage_updates n1 n1 ctx sstrg1 maxidx1 sb1 in
      let sstrg2' := reorder_storage_updates n2 n2 ctx sstrg2 maxidx2 sb2 in
      basic_storage_cmp sstack_val_cmp ctx sstrg1' sstrg2' maxidx1 sb1 maxidx2 sb2 ops
    else
      false.
      
End SStorageCmpImpl.
