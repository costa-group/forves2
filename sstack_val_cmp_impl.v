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

Require Import FORVES2.symbolic_state_dec.
Import SymbolicStateDec.

Require Import FORVES2.constraints.
Import Constraints.

Require Import FORVES2.context.
Import Context.

Module SStackValCmpImpl.

  Definition trivial_compare_sstack_val (smemory_cmp: smemory_cmp_ext_t) (sstorage_cmp: sstorage_cmp_ext_t) (sha3_cmp: sha3_cmp_ext_t) (d: nat) (ctx: ctx_t) (sv1 sv2: sstack_val) (maxidx1: nat) (sb1: sbindings) (maxidx2: nat) (sb2: sbindings) (ops: stack_op_instr_map) : bool :=
    match d with
    | 0 => false
    | S d' =>
        match sv1,sv2 with
        | Val w1, Val w2 => weqb w1 w2
        | InVar n1, InVar n2 => (n1 =? n2)
        | FreshVar n1, FreshVar n2 =>
            if (n1 =? n2)
            then if (maxidx1 =? maxidx2)
                 then if (sbindings_eq_dec sb1 sb2)
                      then true
                      else false
                 else false
            else false
        | _, _ => false
        end
    end.

Fixpoint basic_compare_sstack_val (smemory_cmp: smemory_cmp_ext_t) (sstorage_cmp: sstorage_cmp_ext_t) (sha3_cmp: sha3_cmp_ext_t) (d: nat) (ctx: ctx_t) (sv1 sv2: sstack_val) (maxidx1: nat) (sb1: sbindings) (maxidx2: nat) (sb2: sbindings) (ops: stack_op_instr_map) : bool :=
  match d with
  | 0 => false
  | S d' =>
      let basic_compare_sstack_val_rec :=
        basic_compare_sstack_val smemory_cmp sstorage_cmp sha3_cmp d' in
      match follow_in_smap sv1 maxidx1 sb1 with
      | None => false
      | Some (FollowSmapVal smv1 maxidx1' sb1') =>
          match  follow_in_smap sv2 maxidx2 sb2 with
          | None => false
          | Some (FollowSmapVal smv2 maxidx2' sb2') =>
              match smv1, smv2 with 
              | SymBasicVal sv1', SymBasicVal sv2' =>
                  match sv1',sv2' with
                  | Val w1, Val w2 => weqb w1 w2
                  | InVar n1, InVar n2 => if (n1 =? n2) then true else chk_eq_wrt_ctx ctx sv1' sv2'
                  | _, _ => chk_eq_wrt_ctx ctx sv1' sv2'
                  end
              | SymMETAPUSH cat1 v1, SymMETAPUSH cat2 v2 => andb (cat1 =? cat2)%N (v1 =? v2)%N
              | SymOp label1 args1, SymOp label2 args2 =>
                  if label1 =?i label2 then
                    match ops label1 with
                      OpImp _ _ H_Comm _ =>
                        match (fold_right_two_lists (fun e1 e2 => basic_compare_sstack_val_rec ctx e1 e2 maxidx1' sb1' maxidx2' sb2' ops) args1 args2) with
                        | true => true
                        | false =>
                            match H_Comm with
                            | Some comm_proof =>
                                match args1, args2 with
                                | [a1;a2],[b1;b2] =>
                                    if basic_compare_sstack_val_rec ctx a1 b2 maxidx1' sb1' maxidx2' sb2' ops
                                    then basic_compare_sstack_val_rec ctx a2 b1 maxidx1' sb1' maxidx2' sb2' ops
                                    else false
                                | _, _ => false
                                end
                            | None => false
                            end
                        end
                    end
                  else false
              | SymMLOAD soffset1 smem1, SymMLOAD soffset2 smem2 =>
                  if basic_compare_sstack_val smemory_cmp sstorage_cmp sha3_cmp d' ctx soffset1 soffset2 maxidx1' sb1' maxidx2' sb2' ops
                  then smemory_cmp basic_compare_sstack_val_rec ctx smem1 smem2 maxidx1' sb1' maxidx2' sb2' ops
                  else false
              | SymSLOAD skey1 sstrg1, SymSLOAD skey2 sstrg2 => 
                  if basic_compare_sstack_val smemory_cmp sstorage_cmp sha3_cmp d' ctx skey1 skey2 maxidx1' sb1' maxidx2' sb2' ops
                  then sstorage_cmp basic_compare_sstack_val_rec ctx sstrg1 sstrg2 maxidx1' sb1' maxidx2' sb2' ops
                  else false
              | SymSHA3 soffset1 ssize1 smem1, SymSHA3 soffset2 ssize2 smem2 =>
                  (* the nested if is to avoid using band *)
                  if (if basic_compare_sstack_val_rec ctx soffset1 soffset2 maxidx1' sb1' maxidx2' sb2' ops then
                        if basic_compare_sstack_val_rec ctx ssize1 ssize2 maxidx1' sb1' maxidx2' sb2' ops then
                           smemory_cmp basic_compare_sstack_val_rec ctx smem1 smem2 maxidx1' sb1' maxidx2' sb2' ops 
                        else
                          false
                      else
                        false)
                  then true
                  else 
                    sha3_cmp basic_compare_sstack_val_rec ctx soffset1 ssize1 smem1 soffset2 ssize2 smem2 maxidx1' sb1' maxidx2' sb2' ops
              | _, _ => false
              end
          end
      end
  end.


Fixpoint basic_compare_sstack_val_w_eq_chk (smemory_cmp: smemory_cmp_ext_t) (sstorage_cmp: sstorage_cmp_ext_t) (sha3_cmp: sha3_cmp_ext_t) (d: nat) (ctx: ctx_t) (sv1 sv2: sstack_val) (maxidx1: nat) (sb1: sbindings) (maxidx2: nat) (sb2: sbindings) (ops: stack_op_instr_map) : bool :=
  if (trivial_compare_sstack_val smemory_cmp sstorage_cmp sha3_cmp d ctx sv1 sv2 maxidx1 sb1 maxidx2 sb2 ops)
  then true
  else
  match d with
  | 0 => false
  | S d' =>
      let basic_compare_sstack_val_w_eq_chk_rec :=
        basic_compare_sstack_val_w_eq_chk smemory_cmp sstorage_cmp sha3_cmp d' in
      match follow_in_smap sv1 maxidx1 sb1 with
      | None => false
      | Some (FollowSmapVal smv1 maxidx1' sb1') =>
          match  follow_in_smap sv2 maxidx2 sb2 with
          | None => false
          | Some (FollowSmapVal smv2 maxidx2' sb2') =>
              match smv1, smv2 with 
              | SymBasicVal sv1', SymBasicVal sv2' =>
                  match sv1',sv2' with
                  | Val w1, Val w2 => weqb w1 w2
                  | InVar n1, InVar n2 => if (n1 =? n2) then true else chk_eq_wrt_ctx ctx sv1' sv2'
                  | _, _ => chk_eq_wrt_ctx ctx sv1' sv2'
                  end
              | SymMETAPUSH cat1 v1, SymMETAPUSH cat2 v2 => andb (cat1 =? cat2)%N (v1 =? v2)%N
              | SymOp label1 args1, SymOp label2 args2 =>
                  if label1 =?i label2 then
                    match ops label1 with
                      OpImp _ _ H_Comm _ =>
                        match (fold_right_two_lists (fun e1 e2 => basic_compare_sstack_val_w_eq_chk_rec ctx e1 e2 maxidx1' sb1' maxidx2' sb2' ops) args1 args2) with
                        | true => true
                        | false =>
                            match H_Comm with
                            | Some comm_proof =>
                                match args1, args2 with
                                | [a1;a2],[b1;b2] =>
                                    if basic_compare_sstack_val_w_eq_chk_rec ctx a1 b2 maxidx1' sb1' maxidx2' sb2' ops
                                    then basic_compare_sstack_val_w_eq_chk_rec ctx a2 b1 maxidx1' sb1' maxidx2' sb2' ops
                                    else false
                                | _, _ => false
                                end
                            | None => false
                            end
                        end
                    end
                  else false
              | SymMLOAD soffset1 smem1, SymMLOAD soffset2 smem2 =>
                  if basic_compare_sstack_val_w_eq_chk smemory_cmp sstorage_cmp sha3_cmp d' ctx soffset1 soffset2 maxidx1' sb1' maxidx2' sb2' ops
                  then smemory_cmp basic_compare_sstack_val_w_eq_chk_rec ctx smem1 smem2 maxidx1' sb1' maxidx2' sb2' ops
                  else false
              | SymSLOAD skey1 sstrg1, SymSLOAD skey2 sstrg2 => 
                  if basic_compare_sstack_val_w_eq_chk smemory_cmp sstorage_cmp sha3_cmp d' ctx skey1 skey2 maxidx1' sb1' maxidx2' sb2' ops
                  then sstorage_cmp basic_compare_sstack_val_w_eq_chk_rec ctx sstrg1 sstrg2 maxidx1' sb1' maxidx2' sb2' ops
                  else false
              | SymSHA3 soffset1 ssize1 smem1, SymSHA3 soffset2 ssize2 smem2 =>
                  (* the nested if is to avoid using band *)
                  if (if basic_compare_sstack_val_w_eq_chk_rec ctx soffset1 soffset2 maxidx1' sb1' maxidx2' sb2' ops then
                        if basic_compare_sstack_val_w_eq_chk_rec ctx ssize1 ssize2 maxidx1' sb1' maxidx2' sb2' ops then
                           smemory_cmp basic_compare_sstack_val_w_eq_chk_rec ctx smem1 smem2 maxidx1' sb1' maxidx2' sb2' ops 
                        else
                          false
                      else
                        false)
                  then true
                  else 
                    sha3_cmp basic_compare_sstack_val_w_eq_chk_rec ctx soffset1 ssize1 smem1 soffset2 ssize2 smem2 maxidx1' sb1' maxidx2' sb2' ops
              | _, _ => false
              end
          end
      end
  end.





End SStackValCmpImpl.
