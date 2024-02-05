Require Import bbv.Word.
Require Import Nat. 
Require Import Coq.NArith.NArith.
Require Import PeanoNat.

Require Import FORVES2.constants.
Import Constants.

Require Import FORVES2.symbolic_state.
Import SymbolicState.

Require Import FORVES2.symbolic_state_eval.
Import SymbolicStateEval.

Require Import FORVES2.symbolic_state_cmp.
Import SymbolicStateCmp.

Require Import FORVES2.valid_symbolic_state.
Import ValidSymbolicState.

Require Import FORVES2.execution_state.
Import ExecutionState.

Require Import FORVES2.stack_operation_instructions.
Import StackOpInstrs.

Require Import FORVES2.program.
Import Program.

Require Import FORVES2.symbolic_state_cmp_impl.
Import SymbolicStateCmpImpl.

Require Import FORVES2.symbolic_state_eval_facts.
Import SymbolicStateEvalFacts.

Require Import FORVES2.valid_symbolic_state.
Import ValidSymbolicState.

Require Import FORVES2.misc.
Import Misc.

Require Import FORVES2.eval_common.
Import EvalCommon.

Require Import FORVES2.concrete_interpreter.
Import ConcreteInterpreter.

Require Import FORVES2.optimizations_def.
Import Optimizations_Def.

Require Import FORVES2.optimizations_common.
Import Optimizations_Common.

Require Import FORVES2.constraints.
Import Constraints.

Require Import List.
Import ListNotations.


Module Opt_iszero2_lt.


(* ISZERO(ISZERO(LT(X,Y)) = LT(X,Y) *)
Definition optimize_iszero2_lt_sbinding : opt_smap_value_type := 
fun (val: smap_value) =>
fun (fcmp: sstack_val_cmp_t) =>
fun (sb: sbindings) =>
fun (maxid: nat) =>
fun (ctx: constraints) =>
fun (ops: stack_op_instr_map) => 
match val with
| SymOp ISZERO [arg1] => 
  match follow_in_smap arg1 maxid sb with
  | Some (FollowSmapVal (SymOp ISZERO [arg2]) idx' sb') => 
      match follow_in_smap arg2 idx' sb' with
      | Some (FollowSmapVal (SymOp LT [x;y]) idx'' sb'') => 
          (SymOp LT [x;y], true)
      | _ => (val, false)
      end
  | _ => (val, false)
  end
| _ => (val, false)
end.


Lemma evm_iszero2_lt_snd: forall ctx x y,
evm_iszero ctx [evm_iszero ctx [evm_lt ctx [x; y]]] = evm_lt ctx [x; y].
Proof.
intros ctx x y.
unfold evm_lt.
destruct (wordToN x <? wordToN y)%N eqn: eq_y_lt_x; try reflexivity.
Qed.


Lemma optimize_iszero2_lt_sbinding_smapv_valid:
opt_smapv_valid_snd optimize_iszero2_lt_sbinding.
Proof.
unfold opt_smapv_valid_snd.
intros ctx n fcmp sb val val' flag.
intros Hvalid_smapv_val Hvalid Hoptm_sbinding.
unfold optimize_iszero2_lt_sbinding in Hoptm_sbinding.
destruct (val) as [basicv|pushtagv|label args|offset smem|key sstrg|
  offset size smem] eqn: eq_val; 
  try inject_rw Hoptm_sbinding eq_val'.
destruct label; try try inject_rw Hoptm_sbinding eq_val'.
destruct args as [|arg1 r1]; try inject_rw Hoptm_sbinding eq_val'.
destruct r1; try inject_rw Hoptm_sbinding eq_val'.
destruct (follow_in_smap arg1 n sb) as [fsmv2|] eqn: eq_follow_arg1;
  try inject_rw Hoptm_sbinding eq_val'.
destruct fsmv2 as [smv2 idx' sb'].
destruct smv2 as [basicv|pushtagv|label2 args2|offset smem|key sstrg|
  offset size smem] eqn: eq_args2; try inject_rw Hoptm_sbinding eq_val'.
  
destruct label2; try try inject_rw Hoptm_sbinding eq_val'.
destruct args2 as [|arg2 r2]; try inject_rw Hoptm_sbinding eq_val'.
destruct r2; try inject_rw Hoptm_sbinding eq_val'.
destruct (follow_in_smap arg2) as [fsmv3|] eqn: eq_follow_arg2;
  try inject_rw Hoptm_sbinding eq_val'.
destruct fsmv3 as [smv3 idx'' sb''].
destruct smv3 as [basicv|pushtagv|label3 args3|offset smem|key sstrg|
  offset size smem] eqn: eq_args3; try inject_rw Hoptm_sbinding eq_val'.
destruct label3; try inject_rw Hoptm_sbinding eq_val'.
destruct args3 as [|x args3']; try inject_rw Hoptm_sbinding eq_val'.
destruct args3' as [|y args3'']; try inject_rw Hoptm_sbinding eq_val'.
destruct args3''; try inject_rw Hoptm_sbinding eq_val'.
injection Hoptm_sbinding as eq_val' _.
rewrite <- eq_val'.

simpl in Hvalid_smapv_val. unfold valid_stack_op_instr in Hvalid_smapv_val.
simpl in Hvalid_smapv_val.
destruct Hvalid_smapv_val as [_ [Hvalid_arg1 _]].
pose proof (valid_follow_in_smap sb arg1  n evm_stack_opm
  (SymOp ISZERO [arg2]) idx' sb' Hvalid_arg1 Hvalid eq_follow_arg1) 
  as [Hvalid_arg2 [Hvalid_sb' Himpl2]].
pose proof (not_basic_value_smv_symop ISZERO [arg2]) as Hnot_basic2.
apply Himpl2 in Hnot_basic2.

simpl in Hvalid_arg2. unfold valid_stack_op_instr in Hvalid_arg2.
simpl in Hvalid_arg2. destruct Hvalid_arg2 as [_ [Hvalid_arg2 _]].
pose proof (valid_follow_in_smap sb' arg2  idx' evm_stack_opm
  (SymOp LT [x;y]) idx'' sb'' Hvalid_arg2 Hvalid_sb' eq_follow_arg2)
  as [Hvalid_arg3 [Hvalid_sb'' Himpl3]].
pose proof (not_basic_value_smv_symop LT [x;y]) as Hnot_basic3.
apply Himpl3 in Hnot_basic3.

pose proof (gt_add idx' idx'' Hnot_basic3) as [k3 eq_idx']. 
pose proof (gt_add n idx' Hnot_basic2) as [k2 eq_n].
rewrite -> eq_idx' in eq_n.
rewrite <- Nat.add_assoc in eq_n.
apply valid_smap_value_incr with (m:=k3+k2) in Hvalid_arg3.
rewrite -> eq_n.
assumption.
Qed.


Lemma optimize_iszero2_lt_sbinding_snd:
opt_sbinding_snd optimize_iszero2_lt_sbinding.
Proof.
unfold opt_sbinding_snd.
intros val val' fcmp sb maxidx ctx idx flag Hsafe_sstack_val_cmp
  Hvalid Hissat Hoptm_sbinding.
split.
- (* valid_sbindings *)
  apply valid_bindings_snd_opt with (val:=val)(opt:=optimize_iszero2_lt_sbinding)
    (fcmp:=fcmp)(flag:=flag)(ctx:=ctx); try assumption.
  apply optimize_iszero2_lt_sbinding_smapv_valid. 

- (* evaluation is preserved *) 
  intros model mem strg ext v Hismodel Heval_orig.
  unfold optimize_iszero2_lt_sbinding in Hoptm_sbinding.
  destruct (val) as [basicv|pushtagv|label1 args1|offset smem|key sstrg|
  offset size smem] eqn: eq_val; 
  try inject_rw Hoptm_sbinding eq_val'.
  destruct label1; try try inject_rw Hoptm_sbinding eq_val'.
  destruct args1 as [|arg1 r1]; try inject_rw Hoptm_sbinding eq_val'.
  destruct r1; try inject_rw Hoptm_sbinding eq_val'.
  destruct (follow_in_smap arg1 idx sb) as [fsmv2|] eqn: eq_follow_arg1;
  try inject_rw Hoptm_sbinding eq_val'.
  destruct fsmv2 as [smv2 idx' sb'].
  destruct smv2 as [basicv|pushtagv|label2 args2|offset smem|key sstrg|
    offset size smem] eqn: eq_args2; try inject_rw Hoptm_sbinding eq_val'.
  
  destruct label2; try try inject_rw Hoptm_sbinding eq_val'.
  destruct args2 as [|arg2 r2]; try inject_rw Hoptm_sbinding eq_val'.
  destruct r2; try inject_rw Hoptm_sbinding eq_val'.
  destruct (follow_in_smap arg2) as [fsmv3|] eqn: eq_follow_arg2;
    try inject_rw Hoptm_sbinding eq_val'.
  destruct fsmv3 as [smv3 idx'' sb''].
  destruct smv3 as [basicv|pushtagv|label3 args3|offset smem|key sstrg|
    offset size smem] eqn: eq_args3; try inject_rw Hoptm_sbinding eq_val'.
  destruct label3; try try inject_rw Hoptm_sbinding eq_val'.
  destruct args3 as [|x args3']; try inject_rw Hoptm_sbinding eq_val'.
  destruct args3' as [|y args3'']; try inject_rw Hoptm_sbinding eq_val'.
  destruct args3''; try inject_rw Hoptm_sbinding eq_val'.
  injection Hoptm_sbinding as eq_val' _.
  rewrite <- eq_val'.
  
  unfold eval_sstack_val in Heval_orig.
  simpl in Heval_orig. rewrite -> PeanoNat.Nat.eqb_refl in Heval_orig.
  simpl in Heval_orig.
  destruct (eval_sstack_val' maxidx arg1 model mem strg ext idx sb evm_stack_opm)
    as [arg1_v|] eqn: eval_arg1; try discriminate.
  destruct maxidx as [|maxidx']; try discriminate. simpl in eval_arg1.
  rewrite -> eq_follow_arg1 in eval_arg1. simpl in eval_arg1.
  destruct maxidx' as [|maxidx'']; try discriminate.
  simpl in eval_arg1. rewrite -> eq_follow_arg2 in eval_arg1.
  simpl in eval_arg1.
  
  destruct (eval_sstack_val' maxidx'' x model mem strg ext idx'' sb'' 
    evm_stack_opm) as [xv|] eqn: eval_x; try discriminate.
  destruct (eval_sstack_val' maxidx'' y model mem strg ext idx'' sb'' 
    evm_stack_opm) as [yv|] eqn: eval_y; try discriminate.    
  unfold eval_sstack_val.
  
  pose proof (follow_suffix sb arg1 idx (SymOp ISZERO [arg2]) idx' sb'
    eq_follow_arg1) as [p1 eq_sb].
  pose proof (follow_suffix sb' arg2 idx'(SymOp LT [x; y]) idx'' sb''
    eq_follow_arg2) as [p2 eq_sb'].
  rewrite -> eq_sb' in eq_sb.
  rewrite -> app_assoc in eq_sb.
  
  rewrite -> eval_sstack_val'_one_step. 
  rewrite -> follow_in_smap_head_op.
  rewrite -> evm_stack_opm_LT.
  rewrite -> length_two.
  unfold map_option.
  
  simpl in Hvalid. destruct Hvalid as [_ [Hvalid_arg1 Hvalid_sb]].
  apply eval_sstack_val'_preserved_when_depth_extended in eval_x as eval_x.
  apply eval_sstack_val'_preserved_when_depth_extended in eval_x as eval_x.
  rewrite -> eval'_maxidx_indep_eq with (m:=idx) in eval_x.
  pose proof (eval_sstack_val'_extend_sb  (S (S maxidx'')) model 
    mem strg ext idx sb sb'' evm_stack_opm (p1 ++ p2) Hvalid_sb eq_sb x
    xv eval_x) as eval_x_sb.
  rewrite -> eval_x_sb. 
  apply eval_sstack_val'_preserved_when_depth_extended in eval_y as eval_y.
  apply eval_sstack_val'_preserved_when_depth_extended in eval_y as eval_y.
  rewrite -> eval'_maxidx_indep_eq with (m:=idx) in eval_y.
  pose proof (eval_sstack_val'_extend_sb  (S (S maxidx'')) model 
    mem strg ext idx sb sb'' evm_stack_opm (p1 ++ p2) Hvalid_sb eq_sb y
    yv eval_y) as eval_y_sb.
  rewrite -> eval_y_sb. 

  rewrite <- Heval_orig.
  injection eval_arg1 as eq_arg1_v.
  rewrite <- eq_arg1_v. 
  rewrite <- evm_iszero2_lt_snd.
  reflexivity.
Qed.

End Opt_iszero2_lt.
