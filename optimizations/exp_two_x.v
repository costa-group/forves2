Require Import bbv.Word.
Require Import Nat. 
Require Import Coq.NArith.NArith.


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


Module Opt_exp_two_x.


Definition WTwo : EVMWord := natToWord EVMWordSize 2.

(* EXP(2,X) = SHL(X,1) *)
Definition optimize_exp_two_x_sbinding : opt_smap_value_type := 
fun (val: smap_value) =>
fun (fcmp: sstack_val_cmp_t) =>
fun (sb: sbindings) =>
fun (maxid: nat) =>
fun (ctx: constraints) =>
fun (ops: stack_op_instr_map) => 
match val with
| SymOp EXP [arg1; arg2] => 
  if fcmp ctx arg1 (Val WTwo) maxid sb maxid sb  ops then
    (SymOp SHL [arg2; Val WOne], true)
  else
    (val, false)
| _ => (val, false)
end.



Lemma exp_two_shl: forall (x: EVMWord) ctx,
evm_exp ctx [WTwo; x] = evm_shl ctx [x; WOne].
Proof.
intros. simpl. unfold wordBin. simpl.
rewrite -> wlshift_alt. 
rewrite -> pow2_shl.
rewrite -> NToWord_nat.
rewrite -> N2Nat.inj_pow.
rewrite -> wordToN_to_nat.
intuition.
Qed.



Lemma optimize_exp_two_x_sbinding_smapv_valid:
opt_smapv_valid_snd optimize_exp_two_x_sbinding.
Proof.
unfold opt_smapv_valid_snd.
intros ctx n fcmp sb val val' flag.
intros _ _ Hvalid_smapv_val Hvalid_sb Hoptm_sbinding.
unfold optimize_exp_two_x_sbinding in Hoptm_sbinding.
destruct (val) as [basicv|pushtagv|label args|offset smem|key sstrg|
  offset size smem] eqn: eq_val; try inject_rw Hoptm_sbinding eq_val'.
destruct label eqn: eq_label; try inject_rw Hoptm_sbinding eq_val'.
(* EXP *)
destruct args as [|arg1 r1]; try inject_rw Hoptm_sbinding eq_val'.
destruct r1 as [|arg2 r2]; try inject_rw Hoptm_sbinding eq_val'.
destruct r2; try inject_rw Hoptm_sbinding eq_val'.
destruct (fcmp ctx arg1 (Val WTwo) n sb n sb  evm_stack_opm)
    eqn: eq_fcmp_arg1; try inject_rw Hoptm_sbinding eq_val'.
injection Hoptm_sbinding as eq_val' eq_flag.
rewrite <- eq_val'.
simpl in Hvalid_smapv_val. unfold valid_stack_op_instr in Hvalid_smapv_val.
simpl in Hvalid_smapv_val.
destruct Hvalid_smapv_val as [_ [Hvalid_arg1 [Hvalid_arg2 _]]].
simpl. unfold valid_stack_op_instr. simpl.
intuition.
Qed.


Lemma optimize_exp_two_x_sbinding_snd:
opt_sbinding_snd optimize_exp_two_x_sbinding.
Proof.
unfold opt_sbinding_snd.
intros val val' fcmp sb maxidx ctx idx flag Hsafe_sstack_val_cmp
  Hvalid Hissat Hoptm_sbinding.
split.
- (* valid_sbindings *)
  apply valid_bindings_snd_opt with (val:=val)(opt:=optimize_exp_two_x_sbinding)
    (fcmp:=fcmp)(flag:=flag)(ctx:=ctx); try assumption.
  apply optimize_exp_two_x_sbinding_smapv_valid. 
    
- (* evaluation is preserved *) 
  intros model mem strg ext v Hismodel Heval_orig.
  unfold optimize_exp_two_x_sbinding in Hoptm_sbinding.
  pose proof (Hvalid_maxidx  maxidx idx val sb evm_stack_opm
      Hvalid) as eq_maxidx_idx.
  destruct val as [vv|vv|label args|offset smem|key sstrg|offset seze smem]
    eqn: eq_val; try inject_rw Hoptm_sbinding eq_val'.
  (* SymOp label args *)
  destruct label; try inject_rw Hoptm_sbinding eq_val'.
  destruct args as [|arg1 r1] eqn: eq_args; 
    try inject_rw Hoptm_sbinding eq_val'.
  destruct r1 as [|arg2 r2] eqn: eq_r1; 
    try inject_rw Hoptm_sbinding eq_val'.
  destruct r2; try inject_rw Hoptm_sbinding eq_val'.
  destruct (fcmp ctx arg1 (Val WTwo) idx sb idx sb ) 
    eqn: fcmp_arg1_two; try inject_rw Hoptm_sbinding eq_val'.
  (* arg1 ~ WTwo *)
  injection Hoptm_sbinding as eq_val' _. 
  rewrite <- eq_val'.
  unfold eval_sstack_val in Heval_orig. simpl in Heval_orig.
  rewrite -> PeanoNat.Nat.eqb_refl in Heval_orig.
  simpl in Heval_orig.
  destruct (eval_sstack_val' maxidx arg1 model mem strg ext idx sb evm_stack_opm)
    as [varg1|] eqn: eval_arg1; try discriminate.
  destruct (eval_sstack_val' maxidx arg2 model mem strg ext idx sb evm_stack_opm)
    as [varg2|] eqn: eval_arg2; try discriminate.
  unfold safe_sstack_val_cmp in Hsafe_sstack_val_cmp.

  unfold valid_bindings in Hvalid.
  destruct Hvalid as [eq_maxid [Hvalid_smap_value Hvalid_bindings_sb]].
  unfold valid_smap_value in Hvalid_smap_value.
  unfold valid_stack_op_instr in Hvalid_smap_value.
  simpl in Hvalid_smap_value.
  destruct (Hvalid_smap_value) as [_ [Hvalid_arg1 [Hvalid_arg2 _ ]]].
  fold valid_bindings in Hvalid_bindings_sb.

  pose proof (valid_sstack_value_const  idx v) as Hvalid_zero.
  pose proof (Hsafe_sstack_val_cmp ctx arg1 (Val WTwo) idx sb idx sb 
     evm_stack_opm Hissat Hvalid_arg1 Hvalid_zero Hvalid_bindings_sb
    Hvalid_bindings_sb fcmp_arg1_two model mem strg ext Hismodel)
    as [vtwo [Heval_arg1 Heval_vtwo]].
  assert (Heval_arg1_copy := Heval_arg1).
  unfold eval_sstack_val in Heval_arg1_copy.
  rewrite -> eval_sstack_val_const in Heval_vtwo.
  rewrite <- Heval_vtwo in Heval_arg1.
    
  unfold eval_sstack_val.
  rewrite -> eq_maxid in eval_arg1.
  rewrite -> Heval_arg1_copy in eval_arg1.
  injection eval_arg1 as eq_varg1.
  injection Heval_vtwo as eq_vtwo.
  rewrite <- eq_varg1 in Heval_orig.
  rewrite <- eq_vtwo in Heval_orig.
  simpl. rewrite -> PeanoNat.Nat.eqb_refl.
  simpl. rewrite -> eval_arg2.
  rewrite <- eq_maxidx_idx.
  rewrite -> eval_sstack_val'_const.
  rewrite <- Heval_orig.
    
  rewrite -> exp_two_shl.
  reflexivity.
Qed.


End Opt_exp_two_x.
