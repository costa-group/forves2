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

Require Import FORVES2.context.
Import Context.

Require Import List.
Import ListNotations.


Module Opt_gt_x_x.


(* GT(X,X) = 0 *)
Definition optimize_gt_x_x_sbinding : opt_smap_value_type := 
fun (val: smap_value) =>
fun (fcmp: sstack_val_cmp_t) =>
fun (sb: sbindings) =>
fun (maxid: nat) =>
fun (ctx: ctx_t) =>
fun (ops: stack_op_instr_map) => 
match val with
| SymOp GT [arg1; arg2] => 
  if fcmp ctx arg1 arg2 maxid sb maxid sb  ops then
     (SymBasicVal (Val WZero), true)
  else
    (val, false)
| _ => (val, false)
end.






Lemma optimize_gt_x_x_sbinding_smapv_valid:
opt_smapv_valid_snd optimize_gt_x_x_sbinding.
Proof.
unfold opt_smapv_valid_snd.
intros ctx n fcmp sb val val' flag.
intros _ Hvalid_smapv_val Hvalid_sb Hoptm_sbinding.
unfold optimize_gt_x_x_sbinding in Hoptm_sbinding.
destruct (val) as [basicv|pushtagv|label args|offset smem|key sstrg|
  offset size smem] eqn: eq_val; try inject_rw Hoptm_sbinding eq_val'.
destruct label eqn: eq_label; try inject_rw Hoptm_sbinding eq_val'.
(* GT *)
destruct args as [|arg1 r1]; try inject_rw Hoptm_sbinding eq_val'.
destruct r1 as [|arg2 r2]; try inject_rw Hoptm_sbinding eq_val'.
destruct r2 as [|arg3 r3]; try inject_rw Hoptm_sbinding eq_val'.
destruct (fcmp ctx arg1 arg2 n sb n sb  evm_stack_opm)
  eqn: eq_fcmp_arg1; try inject_rw Hoptm_sbinding eq_val'.
injection Hoptm_sbinding as eq_val' eq_flag.
rewrite <- eq_val'.
simpl. intuition.
Qed.




Lemma gt_x_x_zero: forall (x: EVMWord) ctx,
evm_gt ctx [x; x] = WZero.
Proof.
intros. simpl. rewrite -> N.ltb_irrefl.
reflexivity.
Qed.


Lemma optimize_gt_x_x_sbinding_snd:
opt_sbinding_snd optimize_gt_x_x_sbinding.
Proof.
unfold opt_sbinding_snd.
intros val val' fcmp sb maxidx ctx idx flag Hsafe_sstack_val_cmp
  Hvalid Hoptm_sbinding.
split.
- (* valid_sbindings *)
  apply valid_bindings_snd_opt with (val:=val)(opt:=optimize_gt_x_x_sbinding)
    (fcmp:=fcmp)(flag:=flag)(ctx:=ctx); try assumption.
  apply optimize_gt_x_x_sbinding_smapv_valid. 
    
- (* evaluation is preserved *) 
  intros model mem strg ext v Hismodel Heval_orig.
  unfold optimize_gt_x_x_sbinding in Hoptm_sbinding.
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
  destruct r2 as [|arg3 r3] eqn: eq_r2; 
    try inject_rw Hoptm_sbinding eq_val'.
  destruct (fcmp ctx arg1 arg2 idx sb idx sb ) 
    eqn: fcmp_arg1_arg2; try inject_rw Hoptm_sbinding eq_val'.
  (* arg1 ~ arg2 *)
  injection Hoptm_sbinding as eq_val' _. 
  rewrite <- eq_val'.
  unfold eval_sstack_val in Heval_orig. simpl in Heval_orig.
  rewrite -> PeanoNat.Nat.eqb_refl in Heval_orig.
  simpl in Heval_orig.
  destruct (eval_sstack_val' maxidx arg1 model mem strg ext idx sb evm_stack_opm)
    as [varg1|] eqn: eval_arg1; try discriminate.
  destruct (eval_sstack_val' maxidx arg2 model mem strg ext idx sb evm_stack_opm)
    as [varg2|] eqn: eval_arg2; try discriminate.

  unfold valid_bindings in Hvalid.
  destruct Hvalid as [eq_maxid [Hvalid_smap_value Hvalid_bindings_sb]].
  unfold valid_smap_value in Hvalid_smap_value.
  unfold valid_stack_op_instr in Hvalid_smap_value.
  simpl in Hvalid_smap_value.
  destruct (Hvalid_smap_value) as [_ [Hvalid_arg1 [Hvalid_arg2 _ ]]].
  fold valid_bindings in Hvalid_bindings_sb.

  pose proof (Hsafe_sstack_val_cmp ctx arg1 arg2 idx sb idx sb 
     evm_stack_opm Hvalid_arg1 Hvalid_arg2 Hvalid_bindings_sb
    Hvalid_bindings_sb fcmp_arg1_arg2 model mem strg ext Hismodel)
    as [vv [Heval_arg1 Heval_arg2]].
  unfold eval_sstack_val in Heval_arg1. 
  rewrite -> eq_maxidx_idx in Heval_arg1. 
  unfold eval_sstack_val in Heval_arg2.
  rewrite -> eq_maxidx_idx in Heval_arg2.
  rewrite -> Heval_arg1 in eval_arg1.
  injection eval_arg1 as eq_varg1.
  rewrite <- eq_varg1 in Heval_orig.
  rewrite -> Heval_arg2 in eval_arg2.
  injection eval_arg2 as eq_varg2.
  rewrite <- eq_varg2 in Heval_orig.
  rewrite -> gt_x_x_zero in Heval_orig.
  rewrite <- Heval_orig.
  
  unfold eval_sstack_val. simpl.
  rewrite -> PeanoNat.Nat.eqb_refl. 
  reflexivity. 
Qed.


End Opt_gt_x_x.
