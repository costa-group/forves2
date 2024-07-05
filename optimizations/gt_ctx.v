Require Import bbv.Word.
Require Import Nat. 
Require Import Bool.
Require Import Coq.NArith.NArith.

Require Import Coq.Logic.FunctionalExtensionality.

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

Require Import FORVES2.tools_types.
Import ToolsTypes.

Require Import FORVES2.context.
Import Context.

Require Import FORVES2.context_facts.
Import ContextFacts.

Require Import List.
Import ListNotations.


Module Opt_gt_ctx.


(* GT(X,Y) = 1   if ctx |- Y<X *)
Definition optimize_gt_ctx_sbinding : opt_smap_value_type := 
fun (val: smap_value) =>
fun (tools: Tools_1.tools_1_t) =>
fun (sb: sbindings) =>
fun (maxid: nat) =>
fun (ctx: ctx_t) =>
fun (ops: stack_op_instr_map) =>
match val with
| SymOp GT [arg1; arg2] => 
  match chk_lt_wrt_ctx ctx arg2 arg1 with
    | false => match chk_le_wrt_ctx ctx arg1 arg2 with
               | false => (val, false)  (* don't know *)
               | true => (SymBasicVal (Val WZero), true) (* arg1 <= arg2 *)
               end
    | true => (SymBasicVal (Val WOne), true)  (* arg1 > arg2 *)
  end
| _ => (val, false)
end.


Lemma optimize_gt_ctx_sbinding_smapv_valid:
opt_smapv_valid_snd optimize_gt_ctx_sbinding.
Proof.
  unfold opt_smapv_valid_snd.
  intros ctx n fcmp sb val val' flag.
  intros Hvalid_smapv_val Hvalid_sb Hoptm_sbinding.
  unfold optimize_gt_ctx_sbinding in Hoptm_sbinding.
  destruct (val) as [basicv|pushtagv|label args|offset smem|key sstrg|
    offset size smem] eqn: eq_val; try inject_rw Hoptm_sbinding eq_val'.
  destruct label eqn: eq_label; try inject_rw Hoptm_sbinding eq_val'.
  (* GT *)
  destruct args as [|arg1 r1] eqn: eq_args; try inject_rw Hoptm_sbinding eq_val'.
  destruct r1 as [|arg2 r2] eqn: eq_r1; try inject_rw Hoptm_sbinding eq_val'.
  destruct r2 as [|arg3 r3] eqn: eq_r2; try inject_rw Hoptm_sbinding eq_val'.
  destruct (chk_lt_wrt_ctx ctx arg2 arg1); 
    try (injection Hoptm_sbinding as eq_val' eq_flag;
    rewrite <- eq_val';
    simpl; intuition).
  destruct (chk_le_wrt_ctx ctx arg1 arg2); 
    try (injection Hoptm_sbinding as eq_val' eq_flag;
    rewrite <- eq_val';
    simpl; intuition).
Qed.

Lemma le_impl_ltb_swap: forall (v1 v2: N),
  (v2 <= v1)%N -> (v1 <? v2)%N = false.
Proof.
  intros v1 v2 Hle.
  unfold N.ltb. 
  destruct (v1 ?= v2)%N eqn: eq_compare; try reflexivity.
  apply N.compare_nge_iff in eq_compare.
  intuition.
Qed.


Lemma optimize_gt_ctx_sbinding_snd:
opt_sbinding_snd optimize_gt_ctx_sbinding.
Proof.
unfold opt_sbinding_snd.
intros val val' tools sb maxidx ctx idx flag Hvalid Hoptm_sbinding.
split.
- (* valid_sbindings *)
  apply valid_bindings_snd_opt with (val:=val)(opt:=optimize_gt_ctx_sbinding)
  (tools:=tools)(flag:=flag)(ctx:=ctx); try assumption.
  apply optimize_gt_ctx_sbinding_smapv_valid.

- (* evaluation is preserved *) 
  intros model mem strg exts v His_model Heval_orig.
  unfold optimize_gt_ctx_sbinding in Hoptm_sbinding.
  pose proof (Hvalid_maxidx maxidx idx val sb evm_stack_opm
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
  destruct (chk_lt_wrt_ctx ctx arg2 arg1) eqn: eq_chk_lt.
    + unfold eval_sstack_val in Heval_orig.
      simpl in Heval_orig.
      rewrite -> PeanoNat.Nat.eqb_refl in Heval_orig.
      rewrite -> evm_stack_opm_GT in Heval_orig.
      rewrite -> length_two in Heval_orig.
      unfold map_option in Heval_orig.
      destruct (eval_sstack_val' maxidx arg1 model mem strg exts idx sb evm_stack_opm)
        as [arg1v|] eqn: eq_eval_arg1; try discriminate.
      destruct (eval_sstack_val' maxidx arg2 model mem strg exts idx sb evm_stack_opm)
        as [arg2v|] eqn: eq_eval_arg2; try discriminate.

      apply chk_lt_wrt_ctx_snd with (model:=model)(mem:=mem)(strg:=strg)
        (exts:=exts)(maxidx:=maxidx)(sb:=sb)(ops:=evm_stack_opm) in eq_chk_lt;
        try assumption.
      destruct eq_chk_lt as [v2 [v1 [Heval_arg2 [Heval_arg1 Hlt]]]].
      unfold eval_sstack_val in Heval_arg1.
      unfold eval_sstack_val in Heval_arg2.
      apply eval_sstack_val'_preserved_when_depth_extended in eq_eval_arg1.
      rewrite -> eval'_maxidx_indep_eq with (m:=maxidx) in eq_eval_arg1.
      apply eval_sstack_val'_preserved_when_depth_extended in eq_eval_arg2.
      rewrite -> eval'_maxidx_indep_eq with (m:=maxidx) in eq_eval_arg2.
      rewrite -> Heval_arg1 in eq_eval_arg1.
      rewrite -> Heval_arg2 in eq_eval_arg2.
      injection eq_eval_arg1 as eq_v1_argv1.
      injection eq_eval_arg2 as eq_v2_argv2.
      rewrite <- eq_v1_argv1 in Heval_orig.
      rewrite <- eq_v2_argv2 in Heval_orig.

      simpl in Heval_orig.
      rewrite <- N.ltb_lt in Hlt.
      rewrite -> Hlt in Heval_orig.
      rewrite <- Heval_orig.
      injection Hoptm_sbinding as eq_val' _.
      rewrite <- eq_val'.
      unfold eval_sstack_val.
      rewrite <- eval_sstack_val'_freshvar.
      rewrite -> eval_sstack_val'_const.
      reflexivity.
    + destruct (chk_le_wrt_ctx ctx arg1 arg2) eqn: eq_chk_le;
        try inject_rw Hoptm_sbinding eq_val'.
      unfold eval_sstack_val in Heval_orig.
      simpl in Heval_orig.
      rewrite -> PeanoNat.Nat.eqb_refl in Heval_orig.
      rewrite -> evm_stack_opm_GT in Heval_orig.
      rewrite -> length_two in Heval_orig.
      unfold map_option in Heval_orig.
      destruct (eval_sstack_val' maxidx arg1 model mem strg exts idx sb evm_stack_opm)
        as [arg1v|] eqn: eq_eval_arg1; try discriminate.
      destruct (eval_sstack_val' maxidx arg2 model mem strg exts idx sb evm_stack_opm)
        as [arg2v|] eqn: eq_eval_arg2; try discriminate.

      apply chk_le_wrt_ctx_snd with (model:=model)(mem:=mem)(strg:=strg)
        (exts:=exts)(maxidx:=maxidx)(sb:=sb)(ops:=evm_stack_opm) in eq_chk_le;
        try assumption.
      destruct eq_chk_le as [v1 [v2 [Heval_arg1 [Heval_arg2 Hle]]]].
      unfold eval_sstack_val in Heval_arg1.
      unfold eval_sstack_val in Heval_arg2.
      apply eval_sstack_val'_preserved_when_depth_extended in eq_eval_arg1.
      rewrite -> eval'_maxidx_indep_eq with (m:=maxidx) in eq_eval_arg1.
      apply eval_sstack_val'_preserved_when_depth_extended in eq_eval_arg2.
      rewrite -> eval'_maxidx_indep_eq with (m:=maxidx) in eq_eval_arg2.
      rewrite -> Heval_arg1 in eq_eval_arg1.
      rewrite -> Heval_arg2 in eq_eval_arg2.
      injection eq_eval_arg1 as eq_v1_argv1.
      injection eq_eval_arg2 as eq_v2_argv2.
      rewrite <- eq_v1_argv1 in Heval_orig.
      rewrite <- eq_v2_argv2 in Heval_orig.

      simpl in Heval_orig.
      apply le_impl_ltb_swap in Hle.
      rewrite -> Hle in Heval_orig.
      rewrite <- Heval_orig.
      injection Hoptm_sbinding as eq_val' _.
      rewrite <- eq_val'.
      unfold eval_sstack_val.
      rewrite <- eval_sstack_val'_freshvar.
      rewrite -> eval_sstack_val'_const.
      reflexivity.
Qed.


End Opt_gt_ctx.
