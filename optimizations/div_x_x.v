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

Require Import FORVES2.context_facts.
Import ContextFacts.

Require Import FORVES2.tools_types.
Import ToolsTypes.

Require Import List.
Import ListNotations.

(*
From ReductionEffect Require Import PrintingEffect.
From Coq Require Import Strings.String.
*)


Module Opt_div_x_x.


Definition val_diff_zero (arg: sstack_val) (maxid: nat) (sb: sbindings) 
  (ctx: ctx_t) : bool :=
match chk_neq_wrt_ctx ctx arg (Val WZero) with
| true => true
| false => match follow_in_smap arg maxid sb with
          | Some (FollowSmapVal (SymBasicVal (Val v)) _ _) => 
               negb (weqb v WZero)
          | _ => false
          end
end.


Definition eq_and_diff_zero (arg1 arg2: sstack_val) (fcmp: sstack_val_cmp_t) 
  (maxid: nat) (sb: sbindings) (ops: stack_op_instr_map) 
  (ctx: ctx_t)
  : bool :=
match fcmp ctx arg1 arg2 maxid sb maxid sb ops with
| true => val_diff_zero arg2 maxid sb ctx
| false => false
end.


(* DIV(X,X) = 1   if x <> 0*)
Definition optimize_div_x_x_sbinding : opt_smap_value_type := 
fun (val: smap_value) =>
fun (tools: Tools_1.tools_1_t) =>
fun (sb: sbindings) =>
fun (maxid: nat) =>
fun (ctx: ctx_t) =>
fun (ops: stack_op_instr_map) =>
  let fcmp := Tools_1.sstack_val_cmp tools in
  match val with
  | SymOp DIV [arg1; arg2] => 
      if (eq_and_diff_zero arg1 arg2 fcmp maxid sb ops ctx)
      then
        (SymBasicVal (Val WOne), true)
      else
        (val, false)
  | _ => (val, false)
  end.


Lemma optimize_div_x_x_sbinding_smapv_valid:
opt_smapv_valid_snd optimize_div_x_x_sbinding.
Proof.
unfold opt_smapv_valid_snd.
intros ctx n tools sb val val' flag.
intros Hvalid_smapv_val Hvalid_sb Hoptm_sbinding.
unfold optimize_div_x_x_sbinding in Hoptm_sbinding.
destruct (val) as [basicv|pushtagv|label args|offset smem|key sstrg|
  offset size smem] eqn: eq_val; try inject_rw Hoptm_sbinding eq_val'.
destruct label eqn: eq_label; try inject_rw Hoptm_sbinding eq_val'.
(* DIV *)
destruct args as [|arg1 r1] eqn: eq_args; try inject_rw Hoptm_sbinding eq_val'.
destruct r1 as [|arg2 r2] eqn: eq_r1; try inject_rw Hoptm_sbinding eq_val'.
destruct r2 as [|arg3 r3] eqn: eq_r2; try inject_rw Hoptm_sbinding eq_val'.

destruct tools.
unfold Tools_1.sstack_val_cmp in Hoptm_sbinding.
remember sstack_val_cmp as fcmp.
assert(Hsafe_sstack_val_cmp:=H_sstack_val_cmp_snd).

destruct (eq_and_diff_zero arg1 arg2 fcmp n sb  evm_stack_opm); 
    try inject_rw Hoptm_sbinding eq_val'.
injection Hoptm_sbinding as eq_val' eq_flag.
rewrite <- eq_val'.
simpl. intuition.
Qed.



Lemma evm_div_x_x: forall ctx (x: EVMWord), 
weqb x WZero = false ->
evm_div ctx [x; x] = WOne.
Proof.
intros. simpl.
apply weqb_false in H.
unfold wdiv. unfold wordBin.
apply wordToN_neq_0 in H.
rewrite -> N.div_same; try assumption.
reflexivity.
Qed.


Lemma optimize_div_x_x_sbinding_snd:
opt_sbinding_snd optimize_div_x_x_sbinding.
Proof.
unfold opt_sbinding_snd.
intros val val' tools sb maxidx ctx idx flag
  Hvalid Hoptm_sbinding.
split.
- (* valid_sbindings *)
  apply valid_bindings_snd_opt with (val:=val)(opt:=optimize_div_x_x_sbinding)
    (tools:=tools)(flag:=flag)(ctx:=ctx); try assumption.
  apply optimize_div_x_x_sbinding_smapv_valid. 
    
- (* evaluation is preserved *) 
  intros model mem strg ext v Hismodel Heval_orig.
  unfold optimize_div_x_x_sbinding in Hoptm_sbinding.
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

  destruct tools.
  unfold Tools_1.sstack_val_cmp in Hoptm_sbinding.
  remember sstack_val_cmp as fcmp.
  assert(Hsafe_sstack_val_cmp:=H_sstack_val_cmp_snd).

  destruct (eq_and_diff_zero arg1 arg2 fcmp idx sb  evm_stack_opm) 
    eqn: fcmp_arg1_arg2; try inject_rw Hoptm_sbinding eq_val'.
  (* arg1 ~ arg2  /\  arg2 <> WZero *)
  unfold eq_and_diff_zero in fcmp_arg1_arg2.
  destruct (fcmp ctx arg1 arg2 idx sb idx sb  evm_stack_opm) 
    eqn: eq_fcmp_arg1_arg2; try discriminate.
  assert(eq_fcmp_arg1_arg2_bak:=eq_fcmp_arg1_arg2).
  unfold val_diff_zero in fcmp_arg1_arg2.
  destruct (chk_neq_wrt_ctx ctx arg2 (Val WZero)) eqn: eq_chk_neq.
  + (* chk_neq = true *)
    apply chk_neq_wrt_ctx_snd with (model:=model)(mem:=mem)(strg:=strg) 
      (exts:=ext)(maxidx:=maxidx)(sb:=sb)(ops:=evm_stack_opm) in eq_chk_neq;
      try assumption.
    destruct eq_chk_neq as [v2 [vzero [Heval_arg2 [Heval_zero Hweqb]]]].
    rewrite -> eval_sstack_val_const in Heval_zero.
    injection Heval_zero as eq_v2_zero.
    rewrite <- eq_v2_zero in Hweqb.

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
      Hvalid_bindings_sb eq_fcmp_arg1_arg2_bak model mem strg ext Hismodel)
      as [vv [Heval_arg1' Heval_arg2']].
    unfold eval_sstack_val in Heval_arg1'.
    unfold eval_sstack_val in Heval_arg2'.
    rewrite -> eq_maxidx_idx in Heval_arg1'.
    rewrite -> eq_maxidx_idx in Heval_arg2'.
    rewrite -> Heval_arg1' in eval_arg1.
    rewrite -> Heval_arg2' in eval_arg2.
    injection eval_arg1 as eq_varg1.
    injection eval_arg2 as eq_varg2.
    rewrite <- eq_varg1 in Heval_orig.
    rewrite <- eq_varg2 in Heval_orig.
    unfold eval_sstack_val in Heval_arg2.
    apply eval_sstack_val'_preserved_when_depth_extended in Heval_arg2'.
    rewrite -> eval'_maxidx_indep_eq with (m:=maxidx) in Heval_arg2'.
    rewrite -> Heval_arg2' in Heval_arg2.
    injection Heval_arg2 as eq_vv_v2.
    rewrite <- eq_vv_v2 in Hweqb.

    injection Hoptm_sbinding as eq_val' _. 
    rewrite <- eq_val'.
    unfold eval_sstack_val.
    simpl.
    rewrite -> PeanoNat.Nat.eqb_refl.
    apply evm_div_x_x with (ctx:=ext) in Hweqb.
    rewrite -> Hweqb in Heval_orig.
    assumption.
  + destruct (follow_in_smap arg2 idx sb) as [fsmv|] eqn: eq_follow_arg2; 
      try discriminate.
  destruct fsmv as [smv key sb']; try discriminate. 
  destruct smv as [val_arg2|_2|_3|_4|_5|_6]; try discriminate.
  destruct val_arg2 as [varg2'|_2|_3]; try discriminate.
  destruct (weqb varg2' WZero) eqn: eq_weqb_varg2'_WZero; try discriminate.
  
  injection Hoptm_sbinding as eq_val' _. 
  rewrite <- eq_val'.
  unfold eval_sstack_val. simpl.
  rewrite -> PeanoNat.Nat.eqb_refl.

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

  pose proof (valid_sstack_value_const  idx v) as Hvalid_v.
  pose proof (Hsafe_sstack_val_cmp ctx arg1 arg2 idx sb idx sb 
     evm_stack_opm Hvalid_arg1 Hvalid_arg2 Hvalid_bindings_sb
    Hvalid_bindings_sb eq_fcmp_arg1_arg2 model mem strg ext Hismodel)
    as [vv [Heval_arg1 Heval_arg2]].

  unfold eval_sstack_val in Heval_arg1.
  unfold eval_sstack_val in Heval_arg2.
  rewrite -> eq_maxidx_idx in Heval_arg1.
  rewrite -> eq_maxidx_idx in Heval_arg2.
  rewrite -> Heval_arg1 in eval_arg1.
  injection eval_arg1 as eq_arg1_vv.
  rewrite -> Heval_arg2 in eval_arg2.
  injection eval_arg2 as eq_arg2_vv.
  rewrite <- eq_arg1_vv in Heval_orig.
  rewrite <- eq_arg2_vv in Heval_orig.
  
  rewrite <- eq_maxidx_idx in Heval_arg2. simpl in Heval_arg2.
  rewrite -> eq_follow_arg2 in Heval_arg2.
  injection Heval_arg2 as eq_varg2'_vv.
  rewrite -> eq_varg2'_vv in eq_weqb_varg2'_WZero.
  
  rewrite evm_div_x_x in Heval_orig; try assumption.
Qed.


End Opt_div_x_x.
