Require Import bbv.Word.
Require Import Nat. 
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

Require Import List.
Import ListNotations.


Module Opt_jumpi_eval.


Definition val_diff_zero (arg: sstack_val) (fcmp: sstack_val_cmp_t) 
  (maxid: nat) (sb: sbindings) (ctx: ctx_t) (ops: stack_op_instr_map) 
  : bool :=
match follow_in_smap arg maxid sb with
  | Some (FollowSmapVal (SymBasicVal (Val v)) _ _) => 
      negb (weqb v WZero)
  | _ => false
  end.


(* JUMPI(Dest,B) = Dest if B is constant and B <> 0 *)
Definition optimize_jumpi_eval_sbinding : opt_smap_value_type := 
fun (val: smap_value) =>
fun (tools: Tools_1.tools_1_t) =>
fun (sb: sbindings) =>
fun (maxid: nat) =>
fun (ctx: ctx_t) =>
fun (ops: stack_op_instr_map) =>
  let fcmp := Tools_1.sstack_val_cmp tools in
  match val with
  | SymOp JUMPI [arg1; arg2] => 
      if val_diff_zero arg2 fcmp maxid sb ctx ops then
        (SymBasicVal arg1, true)
      else
        (val, false)
  | _ => (val, false)
  end.


Lemma optimize_jumpi_eval_sbinding_smapv_valid:
opt_smapv_valid_snd optimize_jumpi_eval_sbinding.
Proof.
unfold opt_smapv_valid_snd.
intros ctx n tools sb val val' flag.
intros Hvalid_smapv_val Hvalid_sb Hoptm_sbinding.
unfold optimize_jumpi_eval_sbinding in Hoptm_sbinding.
destruct (val) as [basicv|pushtagv|label args|offset smem|key sstrg|
  offset size smem] eqn: eq_val; 
   try inject_rw Hoptm_sbinding eq_val'.
destruct label eqn: eq_label; try inject_rw Hoptm_sbinding eq_val'. try 
(* JUMPI *)
destruct args as [|arg1 r1] eqn: eq_args; try inject_rw Hoptm_sbinding eq_val'.
destruct r1 as [|arg2 r2] eqn: eq_r1; try inject_rw Hoptm_sbinding eq_val'.
destruct r2 as [|arg3 r3] eqn: eq_r2; try inject_rw Hoptm_sbinding eq_val'.

destruct tools.
unfold Tools_1.sstack_val_cmp in Hoptm_sbinding.
remember sstack_val_cmp as fcmp.
assert(Hsafe_sstack_val_cmp:=H_sstack_val_cmp_snd).

destruct (val_diff_zero arg2 fcmp n sb ctx evm_stack_opm)
  eqn: eq_val_diff_zero_arg1.
* injection Hoptm_sbinding as eq_val' eq_flag.
  rewrite <- eq_val'.
  simpl in Hvalid_smapv_val. unfold valid_stack_op_instr in Hvalid_smapv_val.
  simpl in Hvalid_smapv_val.
  destruct Hvalid_smapv_val as [_ [Hvalid_arg1 [Hvalid_arg2 _]]].
  simpl.
  assumption.
* injection Hoptm_sbinding as eq_val' eq_flag.
  rewrite <- eq_val'.
  assumption.
Qed.



Lemma evm_jumpi_not_zero: forall exts a b,
weqb b WZero = false ->
evm_jumpi exts [a; b] = a.
Proof.
intros exts a b Hb_not_z. simpl.
rewrite -> Hb_not_z.
reflexivity.
Qed.


Lemma optimize_jumpi_eval_sbinding_snd:
opt_sbinding_snd optimize_jumpi_eval_sbinding.
Proof.
unfold opt_sbinding_snd.
intros val val' tools sb maxidx ctx idx flag 
  Hvalid Hoptm_sbinding.
split.
- (* valid_sbindings *)
  apply valid_bindings_snd_opt with (val:=val)(opt:=optimize_jumpi_eval_sbinding)
    (tools:=tools)(flag:=flag)(ctx:=ctx); try assumption.
  apply optimize_jumpi_eval_sbinding_smapv_valid. 
    
- (* evaluation is preserved *) 
  intros model mem strg exts v His_model Heval_orig.
  unfold optimize_jumpi_eval_sbinding in Hoptm_sbinding.
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

  destruct (val_diff_zero arg2 fcmp idx sb ctx evm_stack_opm) 
    eqn: eq_val_diff_z_arg2.
  + (* arg2  <> WZero *)
    injection Hoptm_sbinding as eq_val' _. 
    rewrite <- eq_val'.
    unfold eval_sstack_val in Heval_orig. simpl in Heval_orig.
    rewrite -> PeanoNat.Nat.eqb_refl in Heval_orig.
    simpl in Heval_orig.
    destruct (eval_sstack_val' maxidx arg1 model mem strg exts idx sb evm_stack_opm)
      as [varg1|] eqn: eval_arg1; try discriminate.
    destruct (eval_sstack_val' maxidx arg2 model mem strg exts idx sb evm_stack_opm)
      as [varg2|] eqn: eval_arg2; try discriminate.
    unfold safe_sstack_val_cmp in Hsafe_sstack_val_cmp.

    unfold valid_bindings in Hvalid.
    destruct Hvalid as [eq_maxid [Hvalid_smap_value Hvalid_bindings_sb]].
    unfold valid_smap_value in Hvalid_smap_value.
    unfold valid_stack_op_instr in Hvalid_smap_value.
    simpl in Hvalid_smap_value.
    destruct (Hvalid_smap_value) as [_ [Hvalid_arg1 [Hvalid_arg2 _ ]]].
    fold valid_bindings in Hvalid_bindings_sb.

    unfold val_diff_zero in eq_val_diff_z_arg2. 
    destruct (follow_in_smap arg2 idx sb) as [fsmv|] eqn: eq_follow_arg2; try discriminate.
    destruct fsmv as [svm] eqn: eq_fsmv.
    destruct svm as [val2|pushtagv|label args'|offset smem|key' sstrg|
    offset size smem] eqn: eq_svm; try discriminate.
    destruct val2 as [v2|_a|_b] eqn: eq_val2; try discriminate.
    rewrite -> Bool.negb_true_iff in  eq_val_diff_z_arg2.

    rewrite -> eq_maxid in eval_arg2.
    simpl in eval_arg2.
    rewrite -> eq_follow_arg2 in eval_arg2.
    injection eval_arg2 as eq_varg2_v2.
    rewrite <- eq_varg2_v2 in Heval_orig.
    pose proof (evm_jumpi_not_zero exts varg1 v2 eq_val_diff_z_arg2) as Hjumpi.
    simpl in Hjumpi. injection Heval_orig as Heval_orig.
    rewrite -> Hjumpi in Heval_orig.
    rewrite <- Heval_orig.
    
    unfold eval_sstack_val.
    rewrite <- eval_sstack_val'_freshvar.
    apply eval_sstack_val'_preserved_when_depth_extended.
    rewrite -> eval'_maxidx_indep_eq with (m:=idx).
    assumption.
  + (* arg2 = WZero *)
    injection Hoptm_sbinding as eq_val' _.
    rewrite <- eq_val'.
    assumption.
Qed.

End Opt_jumpi_eval.
