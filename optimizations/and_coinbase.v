Require Import bbv.Word.
Require Import Nat. 
Require Import Coq.NArith.NArith.
Require Import Coq.Bool.Bool.


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


Module Opt_and_coinbase.


Definition is_coinbase_mask (sv1 sv2: sstack_val) (fcmp: sstack_val_cmp_t) 
  (maxid : nat) (sb: sbindings) (ops: stack_op_instr_map) 
  (ctx: ctx_t) : bool :=
match follow_in_smap sv1 maxid sb with 
| Some (FollowSmapVal (SymOp COINBASE []) idx' sb') => 
    fcmp ctx sv2 (Val two_exp_160_minus_1) maxid sb maxid sb  ops
| _ => false
end.



(* AND(COINBASE,2^160-1) = COINBASE
   AND(2^160-1,COINBASE) = COINBASE *)
Definition optimize_and_coinbase_sbinding : opt_smap_value_type := 
fun (val: smap_value) =>
fun (tools: Tools_1.tools_1_t) =>
fun (sb: sbindings) =>
fun (maxid: nat) =>
fun (ctx: ctx_t) =>
fun (ops: stack_op_instr_map) =>
  let fcmp := Tools_1.sstack_val_cmp tools in
  match val with
  | SymOp AND [arg1;arg2] => 
      if is_coinbase_mask arg1 arg2 fcmp maxid sb ops ctx ||
           is_coinbase_mask arg2 arg1 fcmp maxid sb ops ctx 
      then (SymOp COINBASE [], true)
      else (val, false)
  | _ => (val, false)
  end.


Lemma optimize_and_coinbase_sbinding_smapv_valid:
opt_smapv_valid_snd optimize_and_coinbase_sbinding.
Proof.
unfold opt_smapv_valid_snd.
intros ctx n tools sb val val' flag.
intros Hvalid_smapv_val Hvalid Hoptm_sbinding.
unfold optimize_and_coinbase_sbinding in Hoptm_sbinding.
destruct (val) as [basicv|pushtagv|label args|offset smem|key sstrg|
  offset size smem] eqn: eq_val; 
  try inject_rw Hoptm_sbinding eq_val'.
destruct label eqn: eq_label; try try inject_rw Hoptm_sbinding eq_val'.
destruct args as [|arg1 r1]; try inject_rw Hoptm_sbinding eq_val'.
destruct r1 as [|arg2 r2]; try inject_rw Hoptm_sbinding eq_val'.
destruct r2; try inject_rw Hoptm_sbinding eq_val'.

destruct tools.
simpl in Hoptm_sbinding.
remember sstack_val_cmp as fcmp.
assert(Hsafe_sstack_val_cmp:=H_sstack_val_cmp_snd).

destruct (is_coinbase_mask arg1 arg2 fcmp n sb evm_stack_opm ctx || 
          is_coinbase_mask arg2 arg1 fcmp n sb evm_stack_opm ctx) 
  eqn: is_coinbase; try inject_rw Hoptm_sbinding eq_val'.
unfold orb in is_coinbase.

unfold valid_smap_value in Hvalid_smapv_val.
unfold valid_stack_op_instr in Hvalid_smapv_val.
simpl in Hvalid_smapv_val. 
destruct Hvalid_smapv_val as [Hlen_and Hvalid_arg1_arg2].
simpl in Hvalid_arg1_arg2.
destruct Hvalid_arg1_arg2 as [Hvalid_arg1 [Hvalid_arg2 _]].

destruct (is_coinbase_mask arg1 arg2 fcmp n  sb evm_stack_opm) 
  eqn: is_coinbase_arg1_arg2.
- injection Hoptm_sbinding as eq_val' _.
  rewrite <- eq_val'. 
  unfold is_coinbase_mask in is_coinbase_arg1_arg2.
  destruct (follow_in_smap arg1 n sb) as [fsmv1|] eqn: eq_follow_arg1; 
    try discriminate.
  destruct fsmv1 as [smv_arg1 idx1' sb1'] eqn: eq_fsmv_arg1.
  destruct (smv_arg1) as [_1|_2|label2 args2|_4|_5|_6]; try discriminate.
  destruct label2; try discriminate.
  destruct args2; try discriminate.
  pose proof (valid_follow_in_smap sb arg1  n evm_stack_opm 
    (SymOp COINBASE []) idx1' sb1' Hvalid_arg1 Hvalid eq_follow_arg1)
    as Hvalid2.
  destruct Hvalid2 as [Hvalid_smpv [_ Himpl]].
  pose proof (not_basic_value_smv_symop COINBASE []) as eq_not_basic.
  apply Himpl in eq_not_basic as n_gt_idx1'.
  apply gt_add in n_gt_idx1'. destruct n_gt_idx1' as [k n_gt_idx1'].
  rewrite -> n_gt_idx1'.
  apply valid_smap_value_incr with (m:=k) in Hvalid_smpv.
  assumption.
  
- destruct (is_coinbase_mask arg2 arg1 fcmp n  sb evm_stack_opm) 
  eqn: is_coinbase_arg2_arg1; try discriminate.
  injection Hoptm_sbinding as eq_val' _.
  rewrite <- eq_val'. 
  unfold is_coinbase_mask in is_coinbase_arg2_arg1.
  destruct (follow_in_smap arg2 n sb) as [fsmv2|] eqn: eq_follow_arg2; 
    try discriminate.
  destruct fsmv2 as [smv_arg2 idx2' sb2'] eqn: eq_fsmv_arg2.
  destruct (smv_arg2) as [_1|_2|label2 args2|_4|_5|_6]; try discriminate.
  destruct label2; try discriminate.
  destruct args2; try discriminate.
  pose proof (valid_follow_in_smap sb arg2  n evm_stack_opm 
    (SymOp COINBASE []) idx2' sb2' Hvalid_arg2 Hvalid eq_follow_arg2)
    as Hvalid2.
  destruct Hvalid2 as [Hvalid_smpv [_ Himpl]].
  pose proof (not_basic_value_smv_symop COINBASE []) as eq_not_basic.
  apply Himpl in eq_not_basic as n_gt_idx2'.
  apply gt_add in n_gt_idx2'. destruct n_gt_idx2' as [k n_gt_idx2'].
  rewrite -> n_gt_idx2'.
  apply valid_smap_value_incr with (m:=k) in Hvalid_smpv.
  assumption.
Qed.


Lemma optimize_and_coinbase_sbinding_snd:
opt_sbinding_snd optimize_and_coinbase_sbinding.
Proof.
unfold opt_sbinding_snd.
intros val val' tools sb maxidx ctx idx flag 
  Hvalid Hoptm_sbinding.
split.
- (* valid_sbindings *)
  apply valid_bindings_snd_opt with (val:=val)(opt:=optimize_and_coinbase_sbinding)
    (tools:=tools)(flag:=flag)(ctx:=ctx); try assumption.
  apply optimize_and_coinbase_sbinding_smapv_valid. 

- (* evaluation is preserved *) 
  intros model mem strg ext v Hismodel Heval_orig.
  unfold optimize_and_coinbase_sbinding in Hoptm_sbinding.
  destruct val as [vv|vv|label args|offset smem|key sstrg|offset seze smem]
    eqn: eq_val; try inject_rw Hoptm_sbinding eq_val'.
  (* SymOp label args *)
  destruct label eqn: eq_label; try inject_rw Hoptm_sbinding eq_val'.
  destruct args as [|arg1 r1] eqn: eq_args; 
    try inject_rw Hoptm_sbinding eq_val'.
  destruct r1 as [|arg2 r2]; try inject_rw Hoptm_sbinding eq_val'.
  destruct r2; try inject_rw Hoptm_sbinding eq_val'.

  destruct tools.
  simpl in Hoptm_sbinding.
  remember sstack_val_cmp as fcmp.
  assert(Hsafe_sstack_val_cmp:=H_sstack_val_cmp_snd).

  destruct (is_coinbase_mask arg1 arg2 fcmp idx  sb evm_stack_opm ctx
         || is_coinbase_mask arg2 arg1 fcmp idx  sb evm_stack_opm ctx )
    eqn: eq_is_coinbase; try inject_rw Hoptm_sbinding eq_val'.
  unfold orb in eq_is_coinbase.
  destruct (is_coinbase_mask arg1 arg2 fcmp idx  sb evm_stack_opm)
    eqn: is_coinbase_arg1_arg2.
  + unfold is_coinbase_mask in is_coinbase_arg1_arg2.
    destruct (follow_in_smap arg1 idx sb) as [fsmv|] eqn: eq_follow_arg1;
      try discriminate.
    destruct fsmv as [smv idx' sb'] eqn: eq_fsmv.
    destruct smv as [_1|_2|label2 args2|_4|_5|_6] eqn: eq_smv;
      try discriminate.
    destruct label2 eqn: eq_label2; try discriminate.
    destruct args2 as [|arg11 r21]; try discriminate.
    
    injection Hoptm_sbinding as eq_val' _.
    rewrite <- eq_val'.
    
    unfold eval_sstack_val in Heval_orig.
    simpl in Heval_orig.
    rewrite -> PeanoNat.Nat.eqb_refl in Heval_orig.
    simpl in Heval_orig.
    destruct (eval_sstack_val' maxidx arg1 model mem strg ext idx sb 
      evm_stack_opm) as [arg1v|] eqn: eq_eval_arg1; try discriminate.
    destruct (eval_sstack_val' maxidx arg2 model mem strg ext idx sb
      evm_stack_opm) as [arg2v|] eqn: eq_eval_arg2; try discriminate.
    injection Heval_orig as eq_v. rewrite <- eq_v.
    
    unfold eval_sstack_val. simpl.
    rewrite -> PeanoNat.Nat.eqb_refl. simpl.
    unfold evm_coinbase.
    unfold eval_sstack_val' in eq_eval_arg1.
    destruct maxidx as [|maxidx'] eqn: eq_maxidx; try discriminate.
    rewrite -> eq_follow_arg1 in eq_eval_arg1. simpl in eq_eval_arg1.
    injection eq_eval_arg1 as eq_arg1v. 
    rewrite <- eq_arg1v. unfold evm_coinbase.
    
    unfold safe_sstack_val_cmp in Hsafe_sstack_val_cmp.
    pose proof (valid_sstack_value_const  idx two_exp_160_minus_1)
      as valid_sstack_two_exp_160_minus_1.
    simpl in Hvalid.
    destruct Hvalid as [eq_idx [Hvalid_stack_op Hvalid_sb]].
    unfold valid_stack_op_instr in Hvalid_stack_op.
    simpl in Hvalid_stack_op.
    destruct Hvalid_stack_op as [_ [Hvalid_arg1 [Hvalid_arg2 _]]].

    pose proof (Hsafe_sstack_val_cmp ctx arg2 (Val two_exp_160_minus_1) idx sb
      idx sb  evm_stack_opm Hvalid_arg2 
      valid_sstack_two_exp_160_minus_1 Hvalid_sb Hvalid_sb is_coinbase_arg1_arg2
      model mem strg ext Hismodel) as eval_arg2_two_exp.
    destruct eval_arg2_two_exp as [vv [eval_arg2_vv eval_two_exp_vv]].
    unfold eval_sstack_val in eval_arg2_vv.
    unfold eval_sstack_val in eval_two_exp_vv.
    rewrite -> eq_idx in eq_eval_arg2.
    rewrite -> eval_sstack_val'_const in eval_two_exp_vv.
    rewrite -> eq_eval_arg2 in eval_arg2_vv.
    rewrite <- eval_arg2_vv in eval_two_exp_vv.
    injection eval_two_exp_vv as eq_vv.
    rewrite <- eq_vv.
    
    unfold two_exp_160_minus_1.
    rewrite <- masking_address_extension_word.
    reflexivity. 

  + unfold is_coinbase_mask in eq_is_coinbase.
    destruct (follow_in_smap arg2 idx sb) as [fsmv|] eqn: eq_follow_arg2;
      try discriminate.
    destruct fsmv as [smv idx' sb'] eqn: eq_fsmv.
    destruct smv as [_1|_2|label2 args2|_4|_5|_6] eqn: eq_smv;
      try discriminate.
    destruct label2 eqn: eq_label2; try discriminate.
    destruct args2 as [|arg11 r21]; try discriminate.
    
    injection Hoptm_sbinding as eq_val' _.
    rewrite <- eq_val'.
    
    unfold eval_sstack_val in Heval_orig.
    simpl in Heval_orig.
    rewrite -> PeanoNat.Nat.eqb_refl in Heval_orig.
    simpl in Heval_orig.
    destruct (eval_sstack_val' maxidx arg1 model mem strg ext idx sb 
      evm_stack_opm) as [arg1v|] eqn: eq_eval_arg1; try discriminate.
    destruct (eval_sstack_val' maxidx arg2 model mem strg ext idx sb
      evm_stack_opm) as [arg2v|] eqn: eq_eval_arg2; try discriminate.
    injection Heval_orig as eq_v. rewrite <- eq_v.
    
    unfold eval_sstack_val. simpl.
    rewrite -> PeanoNat.Nat.eqb_refl. simpl.
    unfold evm_coinbase.
    unfold eval_sstack_val' in eq_eval_arg2.
    destruct maxidx as [|maxidx'] eqn: eq_maxidx; try discriminate.
    rewrite -> eq_follow_arg2 in eq_eval_arg2. simpl in eq_eval_arg2.
    injection eq_eval_arg2 as eq_arg2v. 
    rewrite <- eq_arg2v. unfold evm_coinbase.
    
    unfold safe_sstack_val_cmp in Hsafe_sstack_val_cmp.
    pose proof (valid_sstack_value_const  idx two_exp_160_minus_1)
      as valid_sstack_two_exp_160_minus_1.
    simpl in Hvalid.
    destruct Hvalid as [eq_idx [Hvalid_stack_op Hvalid_sb]].
    unfold valid_stack_op_instr in Hvalid_stack_op.
    simpl in Hvalid_stack_op.
    destruct Hvalid_stack_op as [_ [Hvalid_arg1 [Hvalid_arg2 _]]].

    pose proof (Hsafe_sstack_val_cmp ctx arg1 (Val two_exp_160_minus_1) idx sb
      idx sb  evm_stack_opm Hvalid_arg1 
      valid_sstack_two_exp_160_minus_1 Hvalid_sb Hvalid_sb eq_is_coinbase
      model mem strg ext Hismodel) as eval_arg1_two_exp.
    destruct eval_arg1_two_exp as [vv [eval_arg1_vv eval_two_exp_vv]].
    unfold eval_sstack_val in eval_arg1_vv.
    unfold eval_sstack_val in eval_two_exp_vv.
    rewrite -> eq_idx in eq_eval_arg1.
    rewrite -> eval_sstack_val'_const in eval_two_exp_vv.
    rewrite -> eq_eval_arg1 in eval_arg1_vv.
    rewrite <- eval_arg1_vv in eval_two_exp_vv.
    injection eval_two_exp_vv as eq_vv.
    rewrite <- eq_vv.
    
    unfold two_exp_160_minus_1.
    rewrite -> wand_comm.
    rewrite <- masking_address_extension_word.
    reflexivity.
Qed.


End Opt_and_coinbase.
