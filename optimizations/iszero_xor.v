Require Import bbv.Word.
Require Import Nat. 
Require Import Coq.NArith.NArith.
Require Import Coq.Program.Equality.

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


Module Opt_iszero_xor.


Definition is_xor (sv: sstack_val) (fcmp: sstack_val_cmp_t) 
  (maxid : nat) (sb: sbindings) (ops: stack_op_instr_map) :=
match follow_in_smap sv maxid sb with 
| Some (FollowSmapVal (SymOp XOR [arg1; arg2]) idx' sb') => 
      Some [arg1; arg2]
| _ => None
end.



(* ISZERO(XOR(X, Y)) = EQ(X, Y) *)
Definition optimize_iszero_xor_sbinding : opt_smap_value_type := 
fun (val: smap_value) =>
fun (tools: Tools_1.tools_1_t) =>
fun (sb: sbindings) =>
fun (maxid: nat) =>
fun (ctx: ctx_t) =>
fun (ops: stack_op_instr_map) =>
  let fcmp := Tools_1.sstack_val_cmp tools in
  match val with
  | SymOp ISZERO [arg1] => 
      match is_xor arg1 fcmp maxid  sb ops with
      | Some args => (SymOp EQ args, true)
      | _ => (val, false)
      end
  | _ => (val, false)
  end.


Lemma wxor_weqb_true: forall (size: nat) (a b: word size), 
weqb a b = true -> wxor a b = wzero size.
Proof.
intros size a. 
dependent induction a. 
- (* empty word *) reflexivity.
- (* word h++r *)
  intros b0 H.
  unfold weqb in H. 
  destruct (Bool.eqb b (whd b0)) eqn: eqb_b_head; try discriminate.
  fold weqb in H.
  destruct (weqb a (wtl b0)) eqn: eq_weqb_a; try discriminate.
  unfold wxor. simpl.
  apply Bool.eqb_prop in eqb_b_head.
  rewrite -> eqb_b_head. 
  rewrite -> Bool.xorb_nilpotent.
  apply IHa in eq_weqb_a.
  fold wxor.
  rewrite -> eq_weqb_a.
  reflexivity.
Qed.

Lemma diff_bit_xorb_true: forall b1 b2,
b1 <> b2 -> xorb b1 b2 = true.
Proof.
intros b1 b2 H.
destruct b1 eqn: eq_b1.
- destruct b2 eqn: eq_b2; try intuition.
- destruct b2 eqn: eq_b2; try intuition.
Qed.

Lemma tail_word_diff_zero: forall (n: nat) (w: word n),
w <> wzero n -> WS false w <> wzero (S n).
Proof.
intros n w H.
unfold wzero. unfold natToWord. simpl. fold natToWord. fold (wzero n).
apply WS_neq. 
intuition.
Qed.

Lemma wxor_weqb_false: forall (size: nat) (a b: word size), 
weqb a b = false -> wxor a b <> wzero size.
Proof.
intros size a. 
dependent induction a. 
- (* empty word *) 
  intros b0 H.  simpl in H. discriminate.
- (* word h++r *)
  intros b0 H.
  unfold weqb in H. 
  destruct (Bool.eqb b (whd b0)) eqn: eqb_b_head.
  + fold weqb in H.
    destruct (weqb a (wtl b0)) eqn: eq_weqb_a; try discriminate.
    apply IHa in eq_weqb_a.
    unfold wxor. simpl.
    apply Bool.eqb_prop in eqb_b_head.
    rewrite -> eqb_b_head. 
    rewrite -> Bool.xorb_nilpotent.
    fold wxor.
    apply tail_word_diff_zero.
    assumption.
  + rewrite -> Bool.eqb_false_iff in eqb_b_head.
    unfold wxor. simpl.
    apply diff_bit_xorb_true in eqb_b_head.
    rewrite -> eqb_b_head. 
    intuition.
    unfold wzero in H0. 
    unfold natToWord in H0. simpl in H0. fold natToWord in H0.
    injection H0 as contr _.
    intuition.
Qed.

Lemma wzero_def:
WZero = wzero EVMWordSize.
Proof. reflexivity. Qed.

Lemma iszero_xor_eq: forall (ext: externals) (a b: EVMWord), 
evm_iszero ext [evm_xor ext [a; b]] = evm_eq ext [a; b].
Proof.
intros ext a b.
unfold evm_iszero. unfold evm_eq. unfold evm_xor.
destruct (weqb a b) eqn: weqb_a_b.
- apply wxor_weqb_true in weqb_a_b.
  rewrite -> weqb_a_b. reflexivity.
- apply wxor_weqb_false in weqb_a_b. simpl in weqb_a_b.
  apply weqb_ne in weqb_a_b.
  rewrite <- wzero_def in weqb_a_b.
  rewrite -> weqb_a_b.
  reflexivity.
Qed.



Lemma optimize_iszero_xor_sbinding_smapv_valid:
opt_smapv_valid_snd optimize_iszero_xor_sbinding.
Proof.
unfold opt_smapv_valid_snd.
intros ctx n tools sb val val' flag.
intros Hvalid_smapv_val Hvalid Hoptm_sbinding.
unfold optimize_iszero_xor_sbinding in Hoptm_sbinding.
destruct (val) as [basicv|pushtagv|label args|offset smem|key sstrg|
  offset size smem] eqn: eq_val; 
  try inject_rw Hoptm_sbinding eq_val'.
destruct label eqn: eq_label; try try inject_rw Hoptm_sbinding eq_val'.
destruct args as [|arg1 r1]; try inject_rw Hoptm_sbinding eq_val'.
destruct r1 as [|arg2 r2]; try inject_rw Hoptm_sbinding eq_val'.

destruct tools.
unfold Tools_1.sstack_val_cmp in Hoptm_sbinding.
remember sstack_val_cmp as fcmp.
assert(Hsafe_sstack_val_cmp:=H_sstack_val_cmp_snd).

destruct (is_xor arg1 fcmp n  sb evm_stack_opm) as [args|] 
  eqn: is_xor_arg1; try inject_rw Hoptm_sbinding eq_val'.
injection Hoptm_sbinding as eq_val' _.
rewrite <- eq_val'.
unfold is_xor in is_xor_arg1.
destruct (follow_in_smap arg1 n sb) as [fsmv1|] eqn: Hfollow_arg1;
    try discriminate.
destruct fsmv1 as [smv_arg1 idx' sb'].
destruct (smv_arg1) as [_1|_2|label2 args2|_4|_5|_6]; try discriminate.
destruct label2; try discriminate.
destruct args2 as [|xx r2]; try discriminate.
destruct r2 as [|yy r2']; try discriminate.
destruct r2'; try discriminate.
injection is_xor_arg1 as eq_args.
rewrite <- eq_args.

simpl in Hvalid_smapv_val. unfold valid_stack_op_instr in Hvalid_smapv_val.
simpl in Hvalid_smapv_val.
destruct Hvalid_smapv_val as [_ [Hvalid_sstack_arg1 _]].
pose proof (valid_follow_in_smap sb arg1  n evm_stack_opm
  (SymOp XOR [xx; yy]) idx' sb' Hvalid_sstack_arg1 Hvalid Hfollow_arg1) as Himpl.
destruct Himpl as [Hvalid_xor [Hvalid_sb' Himpl]].
pose proof (not_basic_value_smv_symop SUB [xx; yy]) as Hnot_basic.
apply Himpl in Hnot_basic.
unfold valid_smap_value in Hvalid_xor. 
unfold valid_stack_op_instr in Hvalid_xor.
simpl in Hvalid_xor.
destruct Hvalid_xor as [_ [Hvalid_xx [Hvalid_yy _]]].
apply valid_sstack_value_gt with (m:=n) in Hvalid_xx; try assumption.
apply valid_sstack_value_gt with (m:=n) in Hvalid_yy; try assumption.

simpl. unfold valid_stack_op_instr. simpl. 
intuition.
Qed.


Lemma optimize_iszero_xor_sbinding_snd:
opt_sbinding_snd optimize_iszero_xor_sbinding.
Proof.
unfold opt_sbinding_snd.
intros val val' tools sb maxidx ctx idx flag 
  Hvalid Hoptm_sbinding.
split.
- (* valid_sbindings *)
  apply valid_bindings_snd_opt with (val:=val)(opt:=optimize_iszero_xor_sbinding)
    (tools:=tools)(flag:=flag)(ctx:=ctx); try assumption.
  apply optimize_iszero_xor_sbinding_smapv_valid. 

- (* evaluation is preserved *) 
  intros model mem strg ext v Hismodel Heval_orig.
  unfold optimize_iszero_xor_sbinding in Hoptm_sbinding.
  destruct val as [vv|vv|label args|offset smem|key sstrg|offset seze smem]
    eqn: eq_val; try inject_rw Hoptm_sbinding eq_val'.
  (* SymOp label args *)
  destruct label eqn: eq_label; try inject_rw Hoptm_sbinding eq_val'.
  destruct args as [|arg1 r1] eqn: eq_args; 
    try inject_rw Hoptm_sbinding eq_val'.
  destruct r1 as [|arg2 r2]; try inject_rw Hoptm_sbinding eq_val'.

  destruct tools.
  unfold Tools_1.sstack_val_cmp in Hoptm_sbinding.
  remember sstack_val_cmp as fcmp.
  assert(Hsafe_sstack_val_cmp:=H_sstack_val_cmp_snd).

  destruct (is_xor arg1 fcmp idx  sb evm_stack_opm) 
    as [largs|] eqn: is_xor_arg1; try inject_rw Hoptm_sbinding eq_val'.
  
  injection Hoptm_sbinding as eq_val' _.
  rewrite <- eq_val'.
  unfold is_xor in is_xor_arg1.
  destruct (follow_in_smap arg1 idx sb) as [fsmv1|] eqn: Hfollow_arg1;
    try discriminate.
  destruct fsmv1 as [smv_arg1 idx' sb'].
  destruct (smv_arg1) as [_1|_2|label2 args2|_4|_5|_6]; try discriminate.
  destruct label2; try discriminate.
  destruct args2 as [|xx r2]; try discriminate.
  destruct r2 as [|yy r2']; try discriminate.
  destruct r2'; try discriminate.
  injection is_xor_arg1 as eq_largs.
  rewrite <- eq_largs.
      
  unfold eval_sstack_val in Heval_orig. simpl in Heval_orig.
  rewrite -> PeanoNat.Nat.eqb_refl in Heval_orig.
  simpl in Heval_orig.
  destruct (eval_sstack_val' maxidx arg1 model mem strg ext idx sb 
    evm_stack_opm) as [arg1v|] eqn: eval_arg1; try discriminate.
  
  simpl in Hvalid.
  destruct Hvalid as [eq_maxidx' [Hvalid_arg1 Hvalid_sb]].
  unfold valid_stack_op_instr in Hvalid_arg1.
  simpl in Hvalid_arg1.
  destruct Hvalid_arg1 as [_ [Hvalid_arg1 _]].
  pose proof (follow_suffix sb arg1 idx (SymOp XOR [xx; yy]) idx' sb'
    Hfollow_arg1) as [prefix sb_prefix].
  
  (* rewrite <- Heval_orig.  *)
  (*destruct maxidx as [|maxidx'] eqn: eq_maxidx; 
    try (simpl in eval_arg1; discriminate).*)
  rewrite -> eq_maxidx' in eval_arg1.
  simpl in eval_arg1.
  rewrite -> Hfollow_arg1 in eval_arg1.
  simpl in eval_arg1.
  destruct (eval_sstack_val' idx xx model mem strg ext idx' sb' 
    evm_stack_opm) as [xxv|] eqn: eval_xx_sb'; try discriminate.
  destruct (eval_sstack_val' idx yy model mem strg ext idx' sb' 
    evm_stack_opm) as [yyv|] eqn: eval_yy_sb'; try discriminate.
  unfold eval_sstack_val in eval_arg1. simpl.
  
  unfold eval_sstack_val. 
  rewrite -> eval_sstack_val'_one_step.
  rewrite -> follow_in_smap_head_op.
  rewrite -> evm_stack_opm_EQ.
  rewrite -> length_two.
  unfold map_option.
  simpl.
  
  rewrite -> eval'_maxidx_indep_eq with (m:=idx) in eval_xx_sb'.
  pose proof (eval_sstack_val'_extend_sb  idx model mem strg
    ext idx sb sb' evm_stack_opm prefix Hvalid_sb sb_prefix xx xxv
    eval_xx_sb') as eval_x_sb.
  apply eval_sstack_val'_preserved_when_depth_extended in eval_x_sb.
  rewrite <- eq_maxidx' in eval_x_sb.
  rewrite -> eval_x_sb. 
  
  rewrite -> eval'_maxidx_indep_eq with (m:=idx) in eval_yy_sb'.
  pose proof (eval_sstack_val'_extend_sb  idx model mem strg
    ext idx sb sb' evm_stack_opm prefix Hvalid_sb sb_prefix yy yyv
    eval_yy_sb') as eval_y_sb.
  apply eval_sstack_val'_preserved_when_depth_extended in eval_y_sb.
  rewrite <- eq_maxidx' in eval_y_sb.
  rewrite -> eval_y_sb.
  
  injection eval_arg1 as eq_arg1v.
  rewrite <- eq_arg1v in Heval_orig.
  rewrite <- Heval_orig.
  rewrite <- iszero_xor_eq. unfold evm_xor.
  reflexivity.
Qed.


End Opt_iszero_xor.
