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

Require Import FORVES2.tools_types.
Import ToolsTypes.

Require Import List.
Import ListNotations.


Module Opt_balance_address.


(* BALANCE(ADDRESS) = SELFBALANCE *)
Definition optimize_balance_address_sbinding : opt_smap_value_type := 
fun (val: smap_value) =>
fun (tools: Tools_1.tools_1_t) =>
fun (sb: sbindings) =>
fun (maxid: nat) =>
fun (ctx: ctx_t) =>
fun (ops: stack_op_instr_map) =>
  let fcmp := Tools_1.sstack_val_cmp tools in
  match val with
  | SymOp BALANCE [arg1] => 
      match follow_in_smap arg1 maxid sb with 
      | Some (FollowSmapVal (SymOp ADDRESS []) idx' sb') => 
          (SymOp SELFBALANCE [], true)
      | _ => (val, false)
      end
  | _ => (val, false)
  end.



Lemma optimize_balance_address_sbinding_smapv_valid:
opt_smapv_valid_snd optimize_balance_address_sbinding.
Proof.
unfold opt_smapv_valid_snd.
intros ctx n tools sb val val' flag.
intros smapv_val Hvalid_sb Hoptm_sbinding.
unfold optimize_balance_address_sbinding in Hoptm_sbinding.
destruct (val) as [basicv|pushtagv|label args|offset smem|key sstrg|
  offset size smem] eqn: eq_val; try inject_rw Hoptm_sbinding eq_val'.
destruct label eqn: eq_label; try inject_rw Hoptm_sbinding eq_val'.
(* BALANCE *)
destruct args as [|arg1 r1] eqn: eq_args; try 
  (injection Hoptm_sbinding as eq_val' eq_flag;
  rewrite <- eq_val'; assumption).
destruct r1 as [|arg2 r2]; try inject_rw Hoptm_sbinding eq_val'.
destruct (follow_in_smap arg1 n sb) as [fsmv_arg1|] eqn: eq_follow_arg1;
  try inject_rw Hoptm_sbinding eq_val'.
destruct fsmv_arg1 as [smv_arg1 idx' sb'].
destruct smv_arg1 as [x1|x2|label1 args1|x4|x5|x6]; 
  try inject_rw Hoptm_sbinding eq_val'.
destruct label1; try inject_rw Hoptm_sbinding eq_val'.
destruct args1;  try inject_rw Hoptm_sbinding eq_val'.

injection Hoptm_sbinding as eq_val' eq_flag.
rewrite <- eq_val'.
unfold valid_smap_value.
unfold valid_stack_op_instr.
simpl.
intuition.
Qed.


Lemma balance_address: forall ctx,
evm_balance ctx [evm_address ctx []] = evm_selfbalance ctx [].
Proof.
intros ctx.
unfold evm_address. unfold evm_balance.
unfold evm_selfbalance.
rewrite zext_split1.
reflexivity.
Qed.


Lemma optimize_balance_address_sbinding_snd:
opt_sbinding_snd optimize_balance_address_sbinding.
Proof.
unfold opt_sbinding_snd.
intros val val' tools sb maxidx ctx idx flag 
  Hvalid Hoptm_sbinding.
split.
- (* valid_sbindings *)
  apply valid_bindings_snd_opt with (val:=val)(opt:=optimize_balance_address_sbinding)
    (tools:=tools)(flag:=flag)(ctx:=ctx); try assumption.
  apply optimize_balance_address_sbinding_smapv_valid. 
    
- (* evaluation is preserved *) 
  intros model mem strg ext v Hismodel Heval_orig.
  (*assert (Hlen2 := Hlen).
  rewrite -> Hlen in Hlen2.
  rewrite <- Hlen in Hlen2 at 2.*)
  unfold optimize_balance_address_sbinding in Hoptm_sbinding.
  destruct val as [vv|vv|label args|offset smem|key sstrg|offset seze smem]
    eqn: eq_val; try inject_rw Hoptm_sbinding eq_val'.
  (* SymOp label args *)
  destruct label; try inject_rw Hoptm_sbinding eq_val'.
  destruct args as [|arg1 r1]; try inject_rw Hoptm_sbinding eq_val'.
  destruct r1 as [|arg2 r2]; try inject_rw Hoptm_sbinding eq_val'.
  destruct (follow_in_smap arg1 idx sb) as [fsmv_arg1|] eqn: eq_follow_arg1;
    try inject_rw Hoptm_sbinding eq_val'.
  destruct fsmv_arg1 as [smv_arg1 idx' sb'].
  destruct smv_arg1 as [x1|x2|label1 args1|x4|x5|x6]; 
    try inject_rw Hoptm_sbinding eq_val'.
  destruct label1; try inject_rw Hoptm_sbinding eq_val'.
  destruct args1;  try inject_rw Hoptm_sbinding eq_val'.
 
  injection Hoptm_sbinding as eq_val' _. 
  rewrite <- eq_val'.
  unfold eval_sstack_val in Heval_orig. simpl in Heval_orig.
  rewrite -> PeanoNat.Nat.eqb_refl in Heval_orig.
  simpl in Heval_orig.
  destruct (eval_sstack_val' maxidx arg1 model mem strg ext idx sb evm_stack_opm)
    as [varg1|] eqn: eval_arg1; try discriminate.
  rewrite <- Heval_orig.
  
  destruct maxidx as [|maxidx'] eqn: eq_maxidx; try discriminate.
  simpl in eval_arg1.
  rewrite -> eq_follow_arg1 in eval_arg1.
  simpl in eval_arg1.
  injection eval_arg1 as eq_varg1.
  rewrite <- eq_varg1.
  
  (* simpl was extremely slow, so I've evaluated the call step-by-step
     manually *)
  unfold eval_sstack_val. unfold eval_sstack_val'.
  rewrite -> follow_in_smap_head_op.
  rewrite -> evm_stack_opm_SELFBALANCE.
  rewrite -> length_zero.
  rewrite -> map_option_empty.
  rewrite -> balance_address.
  reflexivity.
Qed.


End Opt_balance_address.
