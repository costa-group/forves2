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


Module Opt_eval.


(* EVAL *)
Definition optimize_eval_sbinding : opt_smap_value_type := 
fun (val: smap_value) =>
fun (tools: Tools_1.tools_1_t) =>
fun (sb: sbindings) =>
fun (maxid: nat) =>
fun (ctx: ctx_t) =>
fun (ops: stack_op_instr_map) =>
  let fcmp := Tools_1.sstack_val_cmp tools in
  match val with
  | SymOp op args => 
      match follow_to_val_args args maxid sb with
      | Some vargs => 
          match ops op with
          | OpImp nargs f Hcomm Hctx_indep => 
              match Hctx_indep with
              | Some _ => if (List.length args =? nargs) then
                            (SymBasicVal (Val (f empty_externals vargs)), true)
                          else 
                            (val, false)
              | None => (val, false)
              end
          end
      | None => (val, false)
      end
  | _ => (val, false)
  end.






Lemma optimize_eval_sbinding_smapv_valid:
opt_smapv_valid_snd optimize_eval_sbinding.
Proof.
unfold opt_smapv_valid_snd.
intros ctx n tools sb val val' flag.
intros Hvalid_smapv_val Hvalid_sb Hoptm_sbinding.
unfold optimize_eval_sbinding in Hoptm_sbinding.
destruct (val) as [basicv|pushtagv|label args|offset smem|key sstrg|
  offset size smem] eqn: eq_val; try (
    injection Hoptm_sbinding as eq_val' _;
    rewrite <- eq_val';
    assumption).
(* SymOp label args *)
destruct (follow_to_val_args args n sb) as [vargs|] eqn: eq_follow; 
  try inject_rw Hoptm_sbinding eq_val'.
destruct (evm_stack_opm label) as [nargs f Hcomm Hctx_indep] eqn: eq_ops_label; 
  try inject_rw Hoptm_sbinding eq_val'.
destruct (Hctx_indep) as [H|]; try inject_rw Hoptm_sbinding eq_val'.
destruct (length args =? nargs); try inject_rw Hoptm_sbinding eq_val'.
injection Hoptm_sbinding as eq_val' _.
rewrite <- eq_val'.
simpl. intuition.
Qed.


Lemma optimize_eval_sbinding_snd:
opt_sbinding_snd optimize_eval_sbinding.
Proof.
unfold opt_sbinding_snd.
intros val val' tools sb maxidx ctx idx flag 
  Hvalid Hoptm_sbinding.
split.
- (* valid_sbindings *)
  apply valid_bindings_snd_opt with (val:=val)(opt:=optimize_eval_sbinding)
    (tools:=tools)(flag:=flag)(ctx:=ctx); try assumption.
  apply optimize_eval_sbinding_smapv_valid. 
    
- (* evaluation is preserved *) 
  intros model mem strg ext v Hlen Heval_orig.
  unfold optimize_eval_sbinding in Hoptm_sbinding.
  destruct val as [vv|vv|label args|offset smem|key sstrg|offset seze smem]
    eqn: eq_val; try inject_rw Hoptm_sbinding eq_val'.
  (* SymOp label args *)
  destruct (follow_to_val_args args idx sb) as [vargs|] eqn: eq_follow; 
  try inject_rw Hoptm_sbinding eq_val'.
  destruct (evm_stack_opm label) as [nargs f Hcomm Hctx_indep] 
    eqn: eq_ops_label; try inject_rw Hoptm_sbinding eq_val'.
  destruct (Hctx_indep) as [H|] eqn: eq_Hctx; 
    try inject_rw Hoptm_sbinding eq_val'.
  destruct (length args =? nargs) eqn: eq_len; 
    try inject_rw Hoptm_sbinding eq_val'.
  injection Hoptm_sbinding as eq_val' _.
  rewrite <- eq_val'.
  unfold eval_sstack_val. simpl.
  rewrite -> PeanoNat.Nat.eqb_refl.
  unfold eval_sstack_val in Heval_orig. simpl in Heval_orig.
  rewrite -> PeanoNat.Nat.eqb_refl in Heval_orig.
  rewrite -> eq_ops_label in Heval_orig.
  rewrite -> eq_len in Heval_orig.
  destruct (map_option
                 (fun sv' : sstack_val =>
                  eval_sstack_val' maxidx sv' model mem strg ext idx sb
                    evm_stack_opm) args) as [vargs'|] eqn: eq_mapo;
    try discriminate.
  pose proof (follow_to_val_args_eval_eq args idx sb vargs maxidx model mem 
    strg ext vargs' eq_follow eq_mapo) as eq_vargs'.
  rewrite <- eq_vargs' in Heval_orig.
  rewrite -> H with (exts2:=ext).
  assumption.
Qed.


End Opt_eval.
