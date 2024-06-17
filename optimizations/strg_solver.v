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

Require Import FORVES2.storage_ops_solvers.
Import StorageOpsSolvers.

Require Import FORVES2.storage_ops_solvers_impl.
Import StorageOpsSolversImpl.

Require Import FORVES2.storage_ops_solvers_impl_soundness.
Import StorageOpsSolversImplSoundness.

Require Import FORVES2.constraints.
Import Constraints.

Require Import FORVES2.context.
Import Context.

Require Import FORVES2.tools_types.
Import ToolsTypes.

Require Import List.
Import ListNotations.


Module Opt_strg_solver.

Definition strg_solver_applied (val1 val2: smap_value) : bool :=
(* If sload_solver does not return SymSLOAD or the symbolic storages have 
   different lengths, then optimized *)
match val1, val2 with
| SymSLOAD skey sstrg, SymSLOAD skey' sstrg' => negb (length sstrg =? length sstrg')
| _, _ => true
end.

(* Storage solver 
  SymSLOAD skey sstrg --> smapv
     if basic_sload_solver (SymSLOAD skey sstrg) = smapv
*)
Definition optimize_strg_solver_sbinding : opt_smap_value_type :=
fun (val: smap_value) =>
fun (tools: Tools_1.tools_1_t) =>
fun (sb: sbindings) =>
fun (maxid: nat) =>
fun (ctx: ctx_t) =>
fun (ops: stack_op_instr_map) =>
  let fcmp := Tools_1.sstack_val_cmp tools in
  match val with
  | SymSLOAD skey sstrg => 
      let val' := (basic_sload_solver (fun _:nat => fcmp) ctx skey sstrg  
                     (SymMap maxid sb) ops) in
      let flag := strg_solver_applied val val' in
      (val', flag)
  | _ => (val, false)
  end.
(* TODO:
- CHECK if is better to pass the whole smap ==> adapt 60 files
- CHECK if maxid is correctly computed
- CHECK if (fun _:nat => fcmp) is an appropiate value of sstack_val_cmp_ext_1_t
    (fcmp is already instantiated with the right maxid, so the lambda receives a
     dummy maxid and discards it)
*)


Lemma optimize_strg_solver_sbinding_smapv_valid:
opt_smapv_valid_snd optimize_strg_solver_sbinding.
Proof.
unfold opt_smapv_valid_snd.
intros ctx n tools sb val val' flag.
intros Hvalid_smapv_val Hvalid_sb Hoptm_sbinding.
unfold optimize_strg_solver_sbinding in Hoptm_sbinding.

destruct tools.
unfold Tools_1.sstack_val_cmp in Hoptm_sbinding.
remember sstack_val_cmp as fcmp.
assert(Hsafe_sstack_val_cmp:=H_sstack_val_cmp_snd).

destruct (val) as [basicv|pushtagv|label args|offset smem|skey sstrg|
  offset size smem] eqn: eq_val; try (
    injection Hoptm_sbinding as eq_val' _;
    rewrite <- eq_val';
    assumption).
(* SymSLOAD skey sstrg *)
pose proof (basic_sload_solver_snd (fun _ : nat => fcmp)
    (safe_fcm_ext_1 fcmp Hsafe_sstack_val_cmp)).
unfold sload_solver_snd in H.
destruct H as [Hsolver_valid _].
unfold sload_solver_valid_res in Hsolver_valid.
specialize Hsolver_valid with (m:=SymMap n sb)(sstrg:=sstrg)(skey:=skey)
  (ctx:=ctx)(smv:=val')(ops:=evm_stack_opm).
simpl in Hsolver_valid.
unfold valid_smap_value in Hvalid_smapv_val.
destruct Hvalid_smapv_val as [Hvalid_sstack_val Hvalid_sstorage].
injection Hoptm_sbinding as eq_basic_mload_solver _.
pose proof (Hsolver_valid Hvalid_sstorage Hvalid_sstack_val 
  eq_basic_mload_solver).
assumption.
Qed.


Lemma optimize_strg_solver_sbinding_snd:
opt_sbinding_snd optimize_strg_solver_sbinding.
Proof.
unfold opt_sbinding_snd.
intros val val' tools sb maxidx ctx idx flag 
  Hvalid Hoptm_sbinding.
split.
- (* valid_sbindings *)
  apply valid_bindings_snd_opt with (val:=val)(opt:=optimize_strg_solver_sbinding)
    (tools:=tools)(flag:=flag)(ctx:=ctx); try assumption.
  apply optimize_strg_solver_sbinding_smapv_valid. 

- (* evaluation is preserved *) 
  intros model mem strg exts v His_model Heval_orig.
  unfold optimize_strg_solver_sbinding in Hoptm_sbinding.
  destruct val as [vv|vv|label args|offset smem|skey sstrg|offset size smem]
    eqn: eq_val; try inject_rw Hoptm_sbinding eq_val'.

  destruct tools.
  unfold Tools_1.sstack_val_cmp in Hoptm_sbinding.
  remember sstack_val_cmp as fcmp.
  assert(Hsafe_sstack_val_cmp:=H_sstack_val_cmp_snd).

  (* SymSLOAD skey sstrg *)
  injection Hoptm_sbinding as eq_basic_solver eq_flag.


  pose proof (basic_sload_solver_snd (fun _ : nat => fcmp)
      (safe_fcm_ext_1 fcmp Hsafe_sstack_val_cmp)).
  unfold sload_solver_snd in H.
  destruct H as [Hsolver_valid Hsolver_correct].
  unfold sload_solver_correct_res in Hsolver_correct.
  specialize Hsolver_correct with (m := SymMap idx sb)(sstrg:=sstrg)
    (skey:=skey)(ctx:=ctx)(smv:=val')
    (ops:=evm_stack_opm)(idx1:=idx)(m1:=SymMap maxidx
    ((idx,val')::sb)).
  unfold valid_bindings in Hvalid.
  destruct Hvalid as [eq_maxidx_idx [eq_valid_smapv eq_valid_bindings]].
  fold valid_bindings in eq_valid_bindings.
  unfold valid_smap in Hsolver_correct.
  simpl in Hsolver_correct.

  pose proof (Hsolver_correct eq_valid_bindings) as Hsolver_correct.
  unfold valid_smap_value in eq_valid_smapv.
  destruct eq_valid_smapv as [eq_valid_offset eq_valid_smem].
  rewrite -> eq_maxidx_idx in Hsolver_correct.
  pose proof (Hsolver_correct eq_valid_smem eq_valid_offset eq_basic_solver) 
    as Hsolver_correct.
  assert ((idx, SymMap (S idx) ((idx, val') :: sb)) =
          (idx, SymMap (S idx) ((idx, val') :: sb))) as eq_smaps; 
      try reflexivity.
  pose proof (Hsolver_correct eq_smaps) as Hsolver_correct.
  destruct Hsolver_correct as [idx2 [m2 [eq_m2 HH]]].
  injection eq_m2 as eq_idx2 eq_m2.
  specialize HH with (model:=model)(mem:=mem)(strg:=strg)(exts:=exts).
  pose proof (HH His_model) as HH.
  destruct HH as [vv [Heval1 Heval2]].
  rewrite <- eq_idx2 in Heval2.
  rewrite <- eq_m2 in Heval2.
  simpl in Heval2.
  rewrite <- eq_maxidx_idx in Heval2.
  rewrite -> Heval_orig in Heval2.
  rewrite -> Heval2.
  rewrite -> eq_maxidx_idx.
  assumption.
Qed.


End Opt_strg_solver.
