(*
Draft of rule-based optimization that uses a constraint checker
The concrete checker is assumed (dummy/invalid implementation).
*)

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


Module Opt_lt_constraints.


Definition the_checker : imp_checker :=
fun (cs: constraints) => 
  fun (c: constraint) => 
    true.
   
Theorem the_checker_snd : imp_checker_snd the_checker.
Admitted.

Definition sstack_val_to_cliteral (sv: sstack_val) : option cliteral :=
match sv with
| Val val => Some (C_VAL (wordToNat val))
| InVar var => Some (C_VAR var)
| _ => None
end.

Definition gen_lt_constr (sv1 sv2: sstack_val) : option constraint :=
match sstack_val_to_cliteral sv1 with
| None => None
| Some cl1 => match sstack_val_to_cliteral sv2 with
              | None => None
              | Some cl2 => Some (C_LT cl1 cl2)
              end
end.

(* LT(X,Y) = 1   if constraints => X<Y *)
Definition optimize_lt_constraints_sbinding : opt_smap_value_type := 
fun (val: smap_value) =>
fun (fcmp: sstack_val_cmp_t) =>
fun (sb: sbindings) =>
fun (maxid: nat) =>
fun (ctx: constraints) =>
fun (ops: stack_op_instr_map) => 
match val with
| SymOp LT [arg1; arg2] => 
  match gen_lt_constr arg1 arg2 with
  | None => (val, false)
  | Some constr => match the_checker ctx constr with
                   | false => (val, false)
                   | true => (SymBasicVal (Val WOne), true)
                   end
  end
| _ => (val, false)
end.


Lemma optimize_lt_constraints_sbinding_smapv_valid:
opt_smapv_valid_snd optimize_lt_constraints_sbinding.
Proof.
unfold opt_smapv_valid_snd.
intros ctx n fcmp sb val val' flag.
intros Hvalid_smapv_val Hvalid_sb Hoptm_sbinding.
unfold optimize_lt_constraints_sbinding in Hoptm_sbinding.
destruct (val) as [basicv|pushtagv|label args|offset smem|key sstrg|
  offset size smem] eqn: eq_val; try inject_rw Hoptm_sbinding eq_val'.
destruct label eqn: eq_label; try inject_rw Hoptm_sbinding eq_val'.
(* LT *)
destruct args as [|arg1 r1] eqn: eq_args; try inject_rw Hoptm_sbinding eq_val'.
destruct r1 as [|arg2 r2] eqn: eq_r1; try inject_rw Hoptm_sbinding eq_val'.
destruct r2 as [|arg3 r3] eqn: eq_r2; try inject_rw Hoptm_sbinding eq_val'.
destruct (gen_lt_constr); try inject_rw Hoptm_sbinding eq_val'.
destruct (the_checker ctx c) eqn: eq_the_checker.
- injection Hoptm_sbinding as eq_val' eq_flag.
  rewrite <- eq_val'.
  simpl. intuition.
- inject_rw Hoptm_sbinding eq_val'.
Qed.


(* arg1 and arg2 can only be Val or InVar, so "sb" could be omitted 
   Probably the same with idx *)
Theorem lt_constr_ok: forall arg1 arg2 c ctx idx sb,
gen_lt_constr arg1 arg2 = Some c ->
the_checker ctx c = true -> 
forall model mem strg ext maxidx v,
is_model ctx model = true -> 
eval_sstack_val (FreshVar idx) model mem strg ext maxidx
               ((idx, SymOp LT [arg1; arg2]) :: sb) evm_stack_opm = Some v ->
v = WOne.
Proof.
Admitted.

(* arg1 and arg2 can only be Val or InVar, so "sb" could be omitted 
   Probably the same with "idx", which is irrelevant for eval_sstack_val' 
   "maxidx" can be anything > 0
*)
Theorem lt_constr_ok': forall (arg1 arg2: sstack_val) (c: constraint) 
  (ctx: constraints) (idx: nat) (sb: sbindings),
gen_lt_constr arg1 arg2 = Some c ->
the_checker ctx c = true -> 
forall (model: assignment) (mem: memory) (strg: storage) (ext: externals) 
  (maxidx: nat) (arg1v arg2v: EVMWord),
is_model ctx model = true -> 
eval_sstack_val' maxidx arg1 model mem strg ext idx sb evm_stack_opm = Some arg1v ->
eval_sstack_val' maxidx arg2 model mem strg ext idx sb evm_stack_opm = Some arg2v ->
(N.ltb (wordToN arg1v) (wordToN arg2v)) = true.
Proof.
Admitted.

Lemma evm_stack_opm_lt: 
  evm_stack_opm LT = OpImp 2 evm_lt None (Some lt_exts_ind).
Proof.
intuition.
Qed.

Lemma length_2:  forall {T} (x y: T), length [x; y] =? 2 = true.
Proof.
intuition.
Qed.



Lemma optimize_lt_constraints_sbinding_snd:
opt_sbinding_snd optimize_lt_constraints_sbinding.
Proof.
unfold opt_sbinding_snd.
intros val val' fcmp sb maxidx ctx idx flag Hsafe_sstack_val_cmp
  Hvalid Hissat Hoptm_sbinding.
split.
- (* valid_sbindings *)
  apply valid_bindings_snd_opt with (val:=val)(opt:=optimize_lt_constraints_sbinding)
    (fcmp:=fcmp)(flag:=flag)(ctx:=ctx); try assumption.
  apply optimize_lt_constraints_sbinding_smapv_valid.

- (* evaluation is preserved *) 
  intros model mem strg ext v Hismodel Heval_orig.
  unfold optimize_lt_constraints_sbinding in Hoptm_sbinding.
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
  destruct (gen_lt_constr arg1 arg2) 
    eqn: eq_gen_lt; try inject_rw Hoptm_sbinding eq_val'.
  destruct (the_checker ctx c) eqn: eq_the_checker; 
    try inject_rw Hoptm_sbinding eq_val'.
  
  unfold eval_sstack_val in Heval_orig.
  simpl in Heval_orig.
  rewrite -> PeanoNat.Nat.eqb_refl in Heval_orig.
  rewrite -> evm_stack_opm_lt in Heval_orig.
  rewrite -> length_2 in Heval_orig.
  unfold map_option in Heval_orig.
  destruct (eval_sstack_val' maxidx arg1 model mem strg ext idx sb evm_stack_opm)
    as [arg1v|] eqn: eq_eval_arg1; try discriminate.
  destruct (eval_sstack_val' maxidx arg2 model mem strg ext idx sb evm_stack_opm)
    as [arg2v|] eqn: eq_eval_arg2; try discriminate.
    
  pose proof (lt_constr_ok' arg1 arg2 c ctx idx sb eq_gen_lt eq_the_checker
    model mem strg ext maxidx arg1v arg2v Hismodel eq_eval_arg1 eq_eval_arg2)
    as Hevm_lt.
  simpl in Heval_orig.
  rewrite -> Hevm_lt in Heval_orig.
  injection Heval_orig as Hv.
  
  rewrite <- Hv.
  injection Hoptm_sbinding as Hval' Hflag.
  rewrite <- Hval'.
  unfold eval_sstack_val.
  simpl. 
  rewrite -> PeanoNat.Nat.eqb_refl.
  reflexivity.
Qed.


End Opt_lt_constraints.
