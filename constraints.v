Require Import bbv.Word.
Require Import Nat. 
Require Import Coq.NArith.NArith.

Require Import FORVES2.constants.
Import Constants.

Require Import FORVES2.program.
Import Program.

Require Import List.
Import ListNotations.


Module Constraints.

(* 
    Literals 
{{{*)
(* INFO: STABLE API *)
Inductive cliteral : Type :=
  | C_VAR (n : nat) (* x *)
  | C_VAL (n : N) (* c *)
  | C_VAR_DELTA (n: nat)(delta : N) (* x + c *)
.

Definition eq_clit (c c': cliteral): bool :=
  match c, c' with
  | C_VAR n, C_VAR n' => n =? n'
  | C_VAL n, C_VAL n' => (n =? n')%N
  | C_VAR_DELTA n d, C_VAR_DELTA n' d' => (n =? n') && (d =? d')%N
  | _, _ => false
  end.

Theorem eq_clit_refl: forall c: cliteral, eq_clit c c = true. 
Proof. 
  intros c.
  destruct c;
  try apply Bool.andb_true_iff;
  try split;
  try apply N.eqb_refl;
  try apply PeanoNat.Nat.eqb_refl.
Qed. 

Theorem eq_clit_snd: forall c c': cliteral,((eq_clit c c' = true) <-> c = c').
Proof. 
  intros c c'.
  split.
  - intro c_eq_c'.
    destruct c.
  -- destruct c'; try discriminate.
  --- simpl in c_eq_c'.
      apply PeanoNat.Nat.eqb_eq in c_eq_c'.
      rewrite c_eq_c'.
      reflexivity.
  -- destruct c'; try discriminate.
  --- simpl in c_eq_c'.
      apply N.eqb_eq in c_eq_c'.
      rewrite c_eq_c'.
      reflexivity.
  -- destruct c'; try discriminate.
     simpl in c_eq_c'.
     try apply Bool.andb_true_iff in c_eq_c'.
     destruct c_eq_c' as [n_eq_n' d_eq_d'].
      apply PeanoNat.Nat.eqb_eq in n_eq_n'.
      apply N.eqb_eq in d_eq_d'.
     rewrite <- n_eq_n'. rewrite <- d_eq_d'. reflexivity.
  - intro c_is_c'.
    rewrite c_is_c'.
    apply eq_clit_refl.
Qed. 

Theorem eq_clit_comm: forall c c': cliteral, eq_clit c c' = eq_clit c' c. 
Proof.
  intros [n | n | n d] [n' | n' | n' d'];
      try (apply N.eqb_sym || apply PeanoNat.Nat.eqb_sym) || reflexivity.
  - simpl.
    rewrite (PeanoNat.Nat.eqb_sym n n').
    rewrite (N.eqb_sym d d').
    reflexivity.
Qed.
(*}}} End Literals *)

(* 
   Constraints 
{{{*) 
Inductive constraint : Type :=
  | C_LT (l r : cliteral)
  | C_EQ (l r : cliteral)
  | C_LE (l r : cliteral)
.


Definition eqc (c c': constraint): bool :=
  match c, c' with
  | C_LT l r , C_LT l' r' 
  | C_EQ l r , C_EQ l' r' 
  | C_LE l r , C_LE l' r' => eq_clit l l' && eq_clit r r'
  | _, _ => false
  end.

Theorem eqc_refl(c: constraint): eqc c c = true.
Proof. 
  destruct c; 
  apply andb_true_intro;
  split;
  apply eq_clit_refl.
Qed. 

Theorem eqc_snd(c c' : constraint): eqc c c' = true <-> c = c'.
Proof. 
  split.
  - intro c_eq_c'.
    destruct c;
    destruct c' as [l' r'|l' r' |l' r']; try discriminate;
        simpl in c_eq_c';
        symmetry in c_eq_c';
        apply Bool.andb_true_eq in c_eq_c';
        destruct c_eq_c' as [l_eq_l' r_eq_r'];
        symmetry in l_eq_l';
        symmetry in r_eq_r';
        apply eq_clit_snd in l_eq_l';
        apply eq_clit_snd in r_eq_r';
        rewrite l_eq_l';
        rewrite r_eq_r';
        reflexivity.
  - intros c_is_c'.
    rewrite c_is_c'.
    apply eqc_refl.
Qed. 

Theorem eqc_comm: forall c c', eqc c c' = eqc c' c.
Proof. 
  intros [l r | l r | l r] [l' r' | l' r' | l' r'];
      simpl;
      try rewrite (eq_clit_comm l l');
      try rewrite (eq_clit_comm r r');
      reflexivity.
Qed. 

Notation conjunction := (list constraint).
Notation disjunction := (list conjunction).
Definition constraints : Type := disjunction.
(** A [constraints] is a disjunctive normal form representation of hypothesis. *)

(*}}} end Constraints *)

(*
   Satisfiability of constraints
{{{*)

Definition assignment : Type := nat -> EVMWord.
(** Maps variable indexes to concrete values *)

Definition cliteral_to_nat (model: assignment) (c: cliteral): N :=
  (** The value of the literal [c] under the assigment [model]. *)
  match c with
  | C_VAL n => n
  | C_VAR i => wordToN (model i)
  | C_VAR_DELTA i delta => wordToN (model i) + delta
  end.

(* INFO: STABLE API *)
Definition satisfies_single_constraint (model: assignment) (c: constraint) : bool :=
  let get_value := cliteral_to_nat model in 
  match c with
  | C_EQ l r => (get_value l =? get_value r)%N
  | C_LT l r => (get_value l <? get_value r)%N
  | C_LE l r => (get_value l <=? get_value r)%N
  end.

Definition satisfies_conjunction (model: assignment) (conj: conjunction): bool :=
  forallb (satisfies_single_constraint model) conj.

Definition satisfies_constraints (model: assignment) (cs: constraints): bool :=
  existsb (satisfies_conjunction model) cs.

Definition is_model (cs : constraints) (model : assignment) : bool := satisfies_constraints model cs.
(** A model of some constraints is a model which satisfies the constraints *)

Definition is_sat (cs : constraints) : Prop :=
  exists (model : assignment), is_model cs model = true.

Definition imply(cs: constraints)(c: constraint) := forall (m: assignment),
  satisfies_constraints m cs = true -> satisfies_single_constraint m c = true.

Definition conj_imply(cs: conjunction)(c: constraint) := forall (m: assignment),
  satisfies_conjunction m cs = true -> satisfies_single_constraint m c = true.
(*}}} End of Satisfiability of constraints*)

(*
   Implication checkers
{{{ *)

Record imp_checker: Type := 
  { imp_checker_fun: constraints -> constraint -> bool
  ; imp_checker_snd: forall (cs: constraints) (c: constraint),
      imp_checker_fun cs c = true -> imply cs c
  }.


Record conj_imp_checker: Type := 
  { conj_imp_checker_fun: conjunction -> constraint -> bool
  ; conj_imp_checker_snd: forall (cs: conjunction) (c: constraint),
      conj_imp_checker_fun cs c = true -> conj_imply cs c
  }.

Program Definition mk_imp_checker (checker: conj_imp_checker): imp_checker := {|
  imp_checker_fun (cs : constraints) c := 
    match cs with
    | [] => false
    | _ => forallb (fun conj => conj_imp_checker_fun checker conj c) cs
    end
|}.
Next Obligation. 
  unfold imply; intros model.
  destruct checker as [checker checker_snd].
  rename H into full_checker__cs_imp_c.
  induction cs as [|c' cs']; try discriminate.
  simpl in *.
  apply Bool.andb_true_iff in full_checker__cs_imp_c 
    as [checker__c'_imp_c checker__cs'_imp_c].
  intros h; apply Bool.orb_true_iff in h as [c'_sat | cs'_sat].
  - exact (checker_snd _ _ checker__c'_imp_c model c'_sat).
  - unfold is_model in cs'_sat.
    destruct cs' as [|c'' cs'']; try discriminate.
    exact (IHcs' checker__cs'_imp_c cs'_sat).
Qed. 
(* }}} Implication checkers *)

(*
   Inclusion implication checker
{{{ *)
Program Definition inclusion_conj_imp_checker: conj_imp_checker := {| 
  conj_imp_checker_fun := fun cs c => existsb (eqc c) cs
|}.
Next Obligation. 
  unfold conj_imply; intros model cs_sat.
  unfold imp_checker_snd.
  induction cs as [|c' cs' IHcs']; try discriminate.
  simpl in H.
  destruct (eqc c' c) eqn:c'_is_c.
  - apply eqc_snd in c'_is_c.
    simpl in *.
    apply Bool.andb_true_iff in cs_sat.
    destruct cs_sat as [c'_sat _].
    rewrite c'_is_c in c'_sat.
    exact c'_sat.
  - simpl.
    rewrite (eqc_comm c' c) in c'_is_c.
    simpl in cs_sat.
    apply Bool.andb_true_iff in cs_sat.
    destruct cs_sat as [_ cs'_sat].
    rewrite c'_is_c in H.
    simpl in H.
    exact (IHcs' H cs'_sat).
Qed. 

Definition inclusion_imp_checker := mk_imp_checker inclusion_conj_imp_checker.
(*}}} End Inclusion implication checker *)


(* 
   just an operation that checks if the constraints are specifiable.
   For now it simply returns true. 
*)

Record sat_checker : Type := 
  { sat_checker_fun : constraints -> bool 
  (* TODO: Perhaps [option assigment] over [bool]? 
           Provides a witness that the constraints are provable *)
  ; sat_checker_snd : forall (cs : constraints),
    sat_checker_fun cs = true -> is_sat cs
  }.

Program Definition chk_is_sat : sat_checker := {|
  sat_checker_fun (cs: constraints) := true
|}.
Next Obligation.
  Admitted.

(* Compute sat_checker_fun chk_is_sat. *)

End Constraints.

(* vim: set foldmethod=marker: *)
