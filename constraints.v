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

(* Record checkers: Type := { *)
(*   checker: nat; *)
(*   snd: nat *)
(* }. *)

(* Definition asdf: checkers := {| a:= 10 ;  b:= 10|}. *)

(* Definition es_10 := a asdf. *)

(* 
    Literals 
{{{*)
(* INFO: STABLE API *)
Inductive cliteral : Type :=
  | C_VAR (n : nat) (* x *)
  | C_VAL (n : nat) (* c *)
  | C_VAR_DELTA (n delta : nat) (* x + c *)
.

Print eq.
Check (eq (C_VAR 10) (C_VAL 10)).

Example sanity_check : forall (x: cliteral), x = x.
Proof. intros c. reflexivity. Qed.

Definition eq_clit (c c': cliteral): bool :=
  match c, c' with
  | C_VAR n, C_VAR n' => n =? n'
  | C_VAL n, C_VAL n' => n =? n'
  | C_VAR_DELTA n d, C_VAR_DELTA n' d' => (n =? n') && (d =? d')
  | _, _ => false
  end.

Theorem eq_clit_refl: forall c: cliteral, eq_clit c c = true. 
Proof. (*{{{*)
  intros c.
  destruct c;
  try apply Bool.andb_true_iff;
  try split;
  try apply PeanoNat.Nat.eqb_refl.
Qed. (*}}}*)

Theorem eq_clit_snd: forall c c': cliteral,((eq_clit c c' = true) <-> c = c').
Proof. (*{{{*)
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
      apply PeanoNat.Nat.eqb_eq in c_eq_c'.
      rewrite c_eq_c'.
      reflexivity.
  -- destruct c'; try discriminate.
     simpl in c_eq_c'.
     try apply Bool.andb_true_iff in c_eq_c'.
     destruct c_eq_c' as [n_eq_n' d_eq_d'].
      apply PeanoNat.Nat.eqb_eq in n_eq_n'.
      apply PeanoNat.Nat.eqb_eq in d_eq_d'.
     rewrite <- n_eq_n'. rewrite <- d_eq_d'. reflexivity.
  - intro c_is_c'.
    rewrite c_is_c'.
    apply eq_clit_refl.
Qed. (*}}}*)

Theorem eq_clit_comm: forall c c': cliteral, eq_clit c c' = eq_clit c' c. 
Proof. (* {{{ *)
  intros [n | n | n d] [n' | n' | n' d'];
      try apply PeanoNat.Nat.eqb_sym || reflexivity.
  - simpl.
    rewrite (PeanoNat.Nat.eqb_sym n n').
    rewrite (PeanoNat.Nat.eqb_sym d d').
    reflexivity.
Qed. (* }}} *)
(* }}} Literals *)

(* 
    Constraints 
{{{ *) 
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
Proof. (* {{{ *)
  destruct c; 
  apply andb_true_intro;
  split;
  apply eq_clit_refl.
Qed. (* }}} *)

Theorem eqc_snd(c c' : constraint): eqc c c' = true <-> c = c'.
Proof. (* {{{ *)
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
Qed. (* }}} *)

Theorem eqc_comm: forall c c', eqc c c' = eqc c' c.
Proof. (* {{{ *)
  intros [l r | l r | l r] [l' r' | l' r' | l' r'];
  simpl;
  try rewrite (eq_clit_comm l l');
  try rewrite (eq_clit_comm r r');
  reflexivity.
Qed. (* }}} *)

Notation conjunction := (list constraint).
Notation disjuntion := (list conjunction).
Definition constraints : Type := disjuntion.
(** A [constraints] is a disjunctive normal form representation of hypothesis. *)

(*}}} Constraints *)

(*
  Satisfiability of constaints
{{{*)

Definition assignment : Type := nat -> EVMWord.
(** Maps variable indexes to concrete values *)

Definition cliteral_to_nat (model: assignment) (c: cliteral): nat :=
  (** The value of the literal [c] under the assigment [model]. *)
  match c with
  | C_VAL n => n
  | C_VAR i => wordToNat (model i)
  | C_VAR_DELTA i delta => wordToNat (model i) + delta
  end.

(* INFO: STABLE API *)
Definition satisfies_single_constraint (model: assignment) (c: constraint) : bool :=
  let get_value := cliteral_to_nat model in 
  match c with
  | C_EQ l r => get_value l =? get_value r
  | C_LT l r => get_value l <? get_value r
  | C_LE l r => get_value l <=? get_value r
  end.

Definition satisfies_conjunction (model: assignment) (conj: conjunction): bool :=
  forallb (satisfies_single_constraint model) conj.

Definition satisfies_constraints (model: assignment) (cs: constraints): bool :=
  forallb (satisfies_conjunction model) cs.

Definition is_model (cs : constraints) (model : assignment) : bool := satisfies_constraints model cs.
(** A model of some constraints is a model which satisfies the constraints *)

Definition is_sat (cs : constraints) : Prop :=
  exists (model : assignment), is_model cs model = true.
(* }}} *)

(*
  Implication checkers
{{{ *)

Record imp_checker: Type := 
  { imp_checker_fun: constraints -> constraint -> bool
  ; imp_checker_snd: forall (cs: constraints) (c: constraint),
      imp_checker_fun cs c = true -> forall (model: assignment),
      is_model cs model = true -> satisfies_single_constraint model c = true
  }.


Record conj_imp_checker: Type := 
  { conj_imp_checker_fun: conjunction -> constraint -> bool
  ; conj_imp_checker_snd: forall (cs: conjunction) (c: constraint),
    conj_imp_checker_fun cs c = true -> forall (model: assignment),
    satisfies_conjunction model cs = true -> satisfies_single_constraint model c = true
  }.

Program Definition mk_imp_checker (checker: conj_imp_checker): imp_checker := {|
  imp_checker_fun (cs : constraints) c := match cs with
              | [] => false
              | _ => forallb (fun conj => conj_imp_checker_fun checker conj c) cs
              end
  |}.
Next Obligation. (* {{{ *)
  destruct checker as [checker checker_snd].
  rename H into full_checker__cs_imp_c.
  generalize dependent H0.
  induction cs as [|c' cs' IHcs'].
  - discriminate.
  - simpl.
    simpl in full_checker__cs_imp_c.
    apply Bool.andb_true_iff in full_checker__cs_imp_c as [checker__c'_imp_c checker__cs'_imp_c].
    destruct cs' as [|c'' cs''] eqn:E.
    -- simpl.
       rewrite Bool.andb_true_r.
       exact (checker_snd c' c checker__c'_imp_c  model).
    -- pose proof (IHcs' checker__cs'_imp_c) as IHcs'.
       unfold conj_imp_checker_snd in checker_snd.
       pose proof (checker_snd c' c checker__c'_imp_c model) as H.
       intros model_sat_c'__and__model_sat_cs'.
       apply Bool.andb_true_iff in model_sat_c'__and__model_sat_cs' as [model_sat_c' model_sat_cs'].
       exact (H model_sat_c').
Qed. (* }}} *)

(* }}} Implication checkers *)

(*
  Inclusion implication checker
{{{ *)
Program Definition inclusion_conj_imp_checker: conj_imp_checker := {| 
  conj_imp_checker_fun := fun cs c => existsb (eqc c) cs
|}.
Next Obligation. (* {{{ *)
  unfold imp_checker_snd.
  induction cs as [|c' cs' IHcs'].
  - discriminate.
  - simpl in H.
    destruct (eqc c' c) eqn:c'_is_c.
    -- apply eqc_snd in c'_is_c.
       simpl.
       apply Bool.andb_true_iff in H0.
       destruct H0 as [H0 _].
       rewrite c'_is_c in H0.
       exact H0.
    -- simpl.
       rewrite (eqc_comm c' c) in c'_is_c.
       simpl in H0.
       apply Bool.andb_true_iff in H0.
       destruct H0 as [_ H0].
       rewrite c'_is_c in H.
       simpl in H.
       exact (IHcs' H H0).
Qed. (* }}} *)

Definition inclusion_imp_checker := mk_imp_checker inclusion_conj_imp_checker.

(* }}} *)

(* 
   just an operation that checks if the constraints are specifiable, 
   for now it simply returns true. 
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

End Constraints.

(* vim: set foldmethod=marker: *)
