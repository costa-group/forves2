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
  (* | C_EQ_offset(l r : cliteral) (n: nat) *)
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

Definition imp_checker_fun':= constraints -> constraint -> bool.

Definition imp_checker_snd' (checker: imp_checker_fun') :=
  forall (cs: constraints) (c: constraint),
      checker cs c = true -> forall (model: assignment),
      is_model cs model = true -> satisfies_single_constraint model c = true.

Record imp_checker: Type := 
  { imp_checker_fun: imp_checker_fun'
  ; imp_checker_snd: imp_checker_snd' imp_checker_fun
  }.

Definition conj_imp_checker_fun': Type := conjunction -> constraint -> bool.
Definition conj_imp_checker_snd'(checker: conj_imp_checker_fun'): Type := 
  forall (cs: conjunction) (c: constraint),
    checker cs c = true -> forall (model: assignment),
    satisfies_conjunction model cs = true -> satisfies_single_constraint model c = true.

Record conj_imp_checker: Type := 
  { conj_imp_checker_fun: conj_imp_checker_fun'
  ; conj_imp_checker_snd: conj_imp_checker_snd' conj_imp_checker_fun
  }.

Definition mk_imp_checker_fun (checker: conj_imp_checker_fun'): imp_checker_fun' :=
  (** A full implication checker can be made from a conjunctive implication checker by
      checking that all hypothesis conjunctions imply the thesis constraint. *)
  fun cs c => match cs with
              | [] => false
              | _ => forallb (fun conj => checker conj c) cs
              end.

Theorem mk_imp_checker_snd(checker: conj_imp_checker) : 
   imp_checker_snd' (mk_imp_checker_fun checker.(conj_imp_checker_fun)).
Proof. (*{{{*)
  destruct checker as [checker checker_snd].
  intros cs c full_checker__cs_imp_c model.
  induction cs as [|c' cs' IHcs'].
  - discriminate.
  - simpl.
    simpl in full_checker__cs_imp_c.
    apply Bool.andb_true_iff in full_checker__cs_imp_c as [checker__c'_imp_c checker__cs'_imp_c].
    destruct cs' as [|c'' cs''] eqn:E.
    -- simpl.
       rewrite Bool.andb_true_r.

       exact (checker_snd c' c checker__c'_imp_c  model).
    -- unfold mk_imp_checker_fun in  IHcs'.
       pose proof (IHcs' checker__cs'_imp_c) as IHcs'.
       unfold conj_imp_checker_snd in checker_snd.
       pose proof (checker_snd c' c checker__c'_imp_c model) as H.
       intros model_sat_c'__and__model_sat_cs'.
       apply Bool.andb_true_iff in model_sat_c'__and__model_sat_cs' as [model_sat_c' model_sat_cs'].
       exact (H model_sat_c').
Qed. (* }}} *)

Definition mk_imp_checker (checker: conj_imp_checker): imp_checker :=
  {| imp_checker_fun := mk_imp_checker_fun checker.(conj_imp_checker_fun)
   ; imp_checker_snd := mk_imp_checker_snd checker
  |}.

(* }}} Implication checkers *)

(*
  Inclusion implication checker
{{{ *)
Definition inclusion_conj_imp_checker_fun (cs: conjunction) (c: constraint) : bool :=
  existsb (eqc c) cs.

Theorem inclusion_conj_imp_checker_snd: conj_imp_checker_snd' inclusion_conj_imp_checker_fun.
Proof. (* {{{ *)
  unfold imp_checker_snd.
  intros cs c h.
  induction cs as [|c' cs' IHcs'].
  - discriminate.
  - intros model.
    simpl in h.
    destruct (eqc c' c) eqn:c'_is_c.
    -- apply eqc_snd in c'_is_c.
       simpl.
       destruct (satisfies_single_constraint model c') eqn:c'_sat_model.
       --- intros cs'_sat_model.
           rewrite c'_is_c in c'_sat_model.
           exact c'_sat_model.
       --- discriminate.
    -- simpl.
       destruct (satisfies_single_constraint model c') eqn:c'_sat_model.
       --- simpl.
           rewrite (eqc_comm c' c) in c'_is_c.
           rewrite c'_is_c in h.
           simpl in h.
           exact (IHcs' h model).
       --- discriminate.
Qed. (* }}} *)

Definition inclusion_conj_imp_checker := 
  {| conj_imp_checker_fun := inclusion_conj_imp_checker_fun 
   ; conj_imp_checker_snd := inclusion_conj_imp_checker_snd
  |}.

Definition inclusion_imp_checker := mk_imp_checker inclusion_conj_imp_checker.

(* }}} *)


End Constraints.

(* vim: set foldmethod=marker: *)
