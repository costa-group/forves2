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

Inductive cliteral : Type :=
  | C_VAR (n : nat)
  | C_VAL (n : nat).

Definition eq_clit (c c': cliteral): bool :=
  match c, c' with
  | C_VAR n, C_VAR n' => n =? n'
  | C_VAL n, C_VAL n' => n =? n'
  | _, _ => false
  end.

Theorem eq_clit_refl: forall c: cliteral, eq_clit c c = true.
Proof.
  intros c.
  destruct c.
  - simpl.
    apply PeanoNat.Nat.eqb_eq.
    reflexivity.
  - simpl.
    apply PeanoNat.Nat.eqb_eq.
    reflexivity.
Qed.

Theorem eq_clit_snd: forall c c': cliteral,((eq_clit c c' = true) <-> c = c').
Proof.
  intros c c'.
  split.
  - intro c_eq_c'.
    destruct c.
  -- destruct c'.
  --- simpl in c_eq_c'.
      apply PeanoNat.Nat.eqb_eq in c_eq_c'.
      rewrite c_eq_c'.
      reflexivity.
  --- discriminate.
  -- destruct c'.
  --- discriminate.
  --- simpl in c_eq_c'.
      apply PeanoNat.Nat.eqb_eq in c_eq_c'.
      rewrite c_eq_c'.
      reflexivity.
  - intro c_is_c'.
    rewrite c_is_c'.
    apply eq_clit_refl.
Qed.

Inductive constraint : Type :=
  | C_LT (l r : cliteral)
  | C_EQ (l r : cliteral).

Definition eqc (c c': constraint): bool :=
  match c, c' with
  | C_LT l r , C_LT l' r' 
  | C_EQ l r , C_EQ l' r'  => eq_clit l l' && eq_clit r r'
  | _, _ => false
  end.

Definition eqc_refl(c: constraint): eqc c c = true.
Proof.
  destruct c.
  - simpl.
    apply andb_true_intro.
    split.
  -- apply eq_clit_refl.
  -- apply eq_clit_refl.
  - simpl.
    apply andb_true_intro.
    split.
  -- apply eq_clit_refl.
  -- apply eq_clit_refl.
Qed.

Theorem eqc_snd(c c' : constraint): eqc c c' = true <-> c = c'.
Proof.
  split.
  - intro c_eq_c'.
    destruct c.
  -- destruct c' as [l' r'|l' r'].
  --- simpl in c_eq_c'.
      symmetry in c_eq_c'.
      apply Bool.andb_true_eq in c_eq_c'.
      destruct c_eq_c' as [l_eq_l' r_eq_r'].
      symmetry in l_eq_l'.
      symmetry in r_eq_r'.
      apply eq_clit_snd in l_eq_l'.
      apply eq_clit_snd in r_eq_r'.
      rewrite l_eq_l'.
      rewrite r_eq_r'.
      reflexivity.
  --- discriminate.
  -- destruct c' as [l' r'|l' r'].
  --- discriminate.
  --- simpl in c_eq_c'.
      symmetry in c_eq_c'.
      apply Bool.andb_true_eq in c_eq_c'.
      destruct c_eq_c' as [l_eq_l' r_eq_r'].
      symmetry in l_eq_l'.
      symmetry in r_eq_r'.
      apply eq_clit_snd in l_eq_l'.
      apply eq_clit_snd in r_eq_r'.
      rewrite l_eq_l'.
      rewrite r_eq_r'.
      reflexivity.
  - intros c_is_c'.
    rewrite c_is_c'.
    apply eqc_refl.
Qed.

Definition constraints : Type := list constraint.

Definition assignment : Type := nat -> EVMWord.

Definition cliteral_to_nat (model: assignment) (c: cliteral): nat :=
  match c with
  | C_VAL n => n
  | C_VAR i => wordToNat (model i)
  end.

Definition is_model_c (c : constraint) (model : assignment) : bool :=
  let get_value := cliteral_to_nat model in 
  match c with
  | C_EQ l r => get_value l =? get_value r
  | C_LT l r => get_value l <? get_value r
  end.

Fixpoint is_model (cs : constraints) (model : assignment) : bool :=
  match cs with
  | [] => true
  | c::cs' => if (is_model_c c model) then is_model cs' model else false
  end.

Definition is_sat (cs : constraints) : Prop :=
  exists (model : assignment), is_model cs model = true.

Definition imp_checker : Type := constraints -> constraint -> bool.

Definition imp_checker_snd (chkr : imp_checker) : Prop :=
  forall cs c,
    chkr cs c = true ->
    forall model, is_model cs model = true -> is_model_c c model = true.

Definition imp_checker_1 (cs: constraints) (c: constraint) : bool :=
  match cs with
  | [] => false
  | c'::cs' => if (eqc c' c) then true else false
  end.

Theorem imp_checker_1_snd : imp_checker_snd imp_checker_1.
Proof.
  unfold imp_checker_snd.
  intros cs c h.
  induction cs as [|c' cs' IHcs'].
  - discriminate.
  - intros model.
    simpl in h.
    destruct (eqc c' c) eqn:E.
  -- apply eqc_snd in E.
      simpl.

  Admitted.


End Constraints.

