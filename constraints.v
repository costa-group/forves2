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

Inductive constraint : Type :=
  | C_GT (l r : cliteral)
  | C_LE (l r : cliteral)
  | C_EQ (l r : cliteral).

Definition constraints : Type := list constraint.

Definition assignment : Type := nat -> EVMWord.

Definition is_model_c (c : constraint) (model : assignment) : bool :=
  true.

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


End Constraints.

