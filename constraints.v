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

Definition is_sat_assignment_c (c : constraint) (v : assignment) : bool :=
  true.

Fixpoint is_sat_assignment (cs : constraints) (v : assignment) : bool :=
  match cs with
  | [] => true
  | c::cs' => if (is_sat_assignment_c c v) then is_sat_assignment cs' v else false
  end.

Definition is_sat (cs : constraints) :=
  true.

Definition imp_checker : Type := constraints -> constraint -> bool.

Definition imp_checker_snd (chkr : imp_checker) : Prop :=
  forall cs c,
    chkr cs c = true ->
    forall v, is_sat_assignment cs v = true -> is_sat_assignment_c c v = true.


End Constraints.
