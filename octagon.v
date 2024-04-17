Require Import Nat. 
Require Import Coq.NArith.NArith.
Open Scope bool_scope.

Require Import ZArith.
(* Require Import Ring. *)
Open Scope Z_scope.

Require Import List.
Import ListNotations.

Require Import Lia.


Module Octagon.

Definition environment : Type := nat -> Z.

Definition pmUnit := { z : Z | z = 1 \/ z = - 1 }.

Lemma pmUnit_hprop : forall (z : Z) (p q :  z = 1 \/ z = -1 ), p = q.
Proof. (* {{{ *)
  intros z p q. 
  destruct p, q; try lia.
  all: f_equal. all: eapply Logic.Eqdep_dec.UIP_dec.
  (* Decidable equality on Z should be somewhere in the standard library but I could not immediately find it *)
  all: repeat decide equality.
  (* https://coq.inria.fr/doc/V8.17.1/stdlib/Coq.Logic.Eqdep_dec.html#UIP_dec *)
Qed. (* }}} *)

Definition opt_to_list{A: Type}(a: option A): list A :=
  match a with
  | Some a' => [a']
  | None => []
  end.

Module Term. (*{{{ *)
Declare Scope term_scope.
Delimit Scope term_scope with term.
Open Scope term_scope.

Record term := {a: pmUnit;x: nat}.
Program Definition eqb(t t': term) := 
  (t.(a) =? t'.(a))%Z && (t.(x) =? t'.(x))%nat.

(* Program Definition t: term := {| a := 1; x:= 1|}. *)
(* Program Definition t': term := {| a := -1; x:= 2|}. *)

Infix "=?" := eqb (at level 70) : term_scope.

Lemma eqb_refl(t: term) : (t =? t = true).
Proof. (* {{{ *)
  unfold eqb.
  apply andb_true_intro.
  split.
  - apply Z.eqb_refl.
  - apply Nat.eqb_refl.
Qed. (* }}} *)

Lemma eqb_eq (t t': term): t = t' <-> (t =? t') = true.
Proof. (* {{{ *)
  split.
  - intros t_t'. subst. apply eqb_refl.
  - destruct t as [a x]; destruct t' as [a' x'].
    intros h.
    apply andb_prop in h as [a_eqb_a' x_eqb_x'].
    simpl in a_eqb_a'.
    apply Z.eqb_eq in a_eqb_a'.
    apply (eq_sig_hprop pmUnit_hprop) in a_eqb_a'.
    simpl in x_eqb_x'.
    apply Nat.eqb_eq in x_eqb_x'.
    subst a' x'.
    reflexivity.
Qed. (* }}} *)

Lemma eqb_spec(t t': term) : Bool.reflect (t = t') (t =? t').
Proof. (* {{{ *)
  apply Bool.iff_reflect.
  exact (eqb_eq t t').
Qed. (* }}} *)

Program Definition op(t: term) := 
  {| a := - t.(a)
  ;  x := t.(x)
  |}.
Next Obligation.
  destruct (a t) as [av [h | h']]; subst.
  - right. reflexivity.
  - left. reflexivity.
Qed.
Notation "'-' t" := (op t) (at level 35, right associativity): term_scope.

End Term. (* }}} *)

Import Term.

Inductive Constraint :=
 | AddConstr (l r: term)(d: Z)
 | BndConstr (t: term)(d: Z).

Module ConstraintEq.
Declare Scope constr_scope.
Delimit Scope constr_scope with constr.
Open Scope constr_scope.

Definition eqb(c c': Constraint): bool :=
  match c, c' with
  | AddConstr l r d, AddConstr l' r' d' => ((l =? l') && (r =? r') && (d =? d')%Z)%term
  | BndConstr t d, BndConstr t' d' => ((t =? t') && (d =? d')%Z)%term
  | _, _ => false
  end.
Infix "=?" := eqb (at level 70) : constr_scope.

Lemma eqb_refl(c: Constraint): c =? c = true.
Proof. (* {{{ *)
  destruct c; simpl.
  - rewrite (Term.eqb_refl l).
    rewrite (Term.eqb_refl r).
    rewrite (Z.eqb_refl d).
    reflexivity.
  - rewrite (Term.eqb_refl t).
    rewrite (Z.eqb_refl d).
    reflexivity.
Qed. (* }}} *)

Lemma eqb_eq(c c': Constraint) : (c = c') <-> (c =? c' = true).
Proof. (* {{{ *)
  split.
  - intros h. subst. apply eqb_refl.
  - intros c_c'.
    destruct c; destruct c' as [l' r' d' | t' d']; try discriminate; simpl in c_c'.
    -- apply Bool.andb_true_iff in c_c' as [ht d_d'].
       apply Bool.andb_true_iff in ht as [l_l' r_r'].
       apply Term.eqb_eq in l_l'.
       apply Term.eqb_eq in r_r'.
       apply Z.eqb_eq in d_d'.
       subst; reflexivity.
    -- apply Bool.andb_true_iff in c_c' as [t_t' d_d'].
       apply Term.eqb_eq in t_t'.
       apply Z.eqb_eq in d_d'.
       subst; reflexivity.
Qed. (* }}} *)

Definition eqb_spec(c c': Constraint) : Bool.reflect (c = c') (c =? c') :=
  Bool.iff_reflect _ _ (eqb_eq _ _).

End ConstraintEq.
Definition combine(c c': Constraint): option Constraint :=
  match c, c' with
  | AddConstr l r d, AddConstr l' r' d' =>
      if      l =? (op l') then Some (AddConstr r r' (d + d'))
      else if l =? (op r') then Some (AddConstr r l' (d + d'))
      else if r =? (op l') then Some (AddConstr l r' (d + d'))
      else if r =? (op r') then Some (AddConstr l l' (d + d'))
      else None
  | AddConstr l r d, BndConstr t' d' =>
      if      l =? (op t') then Some (BndConstr r (d + d'))
      else if r =? (op t') then Some (BndConstr l (d + d'))
      else None
  | BndConstr t d, AddConstr l' r' d' =>
      if      l' =? (op t) then Some (BndConstr r' (d + d'))
      else if r' =? (op t) then Some (BndConstr l' (d + d'))
      else None
  | BndConstr t d, BndConstr t' d' => Some (AddConstr t t' (d + d'))
  end.

Definition trivial_impl(c c': Constraint): bool :=
  match c, c' with
  | AddConstr l r d, AddConstr l' r' d' => 
      ((l =? l') && (r =? r') || (l =? r') && (r =? l')) && (d <=? d')%Z
  | BndConstr t d, BndConstr t' d' => (t =? t') && (d <=? d')%Z
  | _, _ => false
  end.

Lemma destruct_aoaa(a b c d e: bool) :
  (a && b || c && d) && e = true -> (a = true /\ b = true \/ c = true /\ d = true) /\ e = true.
Proof. (* {{{ *)
  intros h.
  apply Bool.andb_true_iff in h.
  destruct h as [h Pe].
  split; try assumption.
  apply Bool.orb_true_iff in h.
  destruct h as [h | h].
  - left. apply Bool.andb_true_iff in h. assumption.
  - right. apply Bool.andb_true_iff in h. assumption.
Qed. (* }}} *)

(* Compute (fold_left (fun x y => x + y) [1;2;3] 0). *)

Definition join(C C': list Constraint): list Constraint :=
  fold_left (fun cs c' => 
    if forallb (fun c => negb (trivial_impl c c')) cs
    then c' :: filter (fun c => negb (trivial_impl c' c)) cs
    else cs
  ) C' C.

Definition normalize_constraint(c: Constraint): Constraint :=
   match c with
   | AddConstr l r d => 
       if      l =? r      then BndConstr l (d / 2)
       (* else if l =? - r then (1* Delete these constraints *1) *)
       (* NOTE: While it would be useful to delete these constraints, since if it's satisifiable
          then we can assume them to be of the sort 0 <= k for k natural, we don't include
          a proof that the constraints are satisifiable, so for now it just complicates the
          proof. It suffices that we normalize AddConstr t t d to BndConstr t (d/2) for now,
          since this guarantees that flatten C = [] <-> C = [] *)
       else c
   | c => c
   end.

Definition flatten(C: list Constraint): list Constraint :=
  map normalize_constraint C.

Definition flatten_is_nil(C: list Constraint): flatten C = [] <-> C = [].
Proof. (* {{{ *)
  split; intros h; try (subst; reflexivity).
  unfold flatten in h.
  destruct C as [|c' C']; try reflexivity.
  simpl in h.
  unfold normalize_constraint in h.
  destruct c'; [ destruct (l =? r) | idtac ]; discriminate.
Qed. (* }}} *)

Definition iterate(C: list Constraint) : list Constraint :=
  let C' := flat_map (fun c => flat_map (fun c' => opt_to_list(combine c c')) C) C in
  let C'' := flatten C' in
  join C C''.

Definition model : Type := nat -> Z.

Definition term_value(m: model)(t: term): Z := proj1_sig t.(a) * (m t.(x)).

Lemma term_value_op(t: term)(m: model): term_value m (-t) =  (- (term_value m t))%Z.
Proof. (* {{{ *)
  unfold term_value.
  destruct t as [a x].
  unfold Term.a.
  simpl.
  Print Scope Z_scope.
  Search Z.opp.
  apply Z.mul_opp_l.
Qed. (* }}} *)

Definition satisfies_single_constraint (m: model) (c: Constraint): bool :=
  match c with 
  | AddConstr l r d => term_value m l + term_value m r <=? d
  | BndConstr t d => term_value m t <=? d
  end.

Definition satisfies_constraints (m: model) (C: list Constraint): bool :=
  forallb (satisfies_single_constraint m) C.

Definition implies(c c': Constraint) := forall (m : model),
  let is_sat := satisfies_single_constraint m in
  is_sat c = true -> is_sat c' = true.
Infix "-->" := implies (at level 90, right associativity).

Definition imply(C: list Constraint)( c': Constraint) := forall (m : model),
  match C with
  | [] => False
  |  _ => satisfies_constraints m C = true -> satisfies_single_constraint m c' = true
  end.
Infix "==>" := imply (at level 95, right associativity).

Lemma add_constr_comm(l r: term)(d: Z) :
  AddConstr l r d --> AddConstr r l d.
Proof. (* {{{ *)
  intros m. simpl.
  intros h.
  rewrite (Z.add_comm (term_value m r) (term_value m l)).
  assumption.
Qed. (* }}} *)

Lemma trivial_impl_is_implication(c c': Constraint) : 
  trivial_impl c c' = true -> (c --> c').
Proof. (* {{{ *)
  intros c_ti_c' m.
  destruct c; destruct c' as [l' r' d'| t' d']; try (discriminate || unfold satisfies_single_constraint).
  - intros h.
    unfold trivial_impl in c_ti_c'.
    apply destruct_aoaa in c_ti_c' as [[[l_l' r_r'] | [l_r' r_l']] d_le_d'].
  -- apply Term.eqb_eq in l_l'.
     apply Term.eqb_eq in r_r'.
     subst l' r'.

     apply Zle_is_le_bool in d_le_d'.
     apply Zle_is_le_bool in h.
     apply Zle_is_le_bool.

     apply (Z.le_trans _ _ _ h d_le_d').

  -- apply Term.eqb_eq in l_r'.
     apply Term.eqb_eq in r_l'.
     subst l' r'.

     apply Zle_is_le_bool in d_le_d'.
     apply Zle_is_le_bool in h.
     apply Zle_is_le_bool.

     rewrite (Z.add_comm (term_value m r) (term_value m l)).

     apply (Z.le_trans _ _ _ h d_le_d').

  - unfold trivial_impl in c_ti_c'.
    apply Bool.andb_true_iff in c_ti_c' as [t_t' d_le_d'].

    apply Term.eqb_eq in t_t'.
    subst t'.
    intros h.

    apply Zle_is_le_bool in d_le_d'.
    apply Zle_is_le_bool in h.
    apply Zle_is_le_bool.

    apply (Z.le_trans _ _ _ h d_le_d').
Qed. (* }}} *)

Lemma impl_trans(c c' c'': Constraint) : 
  (c --> c') -> (c' --> c'') -> (c --> c'').
Proof. (* {{{ *)
  intros c_imp_c' c'_imp_c'' m.
  intros ? c_proof.
  exact (c'_imp_c'' m (c_imp_c' m c_proof)).
Qed. (* }}} *)

Theorem impls_more(C: list Constraint)(c c': Constraint) :
  (C ==> c) -> (c' :: C ==> c').
Proof. (* {{{ *)
  intros C_imp_c m.
  unfold satisfies_constraints.
  apply Bool.andb_true_iff.
Qed. (* }}} *)

Lemma combine_addition_constraints(x y z t: Z)(d d': Z) :
  x + y <= d
  -> z + t <= d'
  -> x + y + z + t <= d + d'.
Proof. (* {{{ *)
  intros h h'. 
  Search (?x <=? ?y = true -> ?x + ?n <=? ?y + ?n = true).
  Check Zplus_le_compat.
  Check Zplus_le_compat_r.
  transitivity (x + y + (z + t)).
  - 
    Search ( ?x + ?y + ?z = ?x + (?y + ?z)).
    Check Zplus_assoc_reverse.
    rewrite <- (Zplus_assoc_reverse _ (z) (t)).
    apply Z.le_refl.
  - 
  apply (Zplus_le_compat _ _ _ _ h h').
Qed. (* }}} *)

Lemma combine_bound_constraints(x y:Z)(d d': Z):
  x <= d
  -> y <= d'
  -> x + y <= d + d'.
Proof. (* {{{ *)
  intros h h'. 
  apply (Zplus_le_compat _ _ _ _ h h').
Qed. (* }}} *)

Lemma combine_mixed_constraints(x y z: Z)(d d': Z) :
  x + y <= d
  -> z <= d'
  -> x + y + z <= d + d'.
Proof. (* {{{ *)
  intros h h'. 
  apply (Zplus_le_compat _ _ _ _ h h').
Qed. (* }}} *)

Lemma nil_caract{A: Type}(ls: list A): (forall x, ~ In x ls) -> ls = [].
Proof. (* {{{ *)
  intros no_mem_ls.
  destruct ls.
  - reflexivity.
  - specialize (no_mem_ls a0).
    exfalso.
    apply no_mem_ls.
    Search (In ?x  (?x :: ?l)).
    apply in_eq.
Qed. (* }}} *)

Lemma superset_preserves_implication(C C': list Constraint)(c: Constraint) :
  (forall x, In x C -> In x C') ->
  (C ==> c) -> (C' ==> c).
Proof. (* {{{ *)
  intros C_subset_C' C_imp_c m.
  specialize (C_imp_c m).
  destruct C' as [|c' C's] eqn:h.
  - simpl in C_subset_C'.
    pose proof (nil_caract C C_subset_C') as h'.
    subst. apply C_imp_c.
  - rewrite <- h; rewrite <- h in C_subset_C'.
    destruct C eqn:h'; try (exfalso; apply C_imp_c).
    rewrite <- h' in C_imp_c; rewrite <- h' in C_subset_C'.
    intros C'_sat. apply C_imp_c.
    unfold satisfies_constraints.
    Search forallb.

    apply forallb_forall.
    intros x x_in_C.
    pose proof (C_subset_C' x x_in_C) as x_in_C'.

    unfold satisfies_constraints in C'_sat.
    assert (in_C'_sat: forall x0 : Constraint, In x0 C' -> satisfies_single_constraint m x0 = true).
    {
      Check forallb_forall.
      apply forallb_forall.
      apply C'_sat.
    }
    apply in_C'_sat.
    exact x_in_C'.
Qed. (* }}} *)

Lemma order_does_not_matter(C C': list Constraint)(c: Constraint) :
  (forall x, In x C <-> In x C') ->
  (C ==> c) <-> (C' ==> c).
Proof. (* {{{ *)
  intros same_elems.
  split.
  - apply superset_preserves_implication.
    intros x. apply same_elems.
  - apply superset_preserves_implication.
    intros x. apply same_elems.
Qed. (* }}} *)

Lemma add_constr_are_commutable(l r: term)(d: Z) : 
  (AddConstr l r d)  --> (AddConstr r l d).
Proof. (* {{{ *)
  intros m is_sat h.
  subst is_sat.
  simpl in *.
  rewrite (Z.add_comm (term_value m r) (term_value m l)).
  assumption.
Qed. (* }}} *)

(*
| AddConstr l r d, AddConstr l' r' d' =>
    if      l =? (op l') then Some (AddConstr r r' (d + d'))
*)

(* Lemma rule1(l r r': term)(d d': Z): *)
(*   [AddConstr l r d; AddConstr (-r) r' d'] ==> AddConstr l r' (d + d'). *)
(* Proof. *)
(*   intros m. simpl. *)
(*   Check term_value_op. *)
(*   rewrite term_value_op. *)
(*   intros h. apply Bool.andb_true_iff in h as [h h']. *)
(*   rewrite Bool.andb_true_r in h'. *)
(* Admitted. *)

(* Ltac trial1 := *)
(*   match goal with *)
(*   | [ A : ?x + ?y <=? ?d |- _] => idtac *)
(*   end. *)

(* Ltac my_add_constr := *)
(*   match goal with *)
(*   | [ A : ?x + ?y <=? ?d |- _] *)
(*   | [ A : ?y + ?x <=? ?d |- _] => *)
(*       match goal with *)
(*       | [ A' : -?x +  ?z <=? ?d' |- ] *)
(*       | [ A' :  ?z + -?x <=? ?d' |- ] => *) 
(*          match goal with *)
(*            | [ |- ?y + ?z <=? (?d + ?d') ] *)
(*            | [ |- ?z + ?y <=? (?d + ?d') ] => *) 
(*                transitivity (- ?x + ?z + ?x + ?y); *) 
(*                [ lia *) 
(*                | apply (combine_addition_constraints _ _ _ _ _ _ A A') *)
(*                ] *)
(*          end *)
(*       end *)
(*   end. *)

(*   | [ B : ?x <=? ?d *) 
(*       |- ?z <=? (?d + ?d') *)
(*       ] => *)
(*       match goal with *)
(*       | [ A' : - ?x + ?z <=? ?d' ] *)
(*       | [ A' :   ?z + -?x <=? ?d' ] => *) 
(*           transitivity (?x + - ?x + ?z); *)
(*           [ lia *)
(*           | apply ( *)
(*           ] *)
(*       | [ B' : ?y <=? ?d' ] => *)
(*       end *)
(*   end. *)

Theorem combine_impl(c c' c'': Constraint) :
  combine c c' = Some c'' -> [c;c'] ==> c''.
Proof. (* {{{ *)
  destruct c; destruct c' as [l' r' d' | t' d'].
  - unfold combine.
    destruct (l =?  - l') eqn:E.
   -- 
      intros h. injection h as h.
      apply Term.eqb_eq in E.
      subst c'' l.
      intros m.
      simpl.
      Check term_value_op.
      rewrite term_value_op.
      intros h.
      apply Bool.andb_true_iff in h as [h h'].
      Search (?x && true).
      rewrite -> (Bool.andb_true_r _) in h'.

      apply Zle_is_le_bool.
      apply Zle_is_le_bool in h.
      apply Zle_is_le_bool in h'.
      transitivity (- term_value m l' + term_value m r + term_value m l' + term_value m r').
  --- lia.
  --- apply (combine_addition_constraints _ _ _ _ _ _ h h').
   -- destruct E. destruct (l =? - r') eqn:E.
  --- intros h. injection h as h.
      apply Term.eqb_eq in E.
      subst c'' l.
      intros m.
      simpl.
      Check term_value_op.
      rewrite term_value_op.
      intros h.
      apply Bool.andb_true_iff in h as [h h'].
      Search (?x && true).
      rewrite -> (Bool.andb_true_r _) in h'.

      apply Zle_is_le_bool.
      apply Zle_is_le_bool in h.
      apply Zle_is_le_bool in h'.
      transitivity (- term_value m r' + term_value m r + term_value m l' + term_value m r').
  ---- lia.
  ---- apply (combine_addition_constraints _ _ _ _ _ _ h h').
  --- destruct E. destruct (r =? - l') eqn:E.
  ---- intros h. injection h as h.
       apply Term.eqb_eq in E.
       subst c'' r.
       intros m.
       simpl.
       Check term_value_op.
       rewrite term_value_op.
       intros h.
       apply Bool.andb_true_iff in h as [h h'].
       (* Search (?x && true). *)
       rewrite -> (Bool.andb_true_r _) in h'.

       apply Zle_is_le_bool.
       apply Zle_is_le_bool in h.
       apply Zle_is_le_bool in h'.
       transitivity (term_value m l + - term_value m l' + term_value m l' + term_value m r').
       + lia.
       + apply (combine_addition_constraints _ _ _ _ _ _ h h').
  ---- destruct E. destruct (r =? - r') eqn:E.
  ----- intros h. injection h as h.
        apply Term.eqb_eq in E.
        subst c'' r.
        intros m.
        simpl.
        Check term_value_op.
        rewrite term_value_op.
        intros h.
        apply Bool.andb_true_iff in h as [h h'].
        (* Search (?x && true). *)
        rewrite -> (Bool.andb_true_r _) in h'.

        apply Zle_is_le_bool.
        apply Zle_is_le_bool in h.
        apply Zle_is_le_bool in h'.
        transitivity (term_value m l + - term_value m r' + term_value m l' + term_value m r').
        + lia.
        + apply (combine_addition_constraints _ _ _ _ _ _ h h').
  ----- discriminate.
  - unfold combine.
    destruct (l =? - t') eqn:E.
  -- intros h. injection h as h.
     apply Term.eqb_eq in E.
     subst c'' l.
     intros m.
     simpl.
     Check term_value_op.
     rewrite term_value_op.
     intros h.
     apply Bool.andb_true_iff in h as [h h'].
     (* Search (?x && true). *)
     rewrite -> (Bool.andb_true_r _) in h'.

     apply Zle_is_le_bool.
     apply Zle_is_le_bool in h.
     apply Zle_is_le_bool in h'.
     transitivity (- term_value m t' + term_value m r + term_value m t').
     + lia.
     + apply (combine_mixed_constraints _ _ _ _ _ h h').
  -- destruct E. destruct (r =? -t') eqn:E.
  --- intros h. injection h as h.
     apply Term.eqb_eq in E.
     subst c'' r.
     intros m.
     simpl.
     Check term_value_op.
     rewrite term_value_op.
     intros h.
     apply Bool.andb_true_iff in h as [h h'].
     (* Search (?x && true). *)
     rewrite -> (Bool.andb_true_r _) in h'.

     apply Zle_is_le_bool.
     apply Zle_is_le_bool in h.
     apply Zle_is_le_bool in h'.
     transitivity (term_value m l + - term_value m t' + term_value m t').
     + lia.
     + apply (combine_mixed_constraints _ _ _ _ _ h h').
  --- discriminate.
  - unfold combine.
    destruct (l' =? -t) eqn:E.
  -- intros h. injection h as h.
     apply Term.eqb_eq in E.
     subst c'' l'.
     intros m.
     simpl.
     Check term_value_op.
     rewrite term_value_op.
     intros h.
     apply Bool.andb_true_iff in h as [h h'].
     (* Search (?x && true). *)
     rewrite -> (Bool.andb_true_r _) in h'.

     apply Zle_is_le_bool.
     apply Zle_is_le_bool in h.
     apply Zle_is_le_bool in h'.
     transitivity (- term_value m t + term_value m r' + term_value m t).
     + lia.
     + rewrite (Z.add_comm d).
       apply (combine_mixed_constraints _ _ _ _ _ h' h).
  -- destruct E. destruct (r' =? -t) eqn:E.
  --- intros h. injection h as h.
     apply Term.eqb_eq in E.
     subst c'' r'.
     intros m.
     simpl.
     Check term_value_op.
     rewrite term_value_op.
     intros h.
     apply Bool.andb_true_iff in h as [h h'].
     (* Search (?x && true). *)
     rewrite -> (Bool.andb_true_r _) in h'.

     apply Zle_is_le_bool.
     apply Zle_is_le_bool in h.
     apply Zle_is_le_bool in h'.
     transitivity (term_value m l' + - term_value m t + term_value m t).
     + lia.
     + rewrite (Z.add_comm d).
       apply (combine_mixed_constraints _ _ _ _ _ h' h).
  --- discriminate.
  - unfold combine.
    intros h. injection h as h. subst.
    intros m h.
    apply Bool.andb_true_iff in h as [h h'].
    (* Search (?x && true). *)
    rewrite -> (Bool.andb_true_r _) in h'.

    apply Zle_is_le_bool.
    apply Zle_is_le_bool in h.
    apply Zle_is_le_bool in h'.
    apply (combine_bound_constraints _ _ _ _ h h').
Qed.
(* }}} *)

Theorem impls_trans(C: list Constraint)(c c': Constraint) :
  (C ==> c) -> (c :: C ==> c') -> (C ==> c').
Proof. (* {{{ *)
  intros C_imp_c c_C_imp_c' m.
  specialize (C_imp_c m).
  specialize (c_C_imp_c' m).
  destruct C eqn:E; try congruence.
  rewrite <- E in *.
  unfold satisfies_constraints.
  intros h.
  apply c_C_imp_c'.
  unfold satisfies_constraints.
  simpl.
  apply Bool.andb_true_iff.
  split; auto.
Qed. (* }}} *)

Print Z.
Print positive.
Search (nat -> Z).

Lemma scale_monotonous(x y: Z)(k: nat): 
  x <= y -> (Z.of_nat k * x <= Z.of_nat k*y).
Proof. (* {{{ *)
  induction k as [| k' IHk']; intros x_le_y.
  - simpl. reflexivity.
  - Search (Z.of_nat).
    rewrite Nat2Z.inj_succ.
    Search (Z.succ).
    Check Z.mul_succ_l.
    repeat rewrite Z.mul_succ_l.
    Search (?x + ?y <= ?z + ?t).
    Check Z.add_le_mono.
    apply Z.add_le_mono; auto.
Qed. (* }}} *)

Theorem normalize_constraint_impl(c: Constraint):
  forall m, satisfies_single_constraint m c = true <-> satisfies_single_constraint m (normalize_constraint c) = true.
Proof with auto. (* {{{ *)
  intros m.
  unfold satisfies_single_constraint.
  destruct c...
  simpl. 
  Search (?x <-> ?x).

  destruct (l =? r) eqn:E.
  - apply eqb_eq in E; subst.
    split.
  -- intros h; apply Zle_is_le_bool in h.
     apply Zle_is_le_bool.
     rewrite Z.add_diag in h.
     Search (?x <= ?y -> ?x / ?k <= ?y / ?k).
     apply (Z.div_le_mono _ _ 2) in h; try lia.
     Search (?x * ?y = ?y * ?x).
     rewrite (Z.mul_comm 2) in h.
     Search (?x * ?k / ?k).
     rewrite (Z.div_mul) in h; try (assumption || discriminate).
  -- intros h; apply Zle_is_le_bool in h.
     apply Zle_is_le_bool.
     rewrite Z.add_diag.
     Search (?x <= ?y -> ?k * ?x  <= ?k * ?y).
     apply (Z.mul_le_mono_nonneg_l _ _ 2) in h; try lia.
     apply Z.le_trans with (2*(d/2)); try lia.
     apply Z.mul_div_le; try lia.
  - simpl; apply iff_refl.
  - simpl; apply iff_refl.
Qed. (* }}} *)

Lemma app_imp(C: list Constraint)(c c': Constraint):
  (C ==> c') -> (c ::C ==> c').
Proof. (* {{{ *)
  intros C_imp_c' m.
  specialize (C_imp_c' m).
  destruct C as [|x xs]; try (exfalso; assumption).
  intros h.
  apply Bool.andb_true_iff in h as [h h'].
  apply C_imp_c'.
  unfold satisfies_constraints.
  assumption.
Qed. (* }}} *)

Theorem flatten_impl(C: list Constraint)(c: Constraint) :
  (C ==> c) -> (flatten C ==> c).
Proof. (* {{{ *)
  intros C_imp_c m.
  specialize (C_imp_c m).
  destruct C eqn:E; try (exfalso; assumption).
  rewrite <- E in *.
  destruct (flatten C) eqn:E'.
  - rewrite E in E'. discriminate.
  - rewrite <- E' in *.
    intros h.
    apply C_imp_c.
    unfold flatten in h.
    unfold satisfies_constraints in *.
    apply forallb_forall.
    rewrite forallb_forall in h.
    intros x x_in_C.
    Check in_map.
    apply (in_map normalize_constraint) in x_in_C.
    pose proof (h _ x_in_C) as h'.
    apply normalize_constraint_impl; assumption.
Qed. (* }}} *)

(* NOTE: I should probably define the concept of "loses no information"
         or "can be derived from" and reword the properties I want in
         terms of these. So, if C =*=> C' means that with C I can derive
         all of C', then we have to show that C =*=> (iterate C), which
         is just showing the same thing for join, flatten and the nexted
         flatmap with combine.
         C =*=> C' can probably be forall c, In c C', (C ==> c)
*)
(* TODO: Rename flatten *)

Theorem iterate_impl(C: list Constraint):
  forall c, In c (iterate C) -> (C ==> c).
Proof.
  intros c.
  (* unfold iterate. *)

Qed.

End Octagon.





