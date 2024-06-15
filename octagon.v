Require Import Nat. 
Require Import Coq.NArith.NArith.
Open Scope bool_scope.

Require Import ZArith.
Open Scope Z_scope.

Require Import List.
Import ListNotations.

Require Import Lia.


Module Octagon.

Definition environment : Type := nat -> Z.

Definition pmUnit := { z : Z | z = 1 \/ z = - 1 }.

Lemma pmUnit_hprop : forall (z : Z) (p q :  z = 1 \/ z = -1 ), p = q.
Proof. 
  intros z p q. 
  destruct p, q; try lia.
  all: f_equal. all: eapply Logic.Eqdep_dec.UIP_dec.
  all: repeat decide equality.
  (* https://coq.inria.fr/doc/V8.17.1/stdlib/Coq.Logic.Eqdep_dec.html#UIP_dec *)
Qed. 

Definition opt_to_list{A: Type}(a: option A): list A :=
  match a with
  | Some a' => [a']
  | None => []
  end.

Module Term.
Declare Scope term_scope.
Delimit Scope term_scope with term.
Open Scope term_scope.

Record term := {a: pmUnit; x: nat}.
Program Definition eqb(t t': term) := 
  (t.(a) =? t'.(a))%Z && (t.(x) =? t'.(x))%nat.

Infix "=?" := eqb (at level 70) : term_scope.

Lemma eqb_refl(t: term) : (t =? t = true).
Proof. 
  unfold eqb.
  apply andb_true_intro.
  split.
  - apply Z.eqb_refl.
  - apply Nat.eqb_refl.
Qed. 

Lemma eqb_eq (t t': term): t = t' <-> (t =? t') = true.
Proof. 
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
Qed. 

Lemma eqb_spec(t t': term) : Bool.reflect (t = t') (t =? t').
Proof. 
  apply Bool.iff_reflect.
  exact (eqb_eq t t').
Qed. 

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

End Term. 

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
Proof. 
  destruct c; simpl.
  - rewrite (Term.eqb_refl l).
    rewrite (Term.eqb_refl r).
    rewrite (Z.eqb_refl d).
    reflexivity.
  - rewrite (Term.eqb_refl t).
    rewrite (Z.eqb_refl d).
    reflexivity.
Qed. 

Lemma eqb_eq(c c': Constraint) : (c = c') <-> (c =? c' = true).
Proof. 
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
Qed. 

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
Proof. 
  intros h.
  apply Bool.andb_true_iff in h.
  destruct h as [h Pe].
  split; try assumption.
  apply Bool.orb_true_iff in h.
  destruct h as [h | h].
  - left. apply Bool.andb_true_iff in h. assumption.
  - right. apply Bool.andb_true_iff in h. assumption.
Qed. 

Definition joined(c': Constraint)(cs: list Constraint) :=
  c' :: filter (fun c => negb (trivial_impl c' c)) cs.

Definition join(C C': list Constraint): list Constraint :=
  fold_left (fun cs c' => 
    if forallb (fun c => negb (trivial_impl c c')) cs
    then joined c' cs
    else cs
  ) C' C.

Definition normalize_constraint(c: Constraint): Constraint :=
   match c with
   | AddConstr l r d => 
       if      l =? r      then BndConstr l (d / 2)
       else c
   | c => c
   end.

Definition flatten(C: list Constraint): list Constraint :=
  map normalize_constraint C.

Definition flatten_is_nil(C: list Constraint): flatten C = [] <-> C = [].
Proof. 
  split; intros h; try (subst; reflexivity).
  unfold flatten in h.
  destruct C as [|c' C']; try reflexivity.
  simpl in h.
  unfold normalize_constraint in h.
  destruct c'; [ destruct (l =? r) | idtac ]; discriminate.
Qed. 

Definition new_constraints(C: list Constraint): list Constraint :=
  flat_map (fun c => flat_map (fun c' => opt_to_list(combine c c')) C) C.

Definition iterate(C: list Constraint) : list Constraint :=
  let C' := new_constraints C in
  let C'' := flatten C' in
  join C C''.

Definition model : Type := nat -> Z.

Definition term_value(m: model)(t: term): Z := proj1_sig t.(a) * (m t.(x)).

Lemma term_value_op(t: term)(m: model): term_value m (-t) =  (- (term_value m t))%Z.
Proof. 
  unfold term_value.
  destruct t as [a x].
  unfold Term.a.
  simpl.
  apply Z.mul_opp_l.
Qed. 

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

Definition imply(C: list Constraint)(c': Constraint) := 
  forall (m : model),
  satisfies_constraints m C = true -> satisfies_single_constraint m c' = true.
Infix "==>" := imply (at level 95, right associativity).

Definition implication(C: list Constraint)(C': list Constraint) :=
  forall m, satisfies_constraints m C = true -> satisfies_constraints m C' = true.
Infix "==>>" := implication (at level 96, right associativity).

Theorem implication_caract(C C': list Constraint) :
  (C ==>> C') <-> forall c', In c' C' -> (C ==> c').
Proof. 
  split.
  - intros C_sat_imp_C'_sat x x_in_C' m C_sat.
    pose proof (C_sat_imp_C'_sat m C_sat) as C'_sat.
    unfold satisfies_constraints in C'_sat.
    rewrite forallb_forall in C'_sat.
    exact (C'_sat x x_in_C').
  - intros C_imp_C' m C_sat.
    unfold implication in C_imp_C'.
    unfold satisfies_constraints.
    apply forallb_forall.
    intros x x_in_C'.
    apply (C_imp_C' x x_in_C' m).
    assumption.
Qed. 

Lemma nil_caract{A: Type}(ls: list A): (forall x, ~ In x ls) -> ls = [].
Proof. 
  intros no_mem_ls.
  destruct ls.
  - reflexivity.
  - specialize (no_mem_ls a0).
    exfalso.
    apply no_mem_ls.
    apply in_eq.
Qed. 

Lemma app_and_cons{A : Type}(x:A)(xs: list A): [x] ++ xs = x :: xs.
Proof. 
  auto.
Qed. 

Module ImplFacts. 
Lemma impl_trans(c c' c'': Constraint) : 
  (c --> c') -> (c' --> c'') -> (c --> c'').
Proof. 
  intros c_imp_c' c'_imp_c'' m.
  intros ? c_proof.
  exact (c'_imp_c'' m (c_imp_c' m c_proof)).
Qed. 

Theorem impls_more(C: list Constraint)(c c': Constraint) :
  (C ==> c) -> (c' :: C ==> c').
Proof. 
  intros C_imp_c m.
  unfold satisfies_constraints.
  apply Bool.andb_true_iff.
Qed. 

Lemma superset_preserves_implication(C C': list Constraint)(c: Constraint) :
  (forall x, In x C -> In x C') ->
  (C ==> c) -> (C' ==> c).
Proof. 
  intros C_subset_C' C_imp_c.
  destruct C' as [|c' C's] eqn:h.
  - simpl in C_subset_C'.
    pose proof (nil_caract C C_subset_C') as h'.
    subst. apply C_imp_c.
  - intros m.
    rewrite <- h; rewrite <- h in C_subset_C'.
    unfold imply in C_imp_c.

    specialize (C_imp_c m).
    intros C'_sat. apply C_imp_c.
    unfold satisfies_constraints.

    apply forallb_forall.
    intros x x_in_C.
    pose proof (C_subset_C' x x_in_C) as x_in_C'.

    unfold satisfies_constraints in C'_sat.
    assert (in_C'_sat: forall x0 : Constraint, In x0 C' -> satisfies_single_constraint m x0 = true).
    {
      apply forallb_forall.
      apply C'_sat.
    }
    apply in_C'_sat.
    exact x_in_C'.
Qed. 

Lemma order_does_not_matter(C C': list Constraint)(c: Constraint) :
  (forall x, In x C <-> In x C') ->
  (C ==> c) <-> (C' ==> c).
Proof. 
  intros same_elems.
  split.
  - apply superset_preserves_implication.
    intros x. apply same_elems.
  - apply superset_preserves_implication.
    intros x. apply same_elems.
Qed. 

Theorem impls_trans(C: list Constraint)(c c': Constraint) :
  (C ==> c) -> (c :: C ==> c') -> (C ==> c').
Proof. 
  intros C_imp_c c_C_imp_c'.
  intros m.
  specialize (C_imp_c m).
  specialize (c_C_imp_c' m).
  unfold satisfies_constraints.
  intros h.
  apply c_C_imp_c'.
  unfold satisfies_constraints.
  simpl.
  apply Bool.andb_true_iff.
  split; auto.
Qed. 

Lemma app_imp_l(C: list Constraint)(c c': Constraint):
  (C ==> c') -> (c ::C ==> c').
Proof. 
  intros C_imp_c' m.
  specialize (C_imp_c' m).
  intros h.
  apply Bool.andb_true_iff in h as [h h'].
  apply C_imp_c'.
  unfold satisfies_constraints.
  assumption.
Qed. 

Lemma app_implication_r(C C': list Constraint)(c': Constraint):
  (C ==>> c' :: C') -> (C ==>> C').
Proof. 
  intros C_imp_c' m C_sat.
  pose proof (C_imp_c' m C_sat) as c'_C'_sat.
  simpl in c'_C'_sat;
    apply Bool.andb_true_iff in c'_C'_sat as [c'_sat C'_sat].
  assumption.
Qed. 

Theorem implication_trans(C C' C'': list Constraint):
  (C ==>> C') -> (C' ==>> C'') -> (C ==>> C'').
Proof. 
  unfold implication.
  intros C_C' C'_C''.
  assert (h: (C ++ C' ==>> C'')). {
    intros m C_C'_sat; specialize (C_C' m); specialize (C'_C'' m).
    apply C'_C''.
    unfold satisfies_constraints in *.
    rewrite forallb_app in C_C'_sat.
    apply Bool.andb_true_iff in C_C'_sat as [C_sat C'_sat].
    assumption.
  }
  intros m; specialize (C_C' m); specialize (C'_C'' m).
  specialize (h m).
  unfold satisfies_constraints in h; rewrite forallb_app in h.
  intros C_sat.
  apply h.
  apply Bool.andb_true_iff.
  split; try assumption.
  exact (C_C' C_sat).
Qed. 

Theorem implication_refl(C: list Constraint):
  (C ==>> C).
Proof. 
  intros m C_sat; assumption.
Qed. 

End ImplFacts. 
Import ImplFacts.

Lemma add_constr_comm(l r: term)(d: Z) :
  AddConstr l r d --> AddConstr r l d.
Proof. 
  intros m. simpl.
  intros h.
  rewrite (Z.add_comm (term_value m r) (term_value m l)).
  assumption.
Qed. 

Lemma trivial_impl_is_implication(c c': Constraint) : 
  trivial_impl c c' = true -> (c --> c').
Proof. 
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
Qed. 

Lemma combine_addition_constraints(x y z t: Z)(d d': Z) :
  x + y <= d
  -> z + t <= d'
  -> x + y + z + t <= d + d'.
Proof. 
  intros h h'. 
  transitivity (x + y + (z + t)).
  - rewrite <- (Zplus_assoc_reverse _ (z) (t)).
    apply Z.le_refl.
  - apply (Zplus_le_compat _ _ _ _ h h').
Qed. 

Lemma combine_bound_constraints(x y:Z)(d d': Z):
  x <= d
  -> y <= d'
  -> x + y <= d + d'.
Proof. 
  intros h h'. 
  apply (Zplus_le_compat _ _ _ _ h h').
Qed. 

Lemma combine_mixed_constraints(x y z: Z)(d d': Z) :
  x + y <= d
  -> z <= d'
  -> x + y + z <= d + d'.
Proof. 
  intros h h'. 
  apply (Zplus_le_compat _ _ _ _ h h').
Qed. 

Lemma add_constr_are_commutable(l r: term)(d: Z) : 
  (AddConstr l r d)  --> (AddConstr r l d).
Proof. 
  intros m is_sat h.
  subst is_sat.
  simpl in *.
  rewrite (Z.add_comm (term_value m r) (term_value m l)).
  assumption.
Qed. 

Theorem combine_impl(c c' c'': Constraint) :
  combine c c' = Some c'' -> [c;c'] ==> c''.
Proof. 
  destruct c; destruct c' as [l' r' d' | t' d'].
  - unfold combine.
    destruct (l =?  - l') eqn:E.
   -- 
      intros h. injection h as h.
      apply Term.eqb_eq in E.
      subst c'' l.
      intros m.
      simpl.
      rewrite term_value_op.
      intros h.
      apply Bool.andb_true_iff in h as [h h'].
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
      rewrite term_value_op.
      intros h.
      apply Bool.andb_true_iff in h as [h h'].
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
       rewrite term_value_op.
       intros h.
       apply Bool.andb_true_iff in h as [h h'].
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
        rewrite term_value_op.
        intros h.
        apply Bool.andb_true_iff in h as [h h'].
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
     rewrite term_value_op.
     intros h.
     apply Bool.andb_true_iff in h as [h h'].
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
     rewrite term_value_op.
     intros h.
     apply Bool.andb_true_iff in h as [h h'].
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
     rewrite term_value_op.
     intros h.
     apply Bool.andb_true_iff in h as [h h'].
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
     rewrite term_value_op.
     intros h.
     apply Bool.andb_true_iff in h as [h h'].
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
    rewrite -> (Bool.andb_true_r _) in h'.

    apply Zle_is_le_bool.
    apply Zle_is_le_bool in h.
    apply Zle_is_le_bool in h'.
    apply (combine_bound_constraints _ _ _ _ h h').
Qed.


Print Z.
Print positive.
Search (nat -> Z).

Lemma scale_monotonous(x y: Z)(k: nat): 
  x <= y -> (Z.of_nat k * x <= Z.of_nat k*y).
Proof. 
  induction k as [| k' IHk']; intros x_le_y.
  - simpl. reflexivity.
  - rewrite Nat2Z.inj_succ.
    repeat rewrite Z.mul_succ_l.
    apply Z.add_le_mono; auto.
Qed. 

Theorem normalize_constraint_impl(c: Constraint):
  forall m, satisfies_single_constraint m c = true 
  <-> satisfies_single_constraint m (normalize_constraint c) = true.
Proof with auto. 
  intros m.
  unfold satisfies_single_constraint.
  destruct c...
  simpl. 
  destruct (l =? r) eqn:E.
  - apply eqb_eq in E; subst.
    split.
  -- intros h; apply Zle_is_le_bool in h.
     apply Zle_is_le_bool.
     rewrite Z.add_diag in h.
     apply (Z.div_le_mono _ _ 2) in h; try lia.
     rewrite (Z.mul_comm 2) in h.
     rewrite (Z.div_mul) in h; try (assumption || discriminate).
  -- intros h; apply Zle_is_le_bool in h.
     apply Zle_is_le_bool.
     rewrite Z.add_diag.
     apply (Z.mul_le_mono_nonneg_l _ _ 2) in h; try lia.
     apply Z.le_trans with (2*(d/2)); try lia.
     apply Z.mul_div_le; try lia.
  - simpl; apply iff_refl.
  - simpl; apply iff_refl.
Qed. 

Theorem flatten_impl(C: list Constraint)(c: Constraint) :
  (C ==> c) -> (flatten C ==> c).
Proof. 
  intros C_imp_c m.
  specialize (C_imp_c m).
  intros h.
  apply C_imp_c.
  unfold flatten in h.
  unfold satisfies_constraints in *.
  apply forallb_forall.
  rewrite forallb_forall in h.
  intros x x_in_C.
  apply (in_map normalize_constraint) in x_in_C.
  pose proof (h _ x_in_C) as h'.
  apply normalize_constraint_impl; assumption.
Qed. 

Theorem flatten_implication(C T: list Constraint):
  (C ==>> T) -> (C ==>> flatten T).
Proof. 
  intros C_imp_T m C_sat.
  pose proof (C_imp_T m C_sat) as T_sat.
  unfold satisfies_constraints in *.
  rewrite forallb_forall in *.
  unfold flatten.
  intros y y_in_flatten_T.
  apply in_map_iff in y_in_flatten_T as [x [x_y x_in_T]].
  subst.
  pose proof (T_sat x x_in_T) as x_sat.
  apply normalize_constraint_impl in x_sat.
  assumption.
Qed. 

Lemma joined_implication_l(C T: list Constraint)(c: Constraint):
  (C ==>> T) -> (joined c C ==>> T).
Proof. 
  intros C_imp_T m cC_sat.
  apply (C_imp_T m).
  unfold joined in cC_sat.
  simpl in cC_sat; apply Bool.andb_true_iff in cC_sat as [c_sat filtered_sat].
  unfold satisfies_constraints in *.
  rewrite forallb_forall in *.
  intros x x_in_C.
  destruct (negb (trivial_impl c x)) eqn:E.
  - apply filtered_sat.
    apply filter_In.
    split; try assumption.
  - apply Bool.negb_false_iff in E.
    apply trivial_impl_is_implication in E.
    specialize (E m) as c_sat_imp_x_sat.
    exact (c_sat_imp_x_sat c_sat).
Qed.

Theorem join_implication(C T: list Constraint):
  (C ==>> T) -> (C ==>> join C T).
Proof. 
  intros C_T m C_sat.
  pose proof (C_T m C_sat) as T_sat.
  unfold join.
  generalize dependent C.
  induction T as [|t ts].
  - intros __ _ C_sat. exact C_sat.
  - intros C C_T C_sat.
    simpl in *.
    apply Bool.andb_true_iff in T_sat as [t_sat ts_sat].
    specialize (IHts ts_sat).
    destruct (forallb (fun c : Constraint => negb (trivial_impl c t)) C) eqn:E.
  -- simpl.
     apply IHts.
  --- apply joined_implication_l. apply app_implication_r with t. assumption.
  --- unfold satisfies_constraints.
      unfold joined.
      apply forallb_forall.
      intros x [x_t | x_in_filtered].
  ---- subst; assumption.
  ---- apply filter_In in x_in_filtered as [x_in_C x_not_triv].
       unfold satisfies_constraints in C_sat.
       rewrite forallb_forall in C_sat.
       apply C_sat.
       assumption.
 -- apply IHts; try assumption.
    apply app_implication_r with t; assumption.
Qed. 

Theorem new_constraints_implication(C T: list Constraint):
  (C ==>> T) -> (C ==>> new_constraints T).
Proof.
  intros C_T m C_sat.
  pose proof (C_T m C_sat) as T_sat.
  unfold new_constraints.
  unfold satisfies_constraints.
  apply forallb_forall.
  intros x h.
  apply in_flat_map in h as [x1 [x1_T h]].
  apply in_flat_map in h as [x2 [x2_T x_is_combine]].
  destruct (combine x1 x2) eqn:E; try (simpl; exfalso; assumption).
  destruct x_is_combine as [h | []]; subst.
  apply (combine_impl x1 x2 x E).
  apply Bool.andb_true_iff.
  unfold satisfies_constraints in T_sat.
  rewrite forallb_forall in T_sat.
  split; try rewrite Bool.andb_true_r; auto.
Qed. 


Theorem iterate_implication(C: list Constraint):
  (C ==>> iterate C).
Proof. 
  apply join_implication.
  apply flatten_implication.
  apply new_constraints_implication.
  apply implication_refl.
Qed. 

Fixpoint church_numeral{A: Type}(n: nat)(f: A -> A)(x: A):=
  match n with
  | O => x
  | S m => f (church_numeral m f x)
  end.

Program Definition mkadd_pp(x: nat)(y: nat)(d: Z) :=
  AddConstr (Build_term 1 x) (Build_term 1 y) d.
Program Definition mkadd_pn(x: nat)(y: nat)(d: Z) :=
  AddConstr (Build_term 1 x) (Build_term (-1) y) d.
Program Definition mkadd_nn(x: nat)(y: nat)(d: Z) :=
  AddConstr (Build_term (-1) x) (Build_term (-1) y) d.
Program Definition mkbnd_p(x: nat)(d: Z) :=
  BndConstr (Build_term 1 x) d.
Program Definition mkbnd_n(x: nat)(d: Z) :=
  BndConstr (Build_term (-1) x) d.

Module ImplChecker.

Definition satisfies_constraint_disjuntion (m: model) (C: list (list Constraint)): bool :=
  existsb (satisfies_constraints m) C.


Record imp_checker: Type := 
  { imp_checker_fun: list (list Constraint) -> Constraint -> bool
  ; imp_checker_snd: forall (cs: list (list Constraint)) (c: Constraint),
     imp_checker_fun cs c = true -> forall model,
     satisfies_constraint_disjuntion model cs = true -> satisfies_single_constraint model c = true
  }.

Record conj_imp_checker: Type := 
  { conj_imp_checker_fun: list Constraint -> Constraint -> bool
    ; conj_imp_checker_snd: forall (cs: list Constraint) (c: Constraint),
    conj_imp_checker_fun cs c = true -> (cs ==> c)
  }.

Program Definition mk_imp_checker (checker: conj_imp_checker): imp_checker := {|
  imp_checker_fun cs c := 
    match cs with
    | [] => false
    | _ => forallb (fun conj => conj_imp_checker_fun checker conj c) cs
        (* We have that hypothesis A or hypothesis B are true, and have to prove that
           thesis C is true. We can only ensure that if A implies C and B implies C
        *)
    end
|}.
Next Obligation. 
  destruct checker as [checker checker_snd].
  rename H into full_checker__cs_imp_c.
  generalize dependent H0.
  induction cs as [|c' cs' IHcs']; try discriminate.
  simpl in full_checker__cs_imp_c.
  apply Bool.andb_true_iff in full_checker__cs_imp_c as [checker__c'_imp_c checker__cs'_imp_c].
  destruct cs' as [|c'' cs''] eqn:E; auto.
  - simpl.
    rewrite Bool.orb_false_r.
    apply checker_snd.
    assumption.
  - intros h; apply Bool.orb_true_iff in h as [c'_sat | E_sat].
  -- apply (checker_snd c' _ checker__c'_imp_c _).
     assumption.
  -- pose proof (IHcs' checker__cs'_imp_c) as IHcs'. 
     apply IHcs'.
     assumption.
Qed. 

Lemma implication_imp_implies(c c': Constraint)(cs: list Constraint):
  In c' cs -> (c' --> c) -> (cs ==> c).
Proof. 
  intros c'_in_cs c'_c m cs_sat.
  specialize (c'_c m).
  apply c'_c.
  unfold satisfies_constraints in cs_sat.
  rewrite forallb_forall in cs_sat.
  apply cs_sat.
  assumption.
Qed. 

Lemma implies_imply(c c': Constraint): (c --> c') <-> ([c] ==> c').
Proof. 
  split; intros c_c'.
  - intros m c_sat.
    specialize (c_c' m).
    simpl in c_sat.
    apply c_c'.
    rewrite Bool.andb_true_r in c_sat.
    assumption.
  - intros m is_sat c_sat.
    specialize (c_c' m).
    unfold is_sat.
    apply c_c'.
    simpl.
    rewrite Bool.andb_true_r.
    assumption.
Qed. 

Lemma imply_implication(cs: list Constraint)(c: Constraint): (cs ==> c) <-> (cs ==>> [c]).
Proof. 
  split; intros cs_c.
  - intros m cs_sat.
    specialize (cs_c m).
    simpl.
    rewrite Bool.andb_true_r.
    apply cs_c.
    assumption.
  - intros m cs_sat.
    specialize (cs_c m).
    simpl in cs_c.
    rewrite Bool.andb_true_r in cs_c.
    apply cs_c.
    assumption.
Qed. 

(* Lemma h''{A: Type}{P : A -> Prop}(f: A -> A): *)
(*   (forall x, P x -> P (f x)) -> *) 
(*   forall n x, P x -> P (church_numeral n f x). *)
(* Proof. *) 
(*   intros cs_imp_f_cs. *)
(*   intros n x h_Px. *)
(*   induction n as [|n' IHn']; try exact h_Px. *)
(*   simpl. *)
(*   apply cs_imp_f_cs. *)
(*   assumption. *)
(* Qed. *) 

Lemma church_numeral_implication
  (n: nat)(f: list Constraint -> list Constraint)(cs: list Constraint): 
    (forall C, C ==>> f C)
    -> cs ==>> church_numeral n f cs.
Proof. 
  intros cs_imp_f_cs.
  induction n as [|n' IHn']; try apply implication_refl.
  apply implication_trans with (church_numeral n' f cs); try assumption.
  apply cs_imp_f_cs.
Qed. 

Lemma imply_refl(cs: list Constraint)(c: Constraint)(c_in_cs: In c cs): cs ==> c.
Proof. 
  intros m cs_sat.
  unfold satisfies_constraints in cs_sat.
  rewrite forallb_forall in cs_sat.
  apply cs_sat.
  assumption.
Qed. 

Open Scope constr_scope.

Program Definition conj_trans_closure_checker(n: nat) : conj_imp_checker := {|
  conj_imp_checker_fun cs c := 
    let trans_closure := church_numeral n iterate cs 
    in existsb (fun c' => trivial_impl c' c) trans_closure
|}.
Next Obligation. 
(*
   Sea c' en trans_closure tal que c' --> c.
   Entonces tenemos:           cs ==>> iterate cs 
                       iterate cs ==> c'
                                c' --> c
   Por transitividad, cs ==> c
*)
  apply existsb_exists in H as [c' [c'_in_trans c'_imp_c]].
  apply trivial_impl_is_implication in c'_imp_c.
  apply implies_imply in c'_imp_c.
  apply imply_implication in c'_imp_c.
  apply imply_implication.

  assert(tcs_imp_c': church_numeral n iterate cs ==>> [c']). {
    apply imply_implication.
    apply imply_refl.
    assumption.
  }
  pose proof church_numeral_implication n iterate cs iterate_implication as cs_imp_tcs.
  pose proof implication_trans _ _ _ tcs_imp_c' c'_imp_c as tcs_imp_c.
  pose proof implication_trans _ _ _ cs_imp_tcs tcs_imp_c as cs_imp_c.
  assumption.
Qed. 

Program Definition trans_closure_checker(n: nat) : imp_checker := mk_imp_checker (conj_trans_closure_checker n).

End ImplChecker.


End Octagon.

Module OctagonExamples.
Local Definition cs := 
  [ Octagon.mkadd_pp 1 2  3 (* b + c <= 3 *)
  ; Octagon.mkadd_pn 2 1  2 (* c + -b <= 2 *)
  ; Octagon.mkadd_pp 3 4  1 (* d + e <= 1 *)
  ; Octagon.mkbnd_n    4 10 (* -e <= 10 *)
  ; Octagon.mkadd_nn 3 5  3 (* -d + -f <= 3 *)
].

Compute Octagon.church_numeral 1 Octagon.iterate cs.
Compute length (Octagon.church_numeral 1 Octagon.iterate cs).
Compute length (Octagon.church_numeral 2 Octagon.iterate cs).
Compute length (Octagon.church_numeral 3 Octagon.iterate cs).
Compute length (Octagon.church_numeral 4 Octagon.iterate cs).

Compute Octagon.combine (Octagon.mkadd_pp 1 2 10) (Octagon.mkadd_pn 3 2 10).

Import Octagon.ImplChecker.
Local Definition checker' := conj_imp_checker_fun (conj_trans_closure_checker (2 * length cs)) cs.

Compute checker' (Octagon.mkadd_pn 3 5 26).
Compute checker' (Octagon.mkadd_pn 3 5 25).
Compute negb (checker' (Octagon.mkadd_pn 3 5 24)).

Compute checker' (Octagon.mkadd_nn 5 4 24).
Compute checker' (Octagon.mkadd_nn 4 5 24).
Compute checker' (Octagon.mkadd_pn 3 5 25).
Compute checker' (Octagon.mkadd_pn 2 5 16).
Compute checker' (Octagon.mkadd_pn 2 4 12).
Compute checker' (Octagon.mkadd_pp 2 3 13).
Compute checker' (Octagon.mkadd_pn 3 4 21).
Compute checker' (Octagon.mkadd_pp 3 2 13).
Compute checker' (Octagon.mkbnd_n 5 14).
Compute checker' (Octagon.mkadd_pn 4 5 4).
Compute checker' (Octagon.mkbnd_p 3 11).
Compute checker' (Octagon.mkbnd_p 2 2).
Compute checker' (Octagon.mkadd_pp 1 2 3).
Compute checker' (Octagon.mkadd_pn 2 1 2).
Compute checker' (Octagon.mkadd_pp 3 4 1).
Compute checker' (Octagon.mkbnd_n 4 10).
Compute checker' (Octagon.mkadd_nn 3 5 3).

Local Definition C := 
  (* Obtained from [x4 = x5] *)
  [ Octagon.mkadd_pn 4 5 0   (*  x4 - x5 <= 0 *)
  ; Octagon.mkadd_pn 5 4 0   (*  x5 - x4 <= 0 *)
  (* Obtained from [x5 = 0] *)
  ; Octagon.mkbnd_p 5 0      (*  x5 <= 0*)
  ; Octagon.mkbnd_n 5 0      (* -x5 <= 0*)
  (* Obtained from [x0 >= x2 + 128] *)
  ; Octagon.mkadd_pn 2 0 (-128) (*  x2 - x0 <= -128 *)
].
Local Definition checker: Octagon.Constraint -> bool := 
  conj_imp_checker_fun (conj_trans_closure_checker (2 * length C)) C.

(* x4 = 0 *)
Compute checker (Octagon.mkbnd_p 4 0) && checker (Octagon.mkbnd_n 4 0).
(* x0 >= x2 + 32 *)
Compute checker (Octagon.mkadd_pn 2 0 (-32)).

Check (1 + 1)%N.
Check (1 + 1)%nat.


End OctagonExamples.

Module ForvesIntegration.
From FORVES2 Require Import constraints.
Require Import bbv.Word.

Definition translate_model(m :Constraints.assignment):
  Octagon.model :=
  fun (n: nat) => Z.of_N (wordToN( m n)).

Import Constraints.

Definition extract_values(l r: Constraints.cliteral):
  option nat * option nat * Z
  := match l, r with
     | C_VAR n, C_VAR n' => 
         (Some n, Some n',  0%Z)
     | C_VAR n, C_VAL d' => 
         (Some n,    None,  Z.of_N d')
     | C_VAR n, C_VAR_DELTA n' d' => 
         (Some n, Some n',  Z.of_N d')
     | C_VAL d, C_VAR n' => 
         (  None, Some n',            - Z.of_N d)
     | C_VAL d, C_VAL d' => 
         (  None,    None,  Z_of_N d' - Z.of_N d)
     | C_VAL d, C_VAR_DELTA n' d' => 
         (  None, Some n',  Z_of_N d' - Z.of_N d)
     | C_VAR_DELTA n d, C_VAR n' => 
         (Some n, Some n',            - Z.of_N d)
     | C_VAR_DELTA n d, C_VAL d' => 
         (Some n,    None,  Z_of_N d' - Z.of_N d)
     | C_VAR_DELTA n d, C_VAR_DELTA n' d' => 
         (Some n, Some n',  Z_of_N d' - Z.of_N d)
     end.

Definition translate_le(values: option nat * option nat * Z):
  Octagon.Constraint :=
  match values with
  | (None  ,    None, d) => Octagon.mkadd_pn 1 1 d
  | (Some n,    None, d) => Octagon.mkbnd_p n  d
  | (None  , Some n', d) => Octagon.mkbnd_n n' d
  | (Some n, Some n', d) => Octagon.mkadd_pn n n' d
  end.

Definition translate_constraint(c: Constraints.constraint):
  list Octagon.Constraint :=
  match c with
  | C_LE l r => [translate_le (extract_values l r)]
  | C_LT l r => let '(n, n', d) := extract_values l r in
                [translate_le (n, n', d-1)]
                (* l < r <-> l <= r-1 *)
  | C_EQ l r => let '(n, n', d) := extract_values l r in
                [translate_le (n, n', d); translate_le(n', n, -d)]
                (* l = r <-> l <= r /\ r <= l *)
  end.

Lemma translate_constraint_lt_to_le(l r: Constraints.cliteral):
  (* l < r  -> l + 1 <= r*)
  translate_constraint (C_LT l r) = 
     match l with
     | C_VAR n => translate_constraint (C_LE (C_VAR_DELTA n 1) r)
     | C_VAL d => translate_constraint (C_LE (C_VAL (d+1)) r)
     | C_VAR_DELTA n d => translate_constraint (C_LE (C_VAR_DELTA n (d+1)) r)
     end.
Proof.
  destruct l.
  - destruct r; simpl; f_equal.
  - destruct r; simpl; f_equal; f_equal; lia.
  - destruct r; simpl; f_equal; f_equal; lia.
Qed.

Lemma translate_constraint_eq_to_le(l r: Constraints.cliteral):
  (* l < r  -> l + 1 <= r*)
  translate_constraint (C_EQ l r) = 
  translate_constraint (C_LE l r) ++  translate_constraint (C_LE r l).
Proof.
  destruct l eqn:E; destruct r eqn:E'; simpl; f_equal; f_equal; f_equal; lia.
Qed.

Lemma lt_to_le_for_Z(a b: Z): a < b -> a <= b - 1.
Proof. lia. Qed.

Lemma eq_to_le_for_Z(a b: Z): a = b -> a <= b /\ b <= a.
Proof. lia. Qed.

Lemma le_from_N_to_Z(x y: N):(x <= y)%N <-> (Z.of_N x <= Z.of_N y).
Proof. lia. Qed.

Lemma lt_from_N_to_Z(x y: N):(x < y)%N -> (Z.of_N x < Z.of_N y).
Proof. lia. Qed.

Lemma eq_from_N_to_Z(x y: N):(x = y)%N <-> (Z.of_N x = Z.of_N y).
Proof. lia. Qed.

Lemma le_pass_term_right(x y: Z): x <= y <-> x - y <= 0.
Proof. lia. Qed.

Lemma le_pass_term_right'(x y z: Z): x + y <= z <-> x <= z - y.
Proof. lia. Qed.

Lemma term_value_on_tranlate_model(m: Constraints.assignment)(t: Octagon.Term.term):
  Octagon.term_value (translate_model m) t =  
  let '(Octagon.Term.Build_term a x) := t in
  Z.of_N (wordToN (m x)) *(
    if proj1_sig a >? 0 
    then  1
    else -1
   ).
Proof.
  destruct t; destruct a as [a pa]; simpl.
  destruct pa as [a_1 | a_m1].
  - subst; unfold Octagon.term_value; unfold translate_model; simpl.
    rewrite Z.mul_1_r.
    destruct (wordToN (m x)); auto.
  - subst; unfold Octagon.term_value; unfold translate_model; simpl.
    rewrite <- Z.opp_eq_mul_m1.
    destruct (wordToN (m x)); auto.
Qed.

Lemma translate_le_preserves_information
  (m: Constraints.assignment)(l r: Constraints.cliteral):
  let m_opt := translate_model m in
  Constraints.satisfies_single_constraint m (Constraints.C_LE l r) = true <->
  Octagon.satisfies_single_constraint m_opt (translate_le (extract_values l r)) = true.
Proof.
  simpl.
  rewrite N.leb_le.
  destruct l as [n|d|n d]; destruct r as [n'|d'|n' d'];
    split; unfold cliteral_to_nat; intros h;
    simpl in *;
    repeat rewrite -> term_value_on_tranlate_model in *;
    simpl in *;
    lia.
Qed.

Lemma translate_constraint_preserves_information(c: Constraints.constraint) :
  forall (m: Constraints.assignment),
    let m_oct := translate_model m in
      Constraints.satisfies_single_constraint m c = true <->
      Octagon.satisfies_constraints m_oct (translate_constraint c) = true.
Proof.
  intros m; simpl.
  destruct c.
  - rewrite translate_constraint_lt_to_le.
    unfold Octagon.satisfies_constraints.
    destruct l;
      unfold translate_constraint;
      unfold forallb;
      rewrite Bool.andb_true_r;
      rewrite <- translate_le_preserves_information;
      simpl; rewrite N.ltb_lt; rewrite N.leb_le;
      lia.
  - rewrite translate_constraint_eq_to_le.
    unfold Octagon.satisfies_constraints.
    unfold translate_constraint.
    rewrite Octagon.app_and_cons.
    unfold forallb.
    rewrite Bool.andb_true_r.
    rewrite Bool.andb_true_iff.
    rewrite <- translate_le_preserves_information.
    rewrite <- translate_le_preserves_information.
    simpl; rewrite N.eqb_eq; repeat rewrite N.leb_le; lia.
  - 
    unfold Octagon.satisfies_constraints.
    unfold translate_constraint.
    unfold forallb.
    rewrite Bool.andb_true_r.
    rewrite <- translate_le_preserves_information.
    reflexivity.
Qed.

Definition translate_constraints(cs: Constraints.conjunction):
  list Octagon.Constraint := flat_map translate_constraint cs.

Lemma translate_preserves_information(m: Constraints.assignment)(C: list Constraints.constraint) :
    let m_oct := translate_model m in
    let C_oct := translate_constraints C in
      Constraints.satisfies_conjunction m C = true <->
      Octagon.satisfies_constraints m_oct C_oct = true.
Proof.
  induction C as [|c cs IHcs]; try reflexivity.
  unfold satisfies_conjunction in *.
  unfold Octagon.satisfies_constraints in *.
  simpl.
  rewrite forallb_app.
  repeat rewrite Bool.andb_true_iff.
  rewrite <- IHcs.
  apply and_iff_compat_r.
  apply translate_constraint_preserves_information.
Qed.

Check forallb.

Program Definition translate_conj_imp_checker
  (oct_checker: Octagon.ImplChecker.conj_imp_checker)
  : Constraints.conj_imp_checker := {|
  conj_imp_checker_fun cs c :=
    let oct_hypotothesis := translate_constraints cs in
    let oct_thesis := translate_constraint c in
    let oct_checker_fn := 
      Octagon.ImplChecker.conj_imp_checker_fun oct_checker
    in
    forallb (oct_checker_fn oct_hypotothesis) oct_thesis
|}.
Next Obligation.
  unfold conj_imply.
  intros model H0.
  rename H0 into c_sat.
  destruct oct_checker as [oct_checker_fn oct_checker_snd].
  simpl in H.
  apply translate_constraint_preserves_information.
  unfold Octagon.imply in oct_checker_snd.
  unfold Octagon.satisfies_constraints.
  rewrite forallb_forall in *.
  intros t t_in_tc.
  specialize (H t t_in_tc).
  remember (translate_constraints cs) as hs.
  apply (oct_checker_snd hs t H (translate_model model)).
  rewrite Heqhs.
  rewrite <- translate_preserves_information.
  assumption.
Qed.


Program Definition conj_trans_closure_checker (n: nat)
  : Constraints.conj_imp_checker :=
  translate_conj_imp_checker (Octagon.ImplChecker.conj_trans_closure_checker n).

End ForvesIntegration.

