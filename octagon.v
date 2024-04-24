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

Record term := {a: pmUnit; x: nat}.
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

Definition new_constraints(C: list Constraint): list Constraint :=
  flat_map (fun c => flat_map (fun c' => opt_to_list(combine c c')) C) C.

Definition iterate(C: list Constraint) : list Constraint :=
  let C' := new_constraints C in
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

Definition imply(C: list Constraint)(c': Constraint) := 
  (* match C with *)
  (* | [] => False *)
  (* |  _ =>*) forall (m : model),
  satisfies_constraints m C = true -> satisfies_single_constraint m c' = true
  (*end*).
Infix "==>" := imply (at level 95, right associativity).

Definition implication(C: list Constraint)(C': list Constraint) :=
  (forall m, satisfies_constraints m C = true -> satisfies_constraints m C' = true).
Infix "==>>" := implication (at level 96, right associativity).

Theorem implication_caract(C C': list Constraint) :
  (C ==>> C') <-> forall c', In c' C' -> (C ==> c').
Proof. (* {{{ *)
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

Lemma app_and_cons{A : Type}(x:A)(xs: list A): [x] ++ xs = x :: xs.
Proof. (* {{{ *)
  auto.
Qed. (* }}} *)

Module ImplFacts. (* {{{ *)
Lemma impl_trans(c c' c'': Constraint) : 
  (c --> c') -> (c' --> c'') -> (c --> c'').
Proof. (* {{{ *)
  intros c_imp_c' c'_imp_c'' m.
  intros ? c_proof.
  exact (c'_imp_c'' m (c_imp_c' m c_proof)).
Qed. (* }}} *)

(* Lemma nil_not_impl(c: Constraint): ~ ([] ==> c). *)
(* Proof. (1* {{{ *1) *)
(*   auto. *)
(* Qed. (1* }}} *1) *)

(* Lemma nil_implies_nil: [] ==>> []. *)
(* Proof. (1* {{{ *1) *)
(*   intros x abs; auto. *)
(* Qed. (1* }}} *1) *)

(* Lemma nil_implied_only_by_nil(C: list Constraint): *)
(*   C ==>> [] -> C = []. *)
(* Proof. (1* {{{ *1) *)
(*   intros C_imp_nil. *)

(* Qed. (1* }}} *1) *)

Theorem impls_more(C: list Constraint)(c c': Constraint) :
  (C ==> c) -> (c' :: C ==> c').
Proof. (* {{{ *)
  intros C_imp_c m.
  unfold satisfies_constraints.
  apply Bool.andb_true_iff.
Qed. (* }}} *)

Lemma superset_preserves_implication(C C': list Constraint)(c: Constraint) :
  (forall x, In x C -> In x C') ->
  (C ==> c) -> (C' ==> c).
Proof. (* {{{ *)
  intros C_subset_C' C_imp_c.
  destruct C' as [|c' C's] eqn:h.
  - simpl in C_subset_C'.
    pose proof (nil_caract C C_subset_C') as h'.
    subst. apply C_imp_c.
  - intros m.
    rewrite <- h; rewrite <- h in C_subset_C'.
    unfold imply in C_imp_c.
    (* rewrite <- h' in C_imp_c; rewrite <- h' in C_subset_C'. *)
    specialize (C_imp_c m).
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

Theorem impls_trans(C: list Constraint)(c c': Constraint) :
  (C ==> c) -> (c :: C ==> c') -> (C ==> c').
Proof. (* {{{ *)
  intros C_imp_c c_C_imp_c'.
  (* destruct C eqn:E; try *) 
  (*   (apply nil_not_impl in C_imp_c; destruct C_imp_c). *)
  intros m.
  specialize (C_imp_c m).
  specialize (c_C_imp_c' m).
  (* rewrite <- E in *. *)
  unfold satisfies_constraints.
  intros h.
  apply c_C_imp_c'.
  unfold satisfies_constraints.
  simpl.
  apply Bool.andb_true_iff.
  split; auto.
Qed. (* }}} *)

Lemma app_imp_l(C: list Constraint)(c c': Constraint):
  (C ==> c') -> (c ::C ==> c').
Proof. (* {{{ *)
  intros C_imp_c' m.
  (* destruct C as [|x xs]; try (exfalso; assumption). *)
  specialize (C_imp_c' m).
  intros h.
  apply Bool.andb_true_iff in h as [h h'].
  apply C_imp_c'.
  unfold satisfies_constraints.
  assumption.
Qed. (* }}} *)

Lemma app_implication_r(C C': list Constraint)(c': Constraint):
  (C ==>> c' :: C') -> (C ==>> C').
Proof. (* {{{ *)
  intros C_imp_c' m C_sat.
  pose proof (C_imp_c' m C_sat) as c'_C'_sat.
  simpl in c'_C'_sat;
    apply Bool.andb_true_iff in c'_C'_sat as [c'_sat C'_sat].
  assumption.
Qed. (* }}} *)

Theorem implication_trans(C C' C'': list Constraint):
  (C ==>> C') -> (C' ==>> C'') -> (C ==>> C'').
Proof. (* {{{ *)
  unfold implication.
  intros C_C' C'_C''.
  assert (h: (C ++ C' ==>> C'')). {
    intros m C_C'_sat; specialize (C_C' m); specialize (C'_C'' m).
    apply C'_C''.
    Check forallb_app.
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
Qed. (* }}} *)

Theorem implication_refl(C: list Constraint):
  (C ==>> C).
Proof. (* {{{ *)
  intros m C_sat; assumption.
Qed. (* }}} *)

End ImplFacts. (* }}} *)
Import ImplFacts.

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
  forall m, satisfies_single_constraint m c = true 
  <-> satisfies_single_constraint m (normalize_constraint c) = true.
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

Theorem flatten_impl(C: list Constraint)(c: Constraint) :
  (C ==> c) -> (flatten C ==> c).
Proof. (* {{{ *)
  intros C_imp_c m.
  specialize (C_imp_c m).
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

Theorem flatten_implication(C T: list Constraint):
  (C ==>> T) -> (C ==>> flatten T).
Proof. (* {{{ *)
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
Qed. (* }}} *)

Lemma joined_implication_l(C T: list Constraint)(c: Constraint):
  (C ==>> T) -> (joined c C ==>> T).
Proof. (* {{{ *)
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
  - Search (negb ?b = false).
    apply Bool.negb_false_iff in E.
    apply trivial_impl_is_implication in E.
    specialize (E m) as c_sat_imp_x_sat.
    exact (c_sat_imp_x_sat c_sat).
Qed.
(* }}} *)

(* Lemma join_In(C T: list Constraint): *)
(*   forall x, In x (join C T) -> *) 
(*   forall c, In c (join C T) -> x = c \/ ~ (c --> x) \/ ~ (x --> c). *)

Theorem join_implication(C T: list Constraint):
  (C ==>> T) -> (C ==>> join C T).
Proof. (* {{{ *)
  intros C_T m C_sat.
  pose proof (C_T m C_sat) as T_sat.
  unfold join.
  (* Check fold_left. *)
  generalize dependent C.
  induction T as [|t ts].
  - intros __ _ C_sat. exact C_sat.
  - intros C C_T C_sat.
    (* Search fold_left. *)
    (* Check fold_left_app. *)
    simpl in *.
    apply Bool.andb_true_iff in T_sat as [t_sat ts_sat].
    specialize (IHts ts_sat).
    destruct (forallb (fun c : Constraint => negb (trivial_impl c t)) C) eqn:E.
  -- simpl.
     apply IHts.
  --- apply joined_implication_l. apply app_implication_r with t. assumption.
  --- 
      unfold satisfies_constraints.
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
Qed. (* }}} *)

Theorem new_constraints_implication(C T: list Constraint):
  (C ==>> T) -> (C ==>> new_constraints T).
Proof.
  (* {{{ *)
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
Qed. (* }}} *)


Theorem iterate_implication(C T: list Constraint):
  (C ==>> iterate C).
Proof. (* {{{ *)
  apply join_implication.
  apply flatten_implication.
  apply new_constraints_implication.
  apply implication_refl.
Qed. (* }}} *)

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
End Octagon.

Local Definition cs := 
  [ Octagon.mkadd_pp 1 2 3
  ; Octagon.mkadd_pn 2 1 2
  ; Octagon.mkadd_pp 3 4 1
  ; Octagon.mkbnd_n    4 10
  ; Octagon.mkadd_nn 3 5 3
].

Compute Octagon.church_numeral 1 Octagon.iterate cs.
Compute length (Octagon.church_numeral 1 Octagon.iterate cs).
Compute length (Octagon.church_numeral 2 Octagon.iterate cs).
Compute length (Octagon.church_numeral 3 Octagon.iterate cs).
Compute length (Octagon.church_numeral 4 Octagon.iterate cs).

Compute Octagon.combine (Octagon.mkadd_pp 1 2 10) (Octagon.mkadd_pn 3 2 10).

