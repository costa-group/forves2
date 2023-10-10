(**

This file includes facts related to an execution states (as defined in
the file execution_state.v)

**)

Require Import FORVES2.execution_state.
Import ExecutionState.

Require Import Coq.Logic.FunctionalExtensionality.

Module ExecutionStateFacts.
  
(* A state is equal to itself *)
Lemma eq_execution_states_refl:
  forall (st: state), eq_execution_states st st.
Proof.
  intros.
  unfold eq_execution_states.
  intuition. (* this proves the stack and context equivalence *)
  + unfold eq_memory. intro. reflexivity.
  + unfold eq_storage. intro. reflexivity.
Qed.


(*

States equivalence -> states equality. This requires the functional
extension, which is consistent.

TODO: later change _ext (which stands for functional extension) to
something more meaningful, like _eq

*)
Lemma eq_execution_states_ext:
  forall (st st': state),
    eq_execution_states st st' -> st = st'.
Proof.
  intros st st' H_eq.
  destruct st eqn:E_st.
  destruct st' eqn:E_st'.
  unfold eq_execution_states in H_eq.
  simpl in H_eq.
  destruct H_eq as [H_eq_stack [H_eq_mem [H_eq_strg H_eq_ext]]].

  unfold eq_stack in H_eq_stack.
  rewrite H_eq_stack.
  unfold eq_memory in H_eq_mem.
  apply functional_extensionality in H_eq_mem.
  rewrite H_eq_mem.
  unfold eq_storage in H_eq_strg.
  apply functional_extensionality in H_eq_strg. (* functional extension *)
  rewrite H_eq_strg.
  unfold eq_externals in H_eq_ext.
  rewrite H_eq_ext.
  reflexivity.
Qed.

(* Equal states have stack of the same length *)
Lemma eq_execution_states_stack_len:
  forall st st',
    eq_execution_states st st' ->
    length (get_stack_st st) = length (get_stack_st st').
Proof.
  intros st st' H_eq_states.
  apply eq_execution_states_ext in H_eq_states.
  rewrite H_eq_states.
  reflexivity.
Qed.

(* memory is preserved when updating the stack *)
Lemma memory_preserved_when_updating_stack_st:
  forall st stk,
    get_memory_st (set_stack_st st stk) = get_memory_st st.
Proof.
  destruct st.
  reflexivity.
Qed.

(* storage is preserved when updating the stack *)
Lemma storage_preserved_when_updating_stack_st:
  forall st stk,
    get_storage_st (set_stack_st st stk) = get_storage_st st.
Proof.
  destruct st.
  reflexivity.
Qed.

(* externals is preserved when updating the stack *)
Lemma context_preserved_when_updating_stack_st:
  forall st stk,
    get_externals_st (set_stack_st st stk) = get_externals_st st.
Proof.
  destruct st.
  reflexivity.
Qed.

(* setting the stack to 'stk', and then get it will return 'stk' *)
Lemma set_and_then_get_stack_st:
  forall st stk,
    get_stack_st (set_stack_st st stk) = stk.
Proof.
  destruct st.
  reflexivity.
Qed.

End ExecutionStateFacts.
