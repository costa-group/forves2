Require Import FORVES2.constants.
Import Constants.

Require Import Nat.
Require Import bbv.Word.


Module SHA3.

(*

A type for a function that implements the sha3 operation. It basically
recieves a memory slot (sequence of bytes) and returns and EVMWord.

*)

Definition sha3_op : Type := forall (n : nat), word (n*8) -> EVMWord.

(*

Since we do implement an SHA3 operation, but rather all our proofs
will be done wrt any such operation, it is convenient to assume some
facts about such implementations.

 *)
Definition sha3_op_assumptions (f : sha3_op ) : Prop :=
    True.


(*

  A dummy implementation of sha3, just to be used when testing the
  concrete interpreter. Thus the proof that it satisfies
  sha3_op_assumptions is simply admitted.

*)

Definition dummy_sha3 : sha3_op := fun _ _ => WZero.

Lemma dummy_sha3_assumptions: sha3_op_assumptions dummy_sha3.
  Admitted.


End SHA3.
