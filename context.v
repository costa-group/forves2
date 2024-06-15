Require Import List.
Import ListNotations.
Require Import bbv.Word.
Require Import Nat. 
Require Import Coq.NArith.NArith.
 
Require Import FORVES2.octagon.
Import Octagon.

Require Import FORVES2.constraints.
Import Constraints.

Module Context.


  Record ctx_t : Type := 
    {
      ctx_cs : constraints;
      ctx_imp_chkr: imp_checker
    }.

  Inductive available_imp_chkr :=
  | ImpChkr_Trivial
  | ImpChkr_Oct.

  Definition compute_n_iter_for_oct (cs : constraints) :=
    (fold_right (fun l n => (max (length l) n)) 0 cs).
  
  Definition get_impl_chkr (tag: available_imp_chkr) (cs: constraints) : imp_checker :=
    match tag with
    | ImpChkr_Trivial => inclusion_imp_checker
    | ImpChkr_Oct => mk_imp_checker (ForvesIntegration.conj_trans_closure_checker (compute_n_iter_for_oct cs))
    end.

  Definition mk_ctx (imp_chkr: imp_checker) (cs: constraints) : ctx_t :=
    {|
      ctx_cs := cs;
      ctx_imp_chkr := imp_chkr
    |}.
  
End Context.



