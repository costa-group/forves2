Require Import List. 
Import ListNotations.
Require Import bbv.Word.
Require Import Nat. 
Require Import Coq.NArith.NArith.
 
Require Import FORVES2.octagon.
Import Octagon.

Require Import FORVES2.constraints.
Import Constraints.

Require Import FORVES2.symbolic_state.
Import SymbolicState.

Module Context.


  Record ctx_t : Type := 
    {
      ctx_cs : constraints;
      ctx_imp_chkr: imp_checker
    }.

  Inductive available_imp_chkr :=
  | ImpChkr_Dummy
  | ImpChkr_Syntactic
  | ImpChkr_Oct.

  Definition compute_n_iter_for_oct (cs : constraints) :=
    (fold_right (fun l n => (max (length l) n)) 0 cs).
  
  Definition get_impl_chkr (tag: available_imp_chkr) (cs: constraints) : imp_checker :=
    match tag with
    | ImpChkr_Dummy => dummy_imp_checker
    | ImpChkr_Syntactic => inclusion_imp_checker
    | ImpChkr_Oct => mk_imp_checker (ForvesIntegration.conj_trans_closure_checker (compute_n_iter_for_oct cs))
    end.

  Definition mk_ctx (imp_chkr: imp_checker) (cs: constraints) : ctx_t :=
    {|
      ctx_cs := cs;
      ctx_imp_chkr := imp_chkr
    |}.



Definition sstack_val_to_cliteral (sv : sstack_val) : option cliteral :=
  match sv with
  | Val w => Some (C_VAL (wordToN w))
  | InVar n => Some (C_VAR n)
  | _ => None
  end.

Definition sstack_val_to_cliteral_w_shift (sv : sstack_val) (shift: N) : option cliteral :=
  match sv with
  | Val w => Some (C_VAL ((wordToN w) + shift))
  | InVar n => Some (C_VAR_DELTA n shift)
  | _ => None
  end.


Definition sstack_val_to_cliteral_smap (sv : sstack_val) (maxidx: nat) (bs : sbindings) : option cliteral :=
  match follow_in_smap sv maxidx bs with
  | Some (FollowSmapVal (SymBasicVal sv') _ _) => sstack_val_to_cliteral sv'
  | _ => None
  end.



Definition chk_eq_wrt_ctx (ctx: ctx_t) (sv1 sv2: sstack_val) :=
  let imp_chkr := imp_checker_fun (ctx_imp_chkr ctx) in
  let cs := ctx_cs ctx in
  let ocl1 := sstack_val_to_cliteral sv1 in
  let ocl2 := sstack_val_to_cliteral sv2 in
  match ocl1, ocl2 with
  | Some cl1, Some cl2 => imp_chkr cs  (C_EQ cl1 cl2)
  | _, _ => false
  end.

Definition chk_lt_wrt_ctx (ctx: ctx_t) (sv1 sv2: sstack_val) :=
  let imp_chkr := imp_checker_fun (ctx_imp_chkr ctx) in
  let cs := ctx_cs ctx in
  let ocl1 := sstack_val_to_cliteral sv1 in
  let ocl2 := sstack_val_to_cliteral sv2 in
  match ocl1, ocl2 with
  | Some cl1, Some cl2 => imp_chkr cs  (C_LT cl1 cl2)
  | _, _ => false
  end.


Definition chk_lt_wrt_ctx_smap (ctx: ctx_t) (sv1 sv2: sstack_val) (maxidx: nat) (bs : sbindings) :=
  let imp_chkr := imp_checker_fun (ctx_imp_chkr ctx) in
  let cs := ctx_cs ctx in
  let ocl1 := sstack_val_to_cliteral_smap sv1 maxidx bs in
  let ocl2 := sstack_val_to_cliteral_smap sv2 maxidx bs in
  match ocl1, ocl2 with
  | Some cl1, Some cl2 => imp_chkr cs  (C_LT cl1 cl2)
  | _, _ => false
  end.

Definition chk_neq_wrt_ctx (ctx: ctx_t) (sv1 sv2: sstack_val) :=
  if chk_lt_wrt_ctx ctx sv1 sv2 then true else chk_lt_wrt_ctx ctx sv2 sv1.

Definition chk_lt_lshift_wrt_ctx (ctx: ctx_t) (sv1 sv2: sstack_val) (shift: N) :=
  let imp_chkr := imp_checker_fun (ctx_imp_chkr ctx) in
  let cs := ctx_cs ctx in
  let ocl1 := sstack_val_to_cliteral_w_shift sv1 shift in
  let ocl2 := sstack_val_to_cliteral sv2 in
  match ocl1, ocl2 with
  | Some cl1, Some cl2 => imp_chkr cs (C_LT cl1 cl2)
  | _, _ => false
  end.

Definition chk_lt_rshift_wrt_ctx (ctx: ctx_t) (sv1 sv2: sstack_val) (shift: N) :=
  let imp_chkr := imp_checker_fun (ctx_imp_chkr ctx) in
  let cs := ctx_cs ctx in
  let ocl1 := sstack_val_to_cliteral sv1 in
  let ocl2 := sstack_val_to_cliteral_w_shift sv2 shift in
  match ocl1, ocl2 with
  | Some cl1, Some cl2 => imp_chkr cs (C_LT cl1 cl2)
  | _, _ => false
  end.

Definition chk_lt_lrshift_wrt_ctx (ctx: ctx_t) (sv1 sv2: sstack_val) (shift1: N) (shift2: N) :=
  let imp_chkr := imp_checker_fun (ctx_imp_chkr ctx) in
  let cs := ctx_cs ctx in
  let ocl1 := sstack_val_to_cliteral_w_shift sv1 shift1 in
  let ocl2 := sstack_val_to_cliteral_w_shift sv2 shift2 in
  match ocl1, ocl2 with
  | Some cl1, Some cl2 => imp_chkr cs (C_LT cl1 cl2)
  | _, _ => false
  end.


Definition chk_le_wrt_ctx (ctx: ctx_t) (sv1 sv2: sstack_val) :=
  let imp_chkr := imp_checker_fun (ctx_imp_chkr ctx) in
  let cs := ctx_cs ctx in
  let ocl1 := sstack_val_to_cliteral sv1 in
  let ocl2 := sstack_val_to_cliteral sv2 in
  match ocl1, ocl2 with
  | Some cl1, Some cl2 => imp_chkr cs  (C_LE cl1 cl2)
  | _, _ => false
  end.

Definition chk_le_lshift_wrt_ctx (ctx: ctx_t) (sv1 sv2: sstack_val) (shift: N) :=
  let imp_chkr := imp_checker_fun (ctx_imp_chkr ctx) in
  let cs := ctx_cs ctx in
  let ocl1 := sstack_val_to_cliteral_w_shift sv1 shift in
  let ocl2 := sstack_val_to_cliteral sv2 in
  match ocl1, ocl2 with
  | Some cl1, Some cl2 => imp_chkr cs (C_LE cl1 cl2)
  | _, _ => false
  end.

Definition chk_le_rshift_wrt_ctx (ctx: ctx_t) (sv1 sv2: sstack_val) (shift: N) :=
  let imp_chkr := imp_checker_fun (ctx_imp_chkr ctx) in
  let cs := ctx_cs ctx in
  let ocl1 := sstack_val_to_cliteral sv1 in
  let ocl2 := sstack_val_to_cliteral_w_shift sv2 shift in
  match ocl1, ocl2 with
  | Some cl1, Some cl2 => imp_chkr cs (C_LE cl1 cl2)
  | _, _ => false
  end.

Definition chk_le_lrshift_wrt_ctx (ctx: ctx_t) (sv1 sv2: sstack_val) (shift1: N) (shift2: N) :=
  let imp_chkr := imp_checker_fun (ctx_imp_chkr ctx) in
  let cs := ctx_cs ctx in
  let ocl1 := sstack_val_to_cliteral_w_shift sv1 shift1 in
  let ocl2 := sstack_val_to_cliteral_w_shift sv2 shift2 in
  match ocl1, ocl2 with
  | Some cl1, Some cl2 => imp_chkr cs (C_LE cl1 cl2)
  | _, _ => false
  end.


End Context.



