Require Import List.
Import ListNotations.

Require Import FORVES2.optimizations_def.
Import Optimizations_Def.

Require Import FORVES2.optimizations.add_zero.
Import Opt_add_zero.
Require Import FORVES2.optimizations.eval.
Import Opt_eval.
Require Import FORVES2.optimizations.sub_x_x.
Import Opt_sub_x_x.
Require Import FORVES2.optimizations.not_not.
Import Opt_not_not.
Require Import FORVES2.optimizations.and_and.
Import Opt_and_and.
Require Import FORVES2.optimizations.and_origin.
Import Opt_and_origin.
Require Import FORVES2.optimizations.mul_shl.
Import Opt_mul_shl.
Require Import FORVES2.optimizations.div_shl.
Import Opt_div_shl.
Require Import FORVES2.optimizations.shr_zero_x.
Import Opt_shr_zero_x.
Require Import FORVES2.optimizations.shr_x_zero.
Import Opt_shr_x_zero.
Require Import FORVES2.optimizations.eq_zero.
Import Opt_eq_zero.
Require Import FORVES2.optimizations.and_zero.
Import Opt_and_zero.
Require Import FORVES2.optimizations.div_one.
Import Opt_div_one.
Require Import FORVES2.optimizations.lt_x_one.
Import Opt_lt_x_one.
Require Import FORVES2.optimizations.gt_one_x.
Import Opt_gt_one_x.
Require Import FORVES2.optimizations.and_address.
Import Opt_and_address.
Require Import FORVES2.optimizations.mul_one.
Import Opt_mul_one.
Require Import FORVES2.optimizations.iszero_gt.
Import Opt_iszero_gt.
Require Import FORVES2.optimizations.eq_iszero.
Import Opt_eq_iszero.
Require Import FORVES2.optimizations.and_caller.
Import Opt_and_caller.
(*Require Import FORVES2.optimizations.iszero3.
Import Opt_iszero3.
Require Import FORVES2.optimizations.add_sub.
Import Opt_add_sub.
Require Import FORVES2.optimizations.shl_zero_x.
Import Opt_shl_zero_x.
Require Import FORVES2.optimizations.sub_zero.
Import Opt_sub_zero.
Require Import FORVES2.optimizations.shl_x_zero.
Import Opt_shl_x_zero.
Require Import FORVES2.optimizations.mul_zero.
Import Opt_mul_zero.
Require Import FORVES2.optimizations.div_x_x.
Import Opt_div_x_x.
Require Import FORVES2.optimizations.div_zero.
Import Opt_div_zero.
Require Import FORVES2.optimizations.mod_one.
Import Opt_mod_one.
Require Import FORVES2.optimizations.mod_zero.
Import Opt_mod_zero.
Require Import FORVES2.optimizations.mod_x_x.
Import Opt_mod_x_x.
Require Import FORVES2.optimizations.exp_x_zero.
Import Opt_exp_x_zero.
Require Import FORVES2.optimizations.exp_x_one.
Import Opt_exp_x_one.
Require Import FORVES2.optimizations.exp_one_x.
Import Opt_exp_one_x.
Require Import FORVES2.optimizations.exp_zero_x.
Import Opt_exp_zero_x.
Require Import FORVES2.optimizations.exp_two_x.
Import Opt_exp_two_x.
Require Import FORVES2.optimizations.gt_zero_x.
Import Opt_gt_zero_x.
Require Import FORVES2.optimizations.gt_x_x.
Import Opt_gt_x_x.
Require Import FORVES2.optimizations.lt_x_zero.
Import Opt_lt_x_zero.
Require Import FORVES2.optimizations.lt_x_x.
Import Opt_lt_x_x.
Require Import FORVES2.optimizations.eq_x_x.
Import Opt_eq_x_x.
Require Import FORVES2.optimizations.iszero_sub.
Import Opt_iszero_sub.
Require Import FORVES2.optimizations.iszero_lt.
Import Opt_iszero_lt.
Require Import FORVES2.optimizations.iszero_xor.
Import Opt_iszero_xor.
Require Import FORVES2.optimizations.iszero2_gt.
Import Opt_iszero2_gt.
Require Import FORVES2.optimizations.iszero2_lt.
Import Opt_iszero2_lt.
Require Import FORVES2.optimizations.iszero2_eq.
Import Opt_iszero2_eq.
Require Import FORVES2.optimizations.xor_x_x.
Import Opt_xor_x_x.
Require Import FORVES2.optimizations.xor_zero.
Import Opt_xor_zero.
Require Import FORVES2.optimizations.xor_xor.
Import Opt_xor_xor.
Require Import FORVES2.optimizations.or_or.
Import Opt_or_or.
Require Import FORVES2.optimizations.or_and.
Import Opt_or_and.
Require Import FORVES2.optimizations.and_or.
Import Opt_and_or.
Require Import FORVES2.optimizations.and_not.
Import Opt_and_not.
Require Import FORVES2.optimizations.or_not.
Import Opt_or_not.
Require Import FORVES2.optimizations.or_x_x.
Import Opt_or_x_x.
Require Import FORVES2.optimizations.and_x_x.
Import Opt_and_x_x.
Require Import FORVES2.optimizations.or_zero.
Import Opt_or_zero.
Require Import FORVES2.optimizations.or_ffff.
Import Opt_or_ffff.
Require Import FORVES2.optimizations.and_ffff.
Import Opt_and_ffff.
Require Import FORVES2.optimizations.and_coinbase.
Import Opt_and_coinbase.
Require Import FORVES2.optimizations.balance_address.
Import Opt_balance_address.*)


Module OptPipelines.

Inductive available_optimization_step :=
| OPT_eval
| OPT_add_zero
| OPT_not_not
| OPT_and_and
| OPT_and_origin
| OPT_mul_shl
| OPT_div_shl
| OPT_shr_zero_x
| OPT_shr_x_zero
| OPT_eq_zero
| OPT_sub_x_x
| OPT_and_zero
| OPT_div_one
| OPT_lt_x_one
| OPT_gt_one_x
| OPT_and_address
| OPT_mul_one
| OPT_iszero_gt
| OPT_eq_iszero
| OPT_and_caller
| OPT_iszero3
| OPT_add_sub
| OPT_shl_zero_x
| OPT_sub_zero
| OPT_shl_x_zero
| OPT_mul_zero
| OPT_div_x_x
| OPT_div_zero
| OPT_mod_one
| OPT_mod_zero
| OPT_mod_x_x
| OPT_exp_x_zero
| OPT_exp_x_one
| OPT_exp_one_x
| OPT_exp_zero_x
| OPT_exp_two_x
| OPT_gt_zero_x
| OPT_gt_x_x
| OPT_lt_x_zero
| OPT_lt_x_x
| OPT_eq_x_x
| OPT_iszero_sub
| OPT_iszero_lt
| OPT_iszero_xor
| OPT_iszero2_gt
| OPT_iszero2_lt
| OPT_iszero2_eq
| OPT_xor_x_x
| OPT_xor_zero
| OPT_xor_xor
| OPT_or_or
| OPT_or_and
| OPT_and_or
| OPT_and_not
| OPT_or_not
| OPT_or_x_x
| OPT_and_x_x
| OPT_or_zero
| OPT_or_ffff
| OPT_and_ffff
| OPT_and_coinbase
| OPT_balance_address
.

Definition list_opt_steps := list available_optimization_step.

Definition get_optimization_step (tag: available_optimization_step) : opt_entry :=
match tag with 
| OPT_eval => OpEntry optimize_eval_sbinding optimize_eval_sbinding_snd
| OPT_add_zero => OpEntry optimize_add_zero_sbinding optimize_add_zero_sbinding_snd
| OPT_not_not => OpEntry optimize_not_not_sbinding optimize_not_not_sbinding_snd
| OPT_and_and => OpEntry optimize_and_and_sbinding optimize_and_and_sbinding_snd
| OPT_and_origin => OpEntry optimize_and_origin_sbinding optimize_and_origin_sbinding_snd
| OPT_mul_shl => OpEntry optimize_mul_shl_sbinding optimize_mul_shl_sbinding_snd
| OPT_div_shl => OpEntry optimize_div_shl_sbinding optimize_div_shl_sbinding_snd
| OPT_shr_zero_x => OpEntry optimize_shr_zero_x_sbinding optimize_shr_zero_x_sbinding_snd
| OPT_shr_x_zero => OpEntry optimize_shr_x_zero_sbinding optimize_shr_x_zero_sbinding_snd
| OPT_eq_zero => OpEntry optimize_eq_zero_sbinding optimize_eq_zero_sbinding_snd
| OPT_sub_x_x => OpEntry optimize_sub_x_x_sbinding optimize_sub_x_x_sbinding_snd
| OPT_and_zero => OpEntry optimize_and_zero_sbinding optimize_and_zero_sbinding_snd
| OPT_div_one => OpEntry optimize_div_one_sbinding optimize_div_one_sbinding_snd
| OPT_lt_x_one => OpEntry optimize_lt_x_one_sbinding optimize_lt_x_one_sbinding_snd
| OPT_gt_one_x => OpEntry optimize_gt_one_x_sbinding optimize_gt_one_x_sbinding_snd
| OPT_and_address => OpEntry optimize_and_address_sbinding optimize_and_address_sbinding_snd
| OPT_mul_one => OpEntry optimize_mul_one_sbinding optimize_mul_one_sbinding_snd
| OPT_iszero_gt => OpEntry optimize_iszero_gt_sbinding optimize_iszero_gt_sbinding_snd
| OPT_eq_iszero => OpEntry optimize_eq_iszero_sbinding optimize_eq_iszero_sbinding_snd
| OPT_and_caller => OpEntry optimize_and_caller_sbinding optimize_and_caller_sbinding_snd
(*| OPT_iszero3 => OpEntry optimize_iszero3_sbinding optimize_iszero3_sbinding_snd
| OPT_add_sub => OpEntry optimize_add_sub_sbinding optimize_add_sub_sbinding_snd
| OPT_shl_zero_x => OpEntry optimize_shl_zero_x_sbinding optimize_shl_zero_x_sbinding_snd
| OPT_sub_zero => OpEntry optimize_sub_zero_sbinding optimize_sub_zero_sbinding_snd
| OPT_shl_x_zero => OpEntry optimize_shl_x_zero_sbinding optimize_shl_x_zero_sbinding_snd
| OPT_mul_zero => OpEntry optimize_mul_zero_sbinding optimize_mul_zero_sbinding_snd
| OPT_div_x_x => OpEntry optimize_div_x_x_sbinding optimize_div_x_x_sbinding_snd
| OPT_div_zero => OpEntry optimize_div_zero_sbinding optimize_div_zero_sbinding_snd
| OPT_mod_one => OpEntry optimize_mod_one_sbinding optimize_mod_one_sbinding_snd
| OPT_mod_zero => OpEntry optimize_mod_zero_sbinding optimize_mod_zero_sbinding_snd
| OPT_mod_x_x => OpEntry optimize_mod_x_x_sbinding optimize_mod_x_x_sbinding_snd
| OPT_exp_x_zero => OpEntry optimize_exp_x_zero_sbinding optimize_exp_x_zero_sbinding_snd
| OPT_exp_x_one => OpEntry optimize_exp_x_one_sbinding optimize_exp_x_one_sbinding_snd
| OPT_exp_one_x => OpEntry optimize_exp_one_x_sbinding optimize_exp_one_x_sbinding_snd
| OPT_exp_zero_x => OpEntry optimize_exp_zero_x_sbinding optimize_exp_zero_x_sbinding_snd
| OPT_exp_two_x => OpEntry optimize_exp_two_x_sbinding optimize_exp_two_x_sbinding_snd
| OPT_gt_zero_x => OpEntry optimize_gt_zero_x_sbinding optimize_gt_zero_x_sbinding_snd
| OPT_gt_x_x => OpEntry optimize_gt_x_x_sbinding optimize_gt_x_x_sbinding_snd
| OPT_lt_x_zero => OpEntry optimize_lt_x_zero_sbinding optimize_lt_x_zero_sbinding_snd
| OPT_lt_x_x => OpEntry optimize_lt_x_x_sbinding optimize_lt_x_x_sbinding_snd
| OPT_eq_x_x => OpEntry optimize_eq_x_x_sbinding optimize_eq_x_x_sbinding_snd
| OPT_iszero_sub => OpEntry optimize_iszero_sub_sbinding optimize_iszero_sub_sbinding_snd
| OPT_iszero_lt => OpEntry optimize_iszero_lt_sbinding optimize_iszero_lt_sbinding_snd
| OPT_iszero_xor => OpEntry optimize_iszero_xor_sbinding optimize_iszero_xor_sbinding_snd
| OPT_iszero2_gt => OpEntry optimize_iszero2_gt_sbinding optimize_iszero2_gt_sbinding_snd
| OPT_iszero2_lt => OpEntry optimize_iszero2_lt_sbinding optimize_iszero2_lt_sbinding_snd
| OPT_iszero2_eq => OpEntry optimize_iszero2_eq_sbinding optimize_iszero2_eq_sbinding_snd
| OPT_xor_x_x => OpEntry optimize_xor_x_x_sbinding optimize_xor_x_x_sbinding_snd
| OPT_xor_zero => OpEntry optimize_xor_zero_sbinding optimize_xor_zero_sbinding_snd
| OPT_xor_xor => OpEntry optimize_xor_xor_sbinding optimize_xor_xor_sbinding_snd
| OPT_or_or => OpEntry optimize_or_or_sbinding optimize_or_or_sbinding_snd
| OPT_or_and => OpEntry optimize_or_and_sbinding optimize_or_and_sbinding_snd
| OPT_and_or => OpEntry optimize_and_or_sbinding optimize_and_or_sbinding_snd
| OPT_and_not => OpEntry optimize_and_not_sbinding optimize_and_not_sbinding_snd
| OPT_or_not => OpEntry optimize_or_not_sbinding optimize_or_not_sbinding_snd
| OPT_or_x_x => OpEntry optimize_or_x_x_sbinding optimize_or_x_x_sbinding_snd
| OPT_and_x_x => OpEntry optimize_and_x_x_sbinding optimize_and_x_x_sbinding_snd
| OPT_or_zero => OpEntry optimize_or_zero_sbinding optimize_or_zero_sbinding_snd
| OPT_or_ffff => OpEntry optimize_or_ffff_sbinding optimize_or_ffff_sbinding_snd
| OPT_and_ffff => OpEntry optimize_and_ffff_sbinding optimize_and_ffff_sbinding_snd
| OPT_and_coinbase => OpEntry optimize_and_coinbase_sbinding optimize_and_coinbase_sbinding_snd
| OPT_balance_address => OpEntry optimize_balance_address_sbinding optimize_balance_address_sbinding_snd*)
(* TODO: remove when all optimization are proved *)
| _ => OpEntry optimize_add_zero_sbinding optimize_add_zero_sbinding_snd
end.

Definition all_optimization_steps_gas : list_opt_steps := 
  [OPT_eval; 
   OPT_add_zero; 
   OPT_not_not; 
   OPT_and_and;    
   OPT_and_origin; 
   OPT_div_shl;
   OPT_mul_shl;
   OPT_shr_zero_x; 
   OPT_shr_x_zero; 
   OPT_eq_zero; 
   OPT_sub_x_x; 
   OPT_and_zero; 
   OPT_div_one; 
   OPT_lt_x_one; 
   OPT_gt_one_x; 
   OPT_and_address; 
   OPT_mul_one; 
   OPT_iszero_gt; 
   OPT_eq_iszero;
   OPT_and_caller;
   OPT_iszero3;
   OPT_add_sub;
   OPT_shl_zero_x;
   OPT_sub_zero;
   OPT_shl_x_zero;
   OPT_mul_zero;
   OPT_div_x_x;
   OPT_div_zero;
   OPT_mod_one;
   OPT_mod_zero;
   OPT_mod_x_x;
   OPT_exp_x_zero;
   OPT_exp_x_one;
   OPT_exp_one_x;
   OPT_exp_zero_x;
   OPT_exp_two_x;
   OPT_gt_zero_x;
   OPT_gt_x_x;
   OPT_lt_x_zero;
   OPT_lt_x_x;
   OPT_eq_x_x;
   OPT_iszero_sub;
   OPT_iszero_lt;
   OPT_iszero_xor;
   OPT_iszero2_gt;
   OPT_iszero2_lt;
   OPT_iszero2_eq;
   OPT_xor_x_x;
   OPT_xor_zero;
   OPT_xor_xor;
   OPT_or_or;
   OPT_or_and;
   OPT_and_or;
   OPT_and_not;
   OPT_or_not;
   OPT_or_x_x;
   OPT_and_x_x;
   OPT_or_zero;
   OPT_or_ffff;
   OPT_and_ffff;
   OPT_and_coinbase;
   OPT_balance_address
].

Definition all_optimization_steps_size := 
  [OPT_div_shl;
   OPT_mul_shl;
   OPT_eval; 
   OPT_add_zero; 
   OPT_not_not; 
   OPT_and_and;    
   OPT_and_origin; 
   OPT_shr_zero_x; 
   OPT_shr_x_zero; 
   OPT_eq_zero; 
   OPT_sub_x_x; 
   OPT_and_zero; 
   OPT_div_one; 
   OPT_lt_x_one; 
   OPT_gt_one_x; 
   OPT_and_address; 
   OPT_mul_one; 
   OPT_iszero_gt; 
   OPT_eq_iszero;
   OPT_and_caller;
   OPT_iszero3;
   OPT_add_sub;
   OPT_shl_zero_x;
   OPT_sub_zero;
   OPT_shl_x_zero;
   OPT_mul_zero;
   OPT_div_x_x;
   OPT_div_zero;
   OPT_mod_one;
   OPT_mod_zero;
   OPT_mod_x_x;
   OPT_exp_x_zero;
   OPT_exp_x_one;
   OPT_exp_one_x;
   OPT_exp_zero_x;
   OPT_exp_two_x;
   OPT_gt_zero_x;
   OPT_gt_x_x;
   OPT_lt_x_zero;
   OPT_lt_x_x;
   OPT_eq_x_x;
   OPT_iszero_sub;
   OPT_iszero_lt;
   OPT_iszero_xor;
   OPT_iszero2_gt;
   OPT_iszero2_lt;
   OPT_iszero2_eq;
   OPT_xor_x_x;
   OPT_xor_zero;
   OPT_xor_xor;
   OPT_or_or;
   OPT_or_and;
   OPT_and_or;
   OPT_and_not;
   OPT_or_not;
   OPT_or_x_x;
   OPT_and_x_x;
   OPT_or_zero;
   OPT_or_ffff;
   OPT_and_ffff;
   OPT_and_coinbase;
   OPT_balance_address
].

End OptPipelines.