Require Import MirrorCharge.Java.JavaType.
Require Import MirrorCharge.Java.JavaFunc.
Require Import MirrorCharge.RTac.PullQuant.

Require Import MirrorCharge.ModularFunc.BaseFunc.
Require Import MirrorCharge.ModularFunc.ILogicFunc.

Require Import MirrorCore.Lambda.ExprCore.

Definition quant_pull := @quant_pull typ func _ _ _ (fun _ => true).
Definition rewrite_exs := @rewrite_exs typ func _ _ (fun _ => true).

 Definition goal : expr typ func :=
 	mkAnd tyProp (mkTrue tyProp) (mkExists tyNat tyProp (mkEq tyNat (Var 0) (mkNat 3))).

Fixpoint crazy_goal n :=
	match n with
		| 0 => goal
		| S n => mkAnd tyProp (crazy_goal n) (crazy_goal n)
	end.

Time Eval vm_compute in quant_pull tyProp (crazy_goal 2).
