Require Import MirrorCharge.Java.JavaType.
Require Import MirrorCharge.Java.JavaFunc.

Require Import MirrorCharge.SetoidRewrite.Base.
Require Import MirrorCharge.SetoidRewrite.ILSetoidRewrite.
Require Import MirrorCharge.SetoidRewrite.BILSetoidRewrite.
Require Import MirrorCharge.SetoidRewrite.EmbedSetoidRewrite.

Require Import MirrorCharge.PullQuant.BILPullQuant.
Require Import MirrorCharge.PullQuant.ILPullQuant.
Require Import MirrorCharge.PullQuant.EmbedPullQuant.

Require Import MirrorCharge.ModularFunc.BaseFunc.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.EmbedFunc.

Require Import MirrorCore.Lambda.ExprCore.
(*
Definition pull_quant := 
	setoid_rewrite fEntails 
		(sr_combine il_respects (sr_combine bil_respects embed_respects)) 
		(sr_combine (il_match_plus (fun _ => true)) (sr_combine bil_match_plus eil_match_plus)).

 Definition goal : expr typ func :=
 	mkAnd tySasn (mkTrue tySasn) (mkEmbed tyProp tySasn (mkExists tyNat tyProp (mkEq tyNat (Var 0) (Var 0)))).

Fixpoint crazy_goal n :=
	match n with
		| 0 => goal
		| S n => mkAnd tySasn (crazy_goal n) (crazy_goal n)
	end.

Set Printing Width 140.

Time Eval vm_compute in pull_quant tySasn (crazy_goal 2).
*)