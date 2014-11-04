Require Import MirrorCharge.Java.JavaType.
Require Import MirrorCharge.Java.JavaFunc.

Require Import MirrorCharge.SetoidRewrite.Base.
Require Import MirrorCharge.SetoidRewrite.ILSetoidRewrite.
Require Import MirrorCharge.SetoidRewrite.BILSetoidRewrite.
Require Import MirrorCharge.SetoidRewrite.EmbedSetoidRewrite.

Require Import MirrorCharge.RTac.PullConjunct.

Require Import MirrorCharge.ModularFunc.BaseFunc.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.EmbedFunc.

Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.RTac.RTac.

Definition f (e : expr typ func) := match ilogicS e with Some (ilf_false _) => true | _ => false end.
Definition PCT := PULLCONJUNCTL typ func subst f ilops.

Check PCT.
Print rtac.

Set Printing Width 140.

Definition goal1 : expr typ func := mkEntails tyProp 
	(mkAnd tyProp (mkTrue tyProp) (mkFalse tyProp)) (mkTrue tyProp).

Definition goal2 : expr typ func := mkEntails tyProp 
	(mkAnd tyProp (mkAnd tyProp (mkTrue tyProp) (mkFalse tyProp)) (mkAnd tyProp (mkAnd tyProp (mkFalse tyProp) (mkTrue tyProp)) (mkFalse tyProp))) (mkTrue tyProp).

Eval vm_compute in PCT nil nil 0 0 CTop (@ctx_empty typ (expr typ func) subst SU CTop) goal1.
Eval vm_compute in PCT nil nil 0 0 CTop (ctx_empty (expr := expr typ func) (subst := subst)) goal2.
