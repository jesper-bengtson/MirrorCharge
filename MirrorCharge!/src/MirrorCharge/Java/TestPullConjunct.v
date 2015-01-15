Require Import MirrorCharge.Java.JavaType.
Require Import MirrorCharge.Java.JavaFunc.

Require Import MirrorCharge.SetoidRewrite.Base.
Require Import MirrorCharge.SetoidRewrite.ILSetoidRewrite.
Require Import MirrorCharge.SetoidRewrite.BILSetoidRewrite.
Require Import MirrorCharge.SetoidRewrite.EmbedSetoidRewrite.

Require Import MirrorCharge.RTac.PullConjunct.

Require Import MirrorCharge.ModularFunc.BaseFunc.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.BILogicFunc.
Require Import MirrorCharge.ModularFunc.EmbedFunc.

Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.RTac.RTac.

Section TestPullConjunct.

Context {fs : Environment}.

Definition f (e : expr typ func) := match ilogicS e with Some (ilf_false _) => true | _ => false end.
Definition PCT := PULLCONJUNCTL typ func f ilops.

Set Printing Width 140.

Fixpoint seq_pc n : expr typ func :=
  match n with
    | 0 => mkAnd tyProp (mkTrue tyProp) (mkFalse tyProp)
    | S n => mkAnd tyProp (seq_pc n) (seq_pc n)
  end.

Definition goal1 : expr typ func := mkEntails tyProp 
	(mkAnd tyProp (mkTrue tyProp) (mkFalse tyProp)) (mkTrue tyProp).

Definition goal2 : expr typ func := mkEntails tyProp 
	(mkAnd tyProp (mkAnd tyProp (mkTrue tyProp) (mkFalse tyProp)) (mkAnd tyProp (mkAnd tyProp (mkFalse tyProp) (mkTrue tyProp)) (mkFalse tyProp))) (mkTrue tyProp).

Definition goal3 : expr typ func := mkEntails tyProp 
	(mkAnd tyProp (mkFalse tyProp) (mkTrue tyProp)) (mkTrue tyProp).

Definition goal4 : expr typ func := mkEntails tyProp 
	(mkAnd tyProp (mkAnd tyProp (mkTrue tyProp) (mkFalse tyProp)) (mkTrue tyProp)) (mkTrue tyProp).

Definition goal5 : expr typ func := mkEntails tyProp 
	(mkAnd tyProp (mkAnd tyProp (mkAnd tyProp (mkTrue tyProp) (mkFalse tyProp)) (mkAnd tyProp (mkTrue tyProp) (mkFalse tyProp))) (mkTrue tyProp)) (mkTrue tyProp).

Definition goal6 : expr typ func := mkEntails tyProp
  (mkAnd tyProp (mkAnd tyProp (mkTrue tyProp) (mkFalse tyProp))
                (mkAnd tyProp (mkTrue tyProp) (mkFalse tyProp)))
  (mkTrue tyProp).
        
Definition goal7 : expr typ func := mkEntails tyProp 
	(mkAnd tyProp (mkAnd tyProp (mkTrue tyProp) (mkFalse tyProp)) 
	  (mkEmp tyProp)) (mkTrue tyProp).


Eval vm_compute in PCT nil nil 0 0 (CTop nil nil) (@ctx_empty typ (expr typ func) (CTop nil nil)) goal1.
Eval vm_compute in PCT nil nil 0 0 (CTop nil nil) (ctx_empty (expr := expr typ func)) goal2.
Eval vm_compute in PCT nil nil 0 0 (CTop nil nil) (ctx_empty (expr := expr typ func)) goal3.
Eval vm_compute in PCT nil nil 0 0 (CTop nil nil) (ctx_empty (expr := expr typ func)) goal4.
Eval vm_compute in PCT nil nil 0 0 (CTop nil nil) (ctx_empty (expr := expr typ func)) goal5.
Eval vm_compute in PCT nil nil 0 0 (CTop nil nil) (ctx_empty (expr := expr typ func)) goal6.
Eval vm_compute in PCT nil nil 0 0 (CTop nil nil) (ctx_empty (expr := expr typ func)) goal7.
Eval vm_compute in PCT nil nil 0 0 (CTop nil nil) (ctx_empty (expr := expr typ func)) 
	(mkEntails tyProp (mkAnd tyProp (seq_pc 3) (mkTrue tyProp)) (mkTrue tyProp)).

End TestPullConjunct.
