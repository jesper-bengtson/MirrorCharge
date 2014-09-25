Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprSubst.

Section InstantiateTac.
	Context {typ func subst : Type}.
	Context {SS : SubstI.Subst subst (expr typ func)}.

	Definition INSTANTIATE := 
		@INSTANTIATE typ (expr typ func) subst SS (@ExprSubst.instantiate typ func).

End InstantiateTac.

Implicit Arguments INSTANTIATE [[SS]].