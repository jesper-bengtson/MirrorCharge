Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.SymI.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.Lambda.ExprUnify_simul.

Section EAutoTac.
	Context {typ func subst : Type}.
	Context {RType_typ : RType typ}.
	Context {Typ2_typ : Typ2 RType_typ Fun}.
	Context {Typ0_typ : Typ0 RType_typ Prop}.
	Context {RSym_func : @RSym _ RType_typ func}.
	Context {SS : SubstI.Subst subst (expr typ func)}.
	Context {SU : SubstI.SubstUpdate subst (expr typ func)}.

	Definition EAPPLY := @EAPPLY typ (expr typ func) subst _ _ SS SU
					  UVar
                      (@vars_to_uvars _ _)
                      (fun _ _ _ tus tvs n l r t s =>
                         @exprUnify _ _ _ _ _ _ _ _ 10 tus tvs n s l r t)
                      (@instantiate _ _).


End EAutoTac.

Implicit Arguments EAPPLY [[RType_typ] [Typ2_typ] [Typ0_typ] [RSym_func] [SS] [SU]].