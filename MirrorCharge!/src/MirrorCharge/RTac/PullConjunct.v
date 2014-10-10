Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.STac.STac.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.

Require Import MirrorCharge.ILogicFunc.
Require Import MirrorCharge.ModularFunc.BaseFunc.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.SetoidRewrite.Base.
Require Import MirrorCharge.SetoidRewrite.ILSetoidRewrite.
Require Import MirrorCharge.PullConjunct.ILPullConjunct.

Require Import Charge.Logics.ILogic.

Set Implicit Arguments.
Set Strict Implicit.

Section PullConjunct.
  Context (typ func subst : Type).
  Context {HIL : ILogicFunc typ func} {HB : BaseFunc typ func}.
  Context {RelDec_func : RelDec (@eq (expr typ func))}.
  Context {target : expr typ func -> bool}.
  Context {RType_typ : RType typ}.
  Context {HT : Typ2 RType_typ Fun}.
  Context {RSym_func : RSym func}.
  Context {ilogic : forall t : typ, option (ILogicOps (typD t))}.

  Definition pull_conjunct := 
	setoid_rewrite fEntails (sr_combine il_respects (il_respects_reflexive ilogic)) (il_pull_conjunct target).

  Definition stac_pull_conjunct_l : stac typ (expr typ func) subst :=
    fun tus tvs s hyps e =>
      match e with
        | App (App f L) R =>
          match ilogicS f with
	        | Some (ilf_entails l) =>
	        	More nil nil s hyps (mkEntails l (pull_conjunct l L) R)
	        | _ => More nil nil s hyps e
	      end
        | _ => More nil nil s hyps e
      end.

End PullConjunct.

Implicit Arguments stac_pull_conjunct_l [[HIL] [HB] [RelDec_func] [RType_typ] [HT] [RSym_func]].

Section PullConjunctTac.
  Context {typ func subst : Type}.
  Context {HIL : ILogicFunc typ func} {HB : BaseFunc typ func}.
  Context {RelDec_func : RelDec (@eq (expr typ func))}.
  Context {target : expr typ func -> bool}.
  Context {SS : SubstI.Subst subst (expr typ func)}.
  Context {SU : SubstI.SubstUpdate subst (expr typ func)}.
  Context {RType_typ : RType typ}.
  Context {HT : Typ2 RType_typ Fun}.
  Context {RSym_func : RSym func}.
  Context {ilogic : forall t : typ, option (ILogicOps (typD t))}.
  
  Definition PULLCONJUNCTL :=
    (STAC_no_hyps (@ExprSubst.instantiate typ func) (stac_pull_conjunct_l typ func subst target ilogic)).

End PullConjunctTac.

Implicit Arguments PULLCONJUNCTL [[HIL] [HB] [RelDec_func] [SU] [RType_typ] [HT] [RSym_func]].

