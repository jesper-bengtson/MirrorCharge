Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.TypesI.

Require Import ExtLib.Core.RelDec.

Require Import MirrorCharge.SetoidRewrite.Base.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.EmbedFunc.
Require Import MirrorCharge.AutoSetoidRewrite.

Require Import Charge.Logics.ILogic.

Section EILPullQuant.
  Context {typ func : Type} {HIL : ILogicFunc typ func} {HB : EmbedFunc typ func}.
  Context {RType_typ : RType typ}.
  Context {RelDec_func : RelDec (@eq (expr typ func))}.

  Let Rbase := expr typ func.

Definition eil_match_plus (e : expr typ func) (_ : list (RG (expr typ func))) (rg : RG Rbase) : m (expr typ func) :=
  match e with
    | App a (App b P) =>
      let P := beta (App P (Var 0)) in
      match embedS (typ := typ) (func := expr typ func) a, ilogicS b with 
      	| Some (eilf_embed u v), Some (ilf_exists t l) =>
	      rg_plus
	      (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails v))))
	        (fun _ => rg_ret (mkExists t v (mkEmbed u v P))))
	      (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails v)))
	        (fun _ => rg_ret (mkExists t v (mkEmbed u v P))))
	    | _, _ => rg_fail
	  end
	| _ => rg_fail
  end.

End EILPullQuant.

Implicit Arguments eil_match_plus [[typ] [func] [HIL] [HB] [RelDec_func]].