Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.TypesI.

Require Import ExtLib.Core.RelDec.

Require Import MirrorCharge.SetoidRewrite.Base.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.BILogicFunc.
Require Import MirrorCharge.AutoSetoidRewrite.

Require Import Charge.Logics.BILogic.
Require Import Charge.Logics.ILogic.

Section BILPullQuant.
  Context {typ func : Type} {HIL : ILogicFunc typ func} {HBIL : BILogicFunc typ func}.
  Context {RType_typ : RType typ}.
  Context {RelDec_func : RelDec (@eq (expr typ func))}.

  Let Rbase := expr typ func.

Definition bil_match_plus_l (e : expr typ func) (_ : list (RG (expr typ func))) (rg : RG Rbase) : m (expr typ func) :=
  match e with
    | App (App a (App b P)) Q =>
      let P := beta (App P (Var 0)) in
      let Q := lift 0 1 Q in
      match bilogicS (typ := typ) (func := expr typ func) a, ilogicS b with 
      	| Some (bilf_star _), Some (ilf_exists t l) =>
	      rg_plus
	      (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
	        (fun _ => rg_ret (mkExists t l (mkAnd l P Q))))
	      (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
	        (fun _ => rg_ret (mkExists t l (mkAnd l P Q))))
	    | _, _ => rg_fail
	  end
	| _ => rg_fail
  end.
  
Definition bil_match_plus_r (e : expr typ func) (_ : list (RG (expr typ func))) (rg : RG Rbase) : m (expr typ func) :=
  match e with
   | App (App a P) (App b Q) =>
   	 let P := lift 0 1 P in
   	 let Q := beta (App Q (Var 0)) in
     match bilogicS a, ilogicS b with
       | Some (bilf_star _), Some (ilf_exists t l) =>
	      rg_plus
	        (rg_bind
	          (unifyRG (@rel_dec (expr typ func) _ _ ) rg (RGinj (fEntails l)))
	            (fun _ => rg_ret (mkExists t l (mkAnd l P Q))))
  	        (rg_bind
	          (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
	            (fun _ => rg_ret (mkExists t l (mkAnd l P Q))))
	   | _, _ => rg_fail
	 end
   | _ => rg_fail
 end.

Definition bil_match_plus := sr_combine bil_match_plus_l bil_match_plus_r.

End BILPullQuant.