Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.TypesI.

Require Import ExtLib.Core.RelDec.

Require Import MirrorCharge.SetoidRewrite.Base.
Require Import MirrorCharge.ModularFunc.BaseFunc.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.AutoSetoidRewrite.

Require Import Charge.Logics.ILogic.

Section ILPullQuant.
  Context {typ func : Type} {HIL : ILogicFunc typ func} {HB : BaseFunc typ func}.
  Context {RType_typ : RType typ}.
  Context {RelDec_func : RelDec (@eq (expr typ func))}.

  Let Rbase := expr typ func.

  Variable inhabited : typ -> bool.  
  Variable inhabited_sound : forall t, inhabited t = true -> Inhabited (typD t).

Definition il_match_plus_l (e : expr typ func) (_ : list (RG (expr typ func))) (rg : RG Rbase) : m (expr typ func) :=
  match e with
    | App (App a (App b P)) Q =>
      let P := beta (App P (Var 0)) in
      let Q := lift 0 1 Q in
      match ilogicS (typ := typ) (func := expr typ func) a, ilogicS b with 
      	| Some (ilf_and _), Some (ilf_exists t l) =>
	      rg_plus
	      (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
	        (fun _ => rg_ret (mkExists t l (mkAnd l P Q))))
	      (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
	        (fun _ => rg_ret (mkExists t l (mkAnd l P Q))))
      	| Some (ilf_or _), Some (ilf_exists t l) =>
      	  let rewrite_rl :=
	        rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
		      (fun _ => rg_ret (mkExists t l (mkOr l P Q))) in
			if inhabited t then
		      rg_plus 
		        rewrite_rl 
		        (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
		          (fun _ => rg_ret (mkExists t l (mkOr l P Q))))
		    else
		      rewrite_rl
	    | _, _ => rg_fail
	  end
	| _ => rg_fail
  end.
  
Definition il_match_plus_r (e : expr typ func) (_ : list (RG (expr typ func))) (rg : RG Rbase) : m (expr typ func) :=
  match e with
   | App (App a P) (App b Q) =>
   	 let P := lift 0 1 P in
   	 let Q := beta (App Q (Var 0)) in
     match ilogicS a, ilogicS b with
       | Some (ilf_and _), Some (ilf_exists t l) =>
	      rg_plus
	        (rg_bind
	          (unifyRG (@rel_dec (expr typ func) _ _ ) rg (RGinj (fEntails l)))
	            (fun _ => rg_ret (mkExists t l (mkAnd l P Q))))
  	        (rg_bind
	          (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
	            (fun _ => rg_ret (mkExists t l (mkAnd l P Q))))
       | Some (ilf_or _), Some (ilf_exists t l) =>
         let rewrite_rl := 
		   rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
		     (fun _ => rg_ret (mkExists t l (mkOr l P Q))) in
		   if inhabited t then
		     rg_plus
		       rewrite_rl
		       (rg_bind (unifyRG (@rel_dec (expr typ func) _ _ ) rg (RGinj (fEntails l)))
		         (fun _ => rg_ret (mkExists t l (mkOr t P Q))))
		   else
		     rewrite_rl
	   | _, _ => rg_fail
	 end
   | _ => rg_fail
 end.

Definition il_match_plus := sr_combine il_match_plus_l il_match_plus_r.

End ILPullQuant.

Implicit Arguments il_match_plus [[typ] [func] [HIL] [RelDec_func]].
