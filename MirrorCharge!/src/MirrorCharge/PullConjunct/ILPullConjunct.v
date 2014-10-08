Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.TypesI.

Require Import ExtLib.Core.RelDec.

Require Import MirrorCharge.SetoidRewrite.Base.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.AutoSetoidRewrite.

Require Import Charge.Logics.ILogic.

Section ILPullConjunct.
  Context {typ func : Type} {HIL : ILogicFunc typ func}.
  Context {RType_typ : RType typ}.
  Context {RelDec_func : RelDec (@eq (expr typ func))}.

  Let Rbase := expr typ func.

  Variable target : expr typ func -> bool.  

Definition il_pull_conjunct_l (e : expr typ func) (_ : list (RG (expr typ func))) (rg : RG Rbase) : m (expr typ func) :=
  match e with
    | App (App a P) (App (App b Q) R) =>
      match ilogicS (typ := typ) (func := expr typ func) a, ilogicS b with
      	| Some (ilf_and l), Some (ilf_and _) =>
      		match target Q with
      			| true => rg_plus
                   (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
				      (fun _ => rg_ret (mkAnd l Q (mkAnd l P R))))
				   (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
				      (fun _ => rg_ret (mkAnd l Q (mkAnd l P R))))      			
      		    | _ => rg_fail
      		end
      	| _, _ => rg_fail
      end
    | _ => rg_fail
  end.

Definition il_pull_conjunct_r (e : expr typ func) (_ : list (RG (expr typ func))) (rg : RG Rbase) : m (expr typ func) :=
  match e with
    | App (App a (App (App b P) Q)) R =>
      match ilogicS (typ := typ) (func := expr typ func) a, ilogicS b with
      	| Some (ilf_and l), Some (ilf_and _) =>
      		match target P with
      			| true => rg_plus
	               (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
					 (fun _ => rg_ret (mkAnd l P (mkAnd l Q R))))
				   (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
					 (fun _ => rg_ret (mkAnd l P (mkAnd l Q R))))      			
      		    | _ => rg_fail
      		end
      	| _, _ => rg_fail
      end
    | _ => rg_fail
  end.

Definition il_pull_conjunct_sym (e : expr typ func) (_ : list (RG (expr typ func))) (rg : RG Rbase) : m (expr typ func) :=
  match e with
    | App (App a P) Q =>
      match ilogicS (typ := typ) (func := expr typ func) a with
      	| Some (ilf_and l) =>
      		match target Q with
      		  | true => rg_plus
		                  (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGflip (RGinj (fEntails l))))
				 		     (fun _ => rg_ret (mkAnd l Q P)))
				 		  (rg_bind (unifyRG (@rel_dec (expr typ func) _ _) rg (RGinj (fEntails l)))
						     (fun _ => rg_ret (mkAnd l Q P)))     
      		  | _ => rg_fail
      		end
        | _ => rg_fail
      end
    | _ => rg_fail
  end.  

Definition il_pull_conjunct := sr_combine il_pull_conjunct_sym (sr_combine il_pull_conjunct_l il_pull_conjunct_r).

End ILPullConjunct.

Implicit Arguments il_pull_conjunct [[typ] [func] [HIL] [RelDec_func]].
