Require Import ExtLib.Core.RelDec.

Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.TypesI.

Require Import MirrorCharge.ModularFunc.ILogicFunc.

Section IntroTac.
	Context {typ func subst : Type}.
	Context {HIL : ILogicFunc typ func}.
	Context {RType_typ : RType typ}.
    Context {Typ0_tyProp : Typ0 RType_typ Prop}.
    Context {Heq : RelDec (@eq typ)}.

    Let tyProp : typ := @typ0 _ _ _ _.

	Definition fintro e : option (OpenAs typ (expr typ func)) :=
		match e with
			| App (Inj f) P =>
				match ilogicS f with
				  | Some (ilf_forall t t') => 
				  	if t' ?[ eq ] tyProp then 
				  		Some (AsAl t (fun x => beta (App P x)))
				  	else
				  		None
				  | Some (ilf_exists t t') => 
				  	if t' ?[ eq ] tyProp then 
				  		Some (AsEx t (fun x => beta (App P x)))
				  	else
				  		None
				  | _ => None
				end
			| App (App (Inj f) P) Q =>
				match ilogicS f with
				  | Some (ilf_impl t') => 
				  	if t' ?[ eq ] tyProp then 
				  		Some (AsHy typ P Q)
				  	else
				  		None
				  | _ => None
				end
			| _ => None
		end.

	Definition INTRO := @INTRO typ (expr typ func) subst (@Var typ func) (@UVar typ func) fintro.

End IntroTac.

Implicit Arguments INTRO [[HIL] [RType_typ] [Typ0_tyProp] [Heq]].