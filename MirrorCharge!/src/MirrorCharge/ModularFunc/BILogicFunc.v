Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.Bool.
Require Import ExtLib.Data.String.
Require Import ExtLib.Tactics.Consider.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.SymI.

Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.BILogic.

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Require Import MirrorCharge.ModularFunc.ILogicFunc.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive bilfunc typ :=
  | bilf_emp (logic : typ)
  | bilf_star (logic : typ)
  | bilf_wand (logic : typ).
 

Class BILogicFunc (typ func : Type) := {
  fEmp : typ -> func;
  fStar : typ -> func;
  fWand : typ -> func;
  bilogicS : func -> option (bilfunc typ)
}.
    
Section BILogicFuncSum.
	Context {typ func : Type} {H : BILogicFunc typ func}.

	Global Instance BILogicFuncSumL (A : Type) : 
		BILogicFunc typ (func + A) := {
		  fEmp l := inl (fEmp l);
		  fStar l := inl (fStar l);
		  fWand l := inl (fWand l);
		  bilogicS f := match f with
		  				  | inl a => bilogicS a
		  				  | _     => None
		  				end 
       }.

	Global Instance BILogicFuncSumR (A : Type) : 
		BILogicFunc typ (A + func) := {
		  fEmp l := inr (fEmp l);
		  fStar l := inr (fStar l);
		  fWand l := inr (fWand l);
		  bilogicS f := match f with
		  				  | inr a => bilogicS a
		  				  | _     => None
		  				end 
       }.

	Global Instance BILogicFuncExpr : 
		BILogicFunc typ (expr typ func) := {
		  fEmp l := Inj (fEmp l);
		  fStar l := Inj (fStar l);
		  fWand l := Inj (fWand l);
		  bilogicS f := match f with
		  				  | Inj a => bilogicS a
		  				  | _ => None
		  				end 
        }.

End BILogicFuncSum.

Section BILogicFuncInst.

	Context {typ func : Type}.
	Context {HR : RType typ} {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

    Variable Typ2_tyArr : Typ2 _ Fun.
    Variable Typ0_tyProp : Typ0 _ Prop.

    Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
    Let tyProp : typ := @typ0 _ _ _ _.

	Global Instance BaseFuncInst : BILogicFunc typ (bilfunc typ) := {
	  fEmp := bilf_emp;
	  fStar := bilf_star;
	  fWand := bilf_wand;
	  bilogicS f := Some f 
	}.
	
  Variable is : logic_ops.

  Definition bilogic_ops := forall (t : typ),
    option (BILOperators (typD t)).
  Definition bilogic_opsOk (l : bilogic_ops) : Prop :=
    forall g, match is g, l g return Prop with
                | Some T, Some U => @BILogic _ T U
                | _, _ => True
              end.

  Variable gs : bilogic_ops.
  
  Definition typeof_bilfunc (f : bilfunc typ) : option typ :=
    match f with
      | bilf_emp t => match gs t with
  				   	     | Some _ => Some t
				  	     | None => None
  					   end
      | bilf_star t
      | bilf_wand t => match gs t with
				  	     | Some _ => Some (tyArr t (tyArr t t))
				  	     | None => None
				  	  end
  	end.

  Global Instance RelDec_bilfunc : RelDec (@eq (bilfunc typ)) :=
  { rel_dec := fun a b =>
	         match a, b with
		   | bilf_emp t, bilf_emp t'
		   | bilf_star t, bilf_star t'
		   | bilf_wand t, bilf_wand t' => t ?[eq] t'
		   | _, _ => false
	         end
  }.

  Global Instance RelDec_Correct_bilfunc : RelDec_Correct RelDec_bilfunc.
  Proof.
    constructor.
    destruct x; destruct y; simpl;
    repeat rewrite rel_dec_correct; intuition congruence.
  Qed.

  Definition typ2_cast_bin (a b c : typ)
  : (typD a -> typD b -> typD c) -> typD (tyArr a (tyArr b c)) :=
    fun f =>
      match eq_sym (typ2_cast a (tyArr b c)) in _ = t
            return t with
        | eq_refl => match eq_sym (typ2_cast b c) in _ = t
                           return _ -> t with
                       | eq_refl => f
                     end
        end.

 Definition funcD (f : bilfunc typ) : match typeof_bilfunc f with
							       | Some t => typD t
							       | None => unit
							      end :=
    match f as f
          return match typeof_bilfunc f with
		   | Some t => typD t
		   | None => unit
		 end
    with
      | bilf_emp t => match gs t as x return (match match x with
											          | Some _ => Some t
											          | None => None
											        end with
				                                 | Some t0 => typD t0
											 	 | None => unit
											       end) with
					    | Some t => @empSP _ t
					    | None => tt
				      end
      | bilf_star t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some (tyArr t (tyArr t t))
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t => typ2_cast_bin _ _ _ (@sepSP _ _)
	  | None => tt
        end
      | bilf_wand t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some (tyArr t (tyArr t t))
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t => typ2_cast_bin _ _ _ (@wandSP _ _)
	  | None => tt
        end
    end.

  Global Instance RSym_bilfunc : SymI.RSym (bilfunc typ) :=
  { typeof_sym := typeof_bilfunc
  ; sym_eqb := fun a b => Some (rel_dec a b)
  ; symD := funcD
  }.

  Global Instance RSymOk_bilfunc : SymI.RSymOk RSym_bilfunc.
  Proof.
    constructor.
    intros. unfold sym_eqb; simpl.
    consider (a ?[ eq ] b); auto.
  Qed.

End BILogicFuncInst.

Section MakeBILogic.
	Context {typ func : Type} {H : BILogicFunc typ func}.

	Definition mkEmp t : expr typ func:= Inj (fEmp t).
	Definition mkStar (t : typ) (P Q : expr typ func) := App (App (fStar t) P) Q.
	Definition mkWand (t : typ) (P Q : expr typ func) := App (App (fWand t) P) Q.

End MakeBILogic.
