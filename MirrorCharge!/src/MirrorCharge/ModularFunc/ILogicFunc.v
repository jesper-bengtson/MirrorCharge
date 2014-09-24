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

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Inductive ilfunc typ :=
  | ilf_entails (logic : typ)
  | ilf_true (logic : typ)
  | ilf_false (logic : typ)
  | ilf_and (logic : typ)
  | ilf_or (logic : typ)
  | ilf_impl (logic : typ)
  | ilf_exists (arg logic : typ)
  | ilf_forall (arg logic : typ).

Class ILogicFunc (typ func : Type) := {
  fEntails  : typ -> func;
  fTrue : typ -> func;
  fFalse : typ -> func;
  fAnd : typ -> func;
  fOr : typ -> func;
  fImpl : typ -> func;
  fExists : typ -> typ -> func;
  fForall : typ -> typ -> func;
  ilogicS : func -> option (ilfunc typ)
}.
    
Section ILogicFuncSum.
	Context {typ func : Type} {H : ILogicFunc typ func}.

	Global Instance ILogicFuncSumL (A : Type) : 
		ILogicFunc typ (func + A) := {
		  fEntails l := inl (fEntails l);
		  fTrue l := inl (fTrue l);
		  fFalse l := inl (fFalse l);
		  fAnd l := inl (fAnd l);
		  fOr l := inl (fOr l);
		  fImpl l := inl (fImpl l);
		  fExists t l := inl (fExists t l);
		  fForall t l := inl (fForall t l);
		  ilogicS f := match f with
		  				 | inl a => ilogicS a
		  		   	 	 | _     => None
		  			   end 
        }.

	Global Instance ILogicFuncSumR (A : Type) : 
		ILogicFunc typ (A + func) := {
		  fEntails l := inr (fEntails l);
		  fTrue l := inr (fTrue l);
		  fFalse l := inr (fFalse l);
		  fAnd l := inr (fAnd l);
		  fOr l := inr (fOr l);
		  fImpl l := inr (fImpl l);
		  fExists t l := inr (fExists t l);
		  fForall t l := inr (fForall t l);
		  ilogicS f := match f with
		  				 | inr a => ilogicS a
		  		   	 	 | _     => None
		  			   end 
        }.
        
	Global Instance ILogicFuncExpr : 
		ILogicFunc typ (expr typ func) := {
		  fEntails l := Inj (fEntails l);
		  fTrue l := Inj (fTrue l);
		  fFalse l := Inj (fFalse l);
		  fAnd l := Inj (fAnd l);
		  fOr l := Inj (fOr l);
		  fImpl l := Inj (fImpl l);
		  fExists t l := Inj (fExists t l);
		  fForall t l := Inj (fForall t l);
		  ilogicS f := match f with
		  				 | Inj a => ilogicS a
		  		   	 	 | _     => None
		  			   end 
        }.

End ILogicFuncSum.

Section ILogicFuncInst.

	Context {typ func : Type}.
	Context {HR : RType typ} {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

    Variable Typ2_tyArr : Typ2 _ Fun.
    Variable Typ0_tyProp : Typ0 _ Prop.

    Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
    Let tyProp : typ := @typ0 _ _ _ _.

	Global Instance BaseFuncInst : ILogicFunc typ (ilfunc typ) := {
	  fEntails := ilf_entails;
	  fTrue := ilf_true;
	  fFalse := ilf_false;
	  fAnd := ilf_and;
	  fOr := ilf_or;
	  fImpl := ilf_impl;
	  fExists := ilf_exists;
	  fForall := ilf_forall;
	  ilogicS f := Some f
	}.

  Definition logic_ops := forall (t : typ),
    option (ILogicOps (typD t)).
  Definition logic_opsOk (l : logic_ops) : Prop :=
    forall g, match l g return Prop with
                | Some T => @ILogic _ T
                | None => True
              end.

  Variable gs : logic_ops.
  
  Definition typeof_func (f : ilfunc typ) : option typ :=
    match f with
      | ilf_true t
      | ilf_false t => match gs t with
  				   	     | Some _ => Some t
				  	     | None => None
  					   end
      | ilf_entails t => match gs t with
					  	   | Some _ => Some (tyArr t (tyArr t tyProp))
					  	   | None => None
					   	 end
      | ilf_and t
      | ilf_or t
      | ilf_impl t => match gs t with
				  	    | Some _ => Some (tyArr t (tyArr t t))
				  	    | None => None
				  	  end
      | ilf_forall a t
      | ilf_exists a t => match gs t with
					  	    | Some _ => Some (tyArr (tyArr a t) t)
					  	    | None => None
					  	  end
  	end.

  Global Instance RelDec_ilfunc : RelDec (@eq (ilfunc typ)) :=
  { rel_dec := fun a b =>
	         match a, b with
		   | ilf_entails t, ilf_entails t'
		   | ilf_true t, ilf_true t'
		   | ilf_false t, ilf_false t'
		   | ilf_and t, ilf_and t'
		   | ilf_or t, ilf_or t'
		   | ilf_impl t, ilf_impl t' => t ?[eq] t'
		   | ilf_forall a t, ilf_forall a' t'
		   | ilf_exists a t, ilf_exists a' t' => (a ?[eq] a' && t ?[eq] t')%bool
		   | _, _ => false
	         end
  }.

  Global Instance RelDec_Correct_ilfunc : RelDec_Correct RelDec_ilfunc.
  Proof.
    constructor.
    destruct x; destruct y; simpl;
    try solve [ try rewrite Bool.andb_true_iff ;
                repeat rewrite rel_dec_correct; intuition congruence ].
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

  Definition typ2_cast_quant (a b c : typ)
  : ((typD a -> typD b) -> typD c) -> typD (tyArr (tyArr a b) c) :=
    fun f =>
      match eq_sym (typ2_cast (tyArr a b) c) in _ = t
            return t with
        | eq_refl => match eq_sym (typ2_cast a b) in _ = t
                           return t -> _ with
                       | eq_refl => f
                     end
      end.
 
 Definition funcD (f : ilfunc typ) : match typeof_func f with
							       | Some t => typD t
							       | None => unit
							      end :=
    match f as f
          return match typeof_func f with
		   | Some t => typD t
		   | None => unit
		 end
    with
      | ilf_true t => match gs t as x return (match match x with
											          | Some _ => Some t
											          | None => None
											        end with
				                                 | Some t0 => typD t0
											 	 | None => unit
											       end) with
					    | Some t => @ltrue _ t
					    | None => tt
				      end
      | ilf_false t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some t
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t => @lfalse _ t
	  | None => tt
        end
      | ilf_entails t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some (tyArr t (tyArr t tyProp))
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some C =>
            match eq_sym (typ2_cast t (tyArr t tyProp)) in _ = t
                  return t with
              | eq_refl =>
                match eq_sym (typ2_cast t tyProp) in _ = t
                      return _ -> t with
                  | eq_refl =>
                    match eq_sym (typ0_cast (F := Prop)) in _ = t
                          return _ -> _ -> t
                    with
                      | eq_refl => @lentails _ _
                    end
                end
            end
	  | None => tt
        end
      | ilf_and t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some (tyArr t (tyArr t t))
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t => typ2_cast_bin _ _ _ (@land _ _)
	  | None => tt
        end
      | ilf_impl t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some (tyArr t (tyArr t t))
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t => typ2_cast_bin _ _ _ (@limpl _ _)
	  | None => tt
        end
      | ilf_or t =>
        match gs t as x
              return (match match x with
			      | Some _ => Some (tyArr t (tyArr t t))
			      | None => None
			    end with
			| Some t0 => typD t0
			| None => unit
		      end) with
	  | Some t => typ2_cast_bin _ _ _ (@lor _ _)
	  | None => tt
        end
      | ilf_exists a t =>
        match gs t as x return (match match x with
					| Some _ => Some (tyArr (tyArr a t) t)
					| None => None
				      end with
				  | Some t0 => typD t0
				  | None => unit
				end) with
	  | Some t0 => typ2_cast_quant _ _ _ (@lexists _ _ _)
	  | None => tt
        end
      | ilf_forall a t =>
        match gs t as x return (match match x with
					| Some _ => Some (tyArr (tyArr a t) t)
					| None => None
				      end with
				  | Some t0 => typD t0
				  | None => unit
				end) with
	  | Some t0 => typ2_cast_quant _ _ _ (@lforall _ _ _)
	  | None => tt
        end
    end.

  Global Instance RSym_ilfunc : SymI.RSym (ilfunc typ) :=
  { typeof_sym := typeof_func
  ; sym_eqb := fun a b => Some (rel_dec a b)
  ; symD := funcD
  }.

  Global Instance RSymOk_ilfunc : SymI.RSymOk RSym_ilfunc.
  Proof.
    constructor.
    intros. unfold sym_eqb; simpl.
    consider (a ?[ eq ] b); auto.
  Qed.

End ILogicFuncInst.

Section MakeILogic.
	Context {typ func : Type} {H : ILogicFunc typ func}.

	Definition mkEntails (t : typ) (P Q : expr typ func) := App (App (fEntails t) P) Q.
	Definition mkTrue t : expr typ func := Inj (fTrue t).
	Definition mkFalse t : expr typ func := Inj (fFalse t).
	Definition mkAnd (t : typ) (P Q : expr typ func) := App (App (fAnd t) P) Q.
	Definition mkOr (t : typ) (P Q : expr typ func) := App (App (fOr t) P) Q.
	Definition mkImpl (t : typ) (P Q : expr typ func) := App (App (fImpl t) P) Q.
	Definition mkExists (t l : typ) (f : expr typ func) := App (fExists t l) (Abs t f).
	Definition mkForall (t l : typ) (f : expr typ func) := App (fForall t l) (Abs t f).

End MakeILogic.
