Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Tactics.Consider.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.SymI.

Require Import Charge.Open.Stack.
Require Import Charge.Open.Subst.
Require Import Charge.Rel.

Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Require Import MirrorCharge.ModularFunc.BaseType.
Require Import MirrorCharge.ModularFunc.ListType.
Require Import MirrorCharge.ModularFunc.SubstType.
Require Import MirrorCharge.ModularFunc.ListFunc.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

  Inductive open_func typ {RType_typ : RType typ} {HST : SubstType typ} :=
    | of_const (_ : typ)
    | of_ap (_ _ : typ)
    | of_var (_ : typD tyVar)
    | of_null
    | of_stack_get
    | of_stack_set
    | of_apply_subst (_ : typ)
    | of_single_subst
    | of_subst
    | of_trunc_subst.
    
Implicit Arguments open_func [[RType_typ] [HST]].
    
Class OpenFunc (typ func : Type) {RType_typ : RType typ} {HST : SubstType typ} := {
  fConst : typ -> func;
  fAp : typ -> typ -> func;
  
  fVar : typD tyVar -> func;
  fNull : func;
  
  fStackGet : func;
  fStackSet : func;
  
  fApplySubst : typ -> func;
  fSingleSubst : func;
  fSubst : func;
  fTruncSubst : func;
  
  open_funcS : func -> option (open_func typ)
}.

Implicit Arguments OpenFunc [[RType_typ] [HST]].

Section OpenFuncSum.
	Context {typ func : Type} `{H : OpenFunc typ func}.

	Global Instance OpenFuncSumL (A : Type) : 
	   OpenFunc typ (func + A) := {
		  fConst t := inl (fConst t);
		  fAp t u := inl (fAp t u);
		  
		  fVar x := inl (fVar x);
		  fNull := inl fNull;
		  
		  fStackGet := inl fStackGet;
		  fStackSet := inl fStackSet;
		  
		  fApplySubst t := inl (fApplySubst t);
		  fSingleSubst := inl fSingleSubst;
		  fSubst := inl fSubst;
		  fTruncSubst := inl fTruncSubst;
		  
		  open_funcS f := match f with
		  				    | inl f => open_funcS f
		  				    | inr _ => None
		  				  end
       }.

	Global Instance OpenFuncSumR (A : Type) : 
	   OpenFunc typ (A + func) := {
		  fConst t := inr (fConst t);
		  fAp t u := inr (fAp t u);
		  
		  fVar x := inr (fVar x);
		  fNull := inr fNull;
		  
		  fStackGet := inr fStackGet;
		  fStackSet := inr fStackSet;
		  
		  fApplySubst t := inr (fApplySubst t);
		  fSingleSubst := inr fSingleSubst;
		  fSubst := inr fSubst;
		  fTruncSubst := inr fTruncSubst;
		  
		  open_funcS f := match f with
		  				    | inr f => open_funcS f
		  				    | inl _ => None
		  				  end
		  
       }.

	Global Instance OpenFuncExpr : 
	   OpenFunc typ (expr typ func) := {
		  fConst t := Inj (fConst t);
		  fAp t u := Inj (fAp t u);
		  
		  fVar x := Inj (fVar x);
		  fNull := Inj fNull;
		  
		  fStackGet := Inj fStackGet;
		  fStackSet := Inj fStackSet;
		  
		  fApplySubst t := Inj (fApplySubst t);
		  fSingleSubst := Inj fSingleSubst;
		  fSubst := Inj fSubst;
		  fTruncSubst := Inj fTruncSubst;
		  
		  open_funcS f := match f with
		  				    | Inj f => open_funcS f
		  				    | _ => None
		  				  end
		  
       }.

End OpenFuncSum.

Section OpenFuncInst.

	Context {typ func : Type} {HBT : BaseType typ} {HLT : ListType typ}.
	Context {HR : RType typ} {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

    Variable Typ2_tyArr : Typ2 _ Fun.
    Variable Typ0_tyProp : Typ0 _ Prop.
    
    Context {HST : SubstType typ} {HV : ValNull (typD tyVal)}.
    Context {HSTD : SubstTypeD}.
    Context {HBTD : BaseTypeD} {HLTD : ListTypeD}.
    
	Context {RelDec_var : RelDec (@eq (typD tyVar))}.
	Context {RelDec_var_Correct : RelDec_Correct RelDec_var}.
	
    Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
    Let tyProp : typ := @typ0 _ _ _ _.

	Local Notation "'tyStack'" := (tyArr tyVar tyVal).
	Local Notation "'tyExpr'" := (tyArr tyStack tyVal).
	Local Notation "'tySubstList'" := (tyList (tyPair tyVar (tyArr tyStack tyVal))).

	Definition stack := @stack (typD tyVar) (typD tyVal).

	Global Instance LaterFuncInst : OpenFunc typ (open_func typ) := {
	  fConst := of_const;
	  fAp := of_ap;
	  fVar := of_var;
	  fNull := of_null;
	  fStackGet := of_stack_get;
	  fStackSet := of_stack_set;
	  fApplySubst := of_apply_subst;
	  fSingleSubst := of_single_subst;
	  fSubst := of_subst;
	  fTruncSubst := of_trunc_subst;
	  
	  open_funcS f := Some f
	}.
  
  Definition typeof_open_func (f : open_func typ) : option typ :=
    match f with
    | of_const t => Some (tyArr t (tyArr tyStack t))
    | of_ap t u => Some (tyArr (tyArr tyStack (tyArr t u)) (tyArr (tyArr tyStack t) (tyArr tyStack u)))
    | of_apply_subst t => Some (tyArr (tyArr tyStack t) (tyArr tySubst (tyArr tyStack t)))
	| of_var _ => Some tyVar
	| of_null => Some tyVal
    | of_stack_get => Some (tyArr tyVar tyExpr)
    | of_stack_set => Some (tyArr tyVar (tyArr tyVal (tyArr tyStack tyStack)))
    | of_single_subst => Some (tyArr tyExpr (tyArr tyVar tySubst))
    | of_subst => Some (tyArr tySubstList tySubst)
    | of_trunc_subst => Some (tyArr tySubstList tySubst)
	end.

  Global Instance RelDec_open_func : RelDec (@eq (open_func typ)) :=
  { rel_dec := fun a b =>
	         match a, b with
	  	       | of_const t, of_const t'
	  	       | of_apply_subst t, of_apply_subst t' => t ?[eq] t'
	  	       | of_ap t u, of_ap t' u' => (t ?[eq] t' && u ?[eq] u')%bool
	  	       | of_var v, of_var v' => v ?[ eq ] v'
	  	       | of_null, of_null
	  	       | of_stack_get, of_stack_get
	  	       | of_stack_set, of_stack_set
	  	       | of_single_subst, of_single_subst
	  	       | of_subst, of_subst
	  	       | of_trunc_subst, of_trunc_subst => true
	  	       | _, _ => false
	         end
  }.

  Global Instance RelDec_Correct_open_func : RelDec_Correct RelDec_open_func.
  Proof.
    constructor.
    destruct x; destruct y; simpl; try rewrite andb_true_iff;
    repeat rewrite rel_dec_correct; try intuition congruence.
  Qed.
  
	Local Instance Applicative_Fun A : Applicative (Fun A) :=
	{ pure := fun _ x _ => x
	; ap := fun _ _ f x y => (f y) (x y)
	}.

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

  Program Definition typ3_cast_bin (a b c d : typ)
  : (typD a -> typD b -> typD c -> typD d) -> typD (tyArr a (tyArr b (tyArr c d))).
  intros.
  unfold tyArr; repeat rewrite typ2_cast. unfold Fun. apply X.
  Defined.

(*
	 Program Definition open_func_symD bf :=
		match bf as bf return match typeof_open_func bf with
								| Some t => typD t
								| None => unit
							  end with
	    | of_cons t => typ2_cast_bin t tyStack t 
	    	(eq_rect_r (fun T : Type => typD t -> T -> typD t) 
	    		(@pure (Fun stack) (Applicative_Fun _) (typD t)) (typ2_cast d r))
  				
	    | of_ap t u => _
	    | of_stack_set => _
	    | of_stack_get => _
	    | of_apply_subst t => _
	    | of_subst => _
	    | of_trunc_subst => _
	 end.
	 Next Obligation.
		apply typ3_cast_bin.
		unfold tyArr. repeat rewrite typ2_cast. unfold Fun.
		apply (@Applicative.ap (Fun stack) (Applicative_Fun _) (typD t) (typD u)).
	 Defined.
	 Next Obligation.
	    apply typ2_cast_bin.
	    unfold tyArr. rewrite typ2_cast.
	    apply (fun (x : typD d) (s : stack) => s x).
	 Defined.
	 Next Obligation.
	 	unfold tyArr; repeat rewrite typ2_cast; unfold Fun.
	 	pose (@stack_add (typD d) _ (@VN typ _ r null)). apply s.
	 Defined.
	 Next Obligation.
		unfold tyArr; repeat rewrite typ2_cast; unfold Fun.
		rewrite stSubst.
		apply (@apply_subst (typD d) (@VN typ _ r null) (typD t)).
	 Defined.
	 Next Obligation.
	    unfold tyArr; rewrite typ2_cast; unfold Fun.
	    rewrite btList, btPair, stSubst; repeat rewrite typ2_cast.
	    apply (@substl_aux (typD d) _ (@VN typ _ r null)).
	 Defined.
	 Next Obligation.
		unfold tyArr; rewrite typ2_cast; unfold Fun.
		rewrite btList, btPair, stSubst. repeat rewrite typ2_cast.
		apply (@substl_trunc_aux (typD d) _ (@VN typ _ r null)).
	 Defined.
*)

	Global Program Instance RSym_OpenFunc : SymI.RSym (open_func typ) := {
	  typeof_sym := typeof_open_func;
	  symD := _;
	  sym_eqb := (fun a b => Some (rel_dec a b))
	}.
	Next Obligation.
		destruct f; simpl.
		+ apply typ2_cast_bin.
		  unfold tyArr. rewrite typ2_cast.
		  apply (@pure (Fun stack) (Applicative_Fun _) (typD t)).
		+ apply typ3_cast_bin.
		  unfold tyArr. repeat rewrite typ2_cast. unfold Fun.
		  apply (@ap (Fun stack) (Applicative_Fun _) (typD t) (typD t0)).
		+ apply t.
		+ apply HV.
		+ apply typ2_cast_bin.
	      unfold tyArr. rewrite typ2_cast.
	      apply (fun (x : typD tyVar) (s : stack) => s x).
		+ unfold tyArr; repeat rewrite typ2_cast; unfold Fun.
	 	  pose (@stack_add (typD tyVar) (typD tyVal) _). apply s.
		+ unfold tyArr; repeat rewrite typ2_cast; unfold Fun.
	  	  rewrite stSubst.
		  apply (@apply_subst (typD tyVar) (typD tyVal) (typD t)).
		+ unfold tyArr; repeat rewrite typ2_cast; unfold Fun.
		  rewrite stSubst.
		  apply (@subst1 (typD tyVar) (typD tyVal) _).
		+ unfold tyArr; rewrite typ2_cast; unfold Fun.
	      rewrite btList, btPair, stSubst; repeat rewrite typ2_cast.
	      apply (@substl_aux (typD tyVar) (typD tyVal) _).
		+ unfold tyArr; rewrite typ2_cast; unfold Fun.
		  rewrite btList, btPair, stSubst. repeat rewrite typ2_cast.
		  apply (@substl_trunc_aux (typD tyVar) (typD tyVal) _ _).
	Defined.

  Global Instance RSymOk_lopen_func : SymI.RSymOk RSym_OpenFunc.
  Proof.
    constructor.
    intros. unfold sym_eqb; simpl.
    consider (a ?[ eq ] b); auto.
  Qed.

End OpenFuncInst.

Section MakeOpen.
	Context {typ func : Type} {HR : RType typ} {HS : SubstType typ}.
	Context {H : OpenFunc typ func} {H1 : ListFunc typ func}
	        {HBT : BaseType typ}.

    Context  {Typ2_tyArr : Typ2 _ Fun}.
    Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

	Definition mkVar (v : typD tyVar) : expr typ func := Inj (fVar v). 
	Definition mkConst (t : typ) (e : expr typ func) := App (fConst t) e.
	Definition mkAp (t u : typ) (f e : expr typ func) := App (App (fAp t u) f) e.
	Definition mkStackGet (x s : expr typ func) := App (App fStackGet x) s.
	Definition mkStackSet (x v s : expr typ func) := App (App (App fStackSet x) v) s.
	Definition mkApplySubst (t : typ) (P s : expr typ func) := App (App (fApplySubst t) P) s.
	Definition mkSingleSubst (e x : expr typ func) := App (App fSingleSubst e) x.
	Definition mkApplySingleSubst t P x e := mkApplySubst t P (mkSingleSubst x e).	
	Definition mkSubst (s : expr typ func) := App fSubst s.
	Definition mkTruncSubst (s : expr typ func) := App fTruncSubst s.
	Definition mkApplyTruncSubst t P s := mkApplySubst t P (mkTruncSubst s).
			
	Fixpoint mkAps f es t :=
		match es with 
			| nil => mkConst t f
			| (e, t')::es => mkAp t' t (mkAps f es (tyArr t' t)) e
		end.

End MakeOpen.
