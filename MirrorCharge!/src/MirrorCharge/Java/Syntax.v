Require Import Charge.Logics.BILogic.

Require Import Java.Language.Lang.
Require Import Java.Logic.AssertionLogic.
Require Import Coq.Strings.String.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCharge.ILogicFunc.
Require Import ExtLib.Structures.Applicative.

Require Import Charge.Open.Stack.

Require Import Java.Logic.SpecLogic.
Require Import Java.Logic.AssertionLogic.
Require Import Java.Semantics.OperationalSemantics.
Require Import Java.Language.Program.
Require Import Java.Language.Lang.

Set Implicit Arguments.
Set Strict Implicit.

Local Instance Applicative_Fun A : Applicative (Fun A) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.

Inductive typ :=
| tyArr : typ -> typ -> typ
| tyVarList : typ
| tyVar : typ
| tyVal : typ
| tyString : typ
| tyProp : typ
| tySpec : typ
| tyAsn : typ
| tyProg : typ
| tyStack : typ
| tyCmd : typ
| tyExpr : typ.

Notation "'tyPure'" := (tyArr tyStack tyProp).
Notation "'tySasn'" := (tyArr tyStack tyAsn). 

Fixpoint type_cast_typ (a b : typ) : option (a = b) :=
  match a as a , b as b return option (a = b) with
    | tyProp , tyProp => Some eq_refl
    | tySpec , tySpec => Some eq_refl
    | tyVal, tyVal => Some eq_refl
    | tyProg, tyProg => Some eq_refl
    | tyVarList, tyVarList => Some eq_refl
    | tyArr x y , tyArr a b =>
      match type_cast_typ x a , type_cast_typ y b with
        | Some pf , Some pf' =>
          Some (match pf in _ = t
                    , pf' in _ = t'
                      return tyArr x y = tyArr t t'
                with
                  | eq_refl , eq_refl => eq_refl
                end)
        | _ , _ => None
      end
    | tyVar , tyVar => Some eq_refl
    | tyString, tyString => Some eq_refl
    | tyCmd, tyCmd => Some eq_refl
    | tyExpr, tyExpr => Some eq_refl
    | tyStack, tyStack => Some eq_refl
    | tyAsn, tyAsn => Some eq_refl
    | _, _ => None
  end.

Instance RelDec_eq_typ : RelDec (@eq typ) :=
{ rel_dec := fun a b => match type_cast_typ a b with
                          | None => false
                          | Some _ => true
                        end }.

Fixpoint typD (ls : list Type) (t : typ) : Type :=
  match t with
    | tyArr a b => typD ls a -> typD ls b
    | tyProp => Prop
    | tySpec => spec
    | tyAsn => asn
    | tyVarList => list Lang.var 
    | tyVar => Lang.var
    | tyVal => sval
    | tyString => string
    | tyProg => Prog_wf
    | tyStack => stack
    | tyCmd => cmd
    | tyExpr => dexpr
  end.
  
Inductive tyAcc_typ : typ -> typ -> Prop :=
| tyAcc_tyArrL : forall a b, tyAcc_typ a (tyArr a b)
| tyAcc_tyArrR : forall a b, tyAcc_typ a (tyArr b a).

Instance RType_typ : RType typ :=
{ typD := typD
; tyAcc := tyAcc_typ
; type_cast := fun _ => type_cast_typ
}.

Instance Typ2_Fun : Typ2 _ Fun :=
{ typ2 := tyArr
; typ2_cast := fun _ _ _ => eq_refl
; typ2_match := fun T ts t tr =>
                  match t as t return T (typD ts t) -> T (typD ts t) with
                    | tyArr a b => fun _ => tr a b
                    | _ => fun fa => fa
                  end
}.

Instance Typ0_Prop : Typ0 _ Prop :=
{ typ0 := tyProp
; typ0_cast := fun _ => eq_refl
; typ0_match := fun T ts t tr =>
                  match t as t return T (typD ts t) -> T (typD ts t) with
                    | tyProp => fun _ => tr
                    | _ => fun fa => fa
                  end
}.

Inductive java_func :=
| pVar (_ : Lang.var)
| pString (_ : string)
| pVal (_ : sval)
| pVarList (_ : list Lang.var)
| pProg (_ : Prog_wf)
| pCmd (_ : cmd)
| pExpr (_ : dexpr)
| pEq (_ : typ)

| pAp (_ _ : typ)
| pConst (_ : typ)
| pUpdate (_ : typ)
| pMethodSpec
| pProgEq
| pTriple

| pStackGet
| pStackSet
| pEval

| pStar (_ : typ)
| pPointsto.

Definition func := (SymEnv.func + java_func + ilfunc typ)%type.

Definition typeof_sym_java (f : java_func) : option typ :=
  match f with
    | pVar _ => Some tyVar
    | pString _ => Some tyString
    | pVal _ => Some tyVal
    | pProg _ => Some tyProg
    | pVarList _ => Some tyVarList
    | pCmd _ => Some tyCmd
    | pExpr _ => Some tyExpr
    | pEq t => Some (tyArr t (tyArr t tyProp))
    | pAp t u => Some (tyArr (tyArr tyStack (tyArr t u)) (tyArr (tyArr tyStack t) (tyArr tyStack u)))
    | pUpdate t => Some (tyArr (tyArr tyStack tyStack)
                               (tyArr (tyArr tyStack t)
                                      (tyArr tyStack t)))
    | pConst t => Some (tyArr t (tyArr tyStack t))
    | pMethodSpec => Some (tyArr tyString (tyArr tyString (tyArr tyVarList
    	 (tyArr tyVar (tyArr tySasn (tyArr tySasn tySpec))))))
    | pProgEq => Some (tyArr tyProg tySpec)
    | pStackGet => Some (tyArr tyVar (tyArr tyStack tyVal))
    | pStackSet => Some (tyArr tyVar (tyArr tyVal (tyArr tyStack tyStack)))
    | pTriple => Some (tyArr tySasn (tyArr tySasn (tyArr tyCmd tySpec)))
    | pEval => Some (tyArr tyExpr (tyArr tyStack tyVal))
    
    | pStar tySasn => Some (tyArr tySasn (tyArr tySasn tySasn))
    | pStar tyAsn => Some (tyArr tyAsn (tyArr tyAsn tyAsn))
    | pStar _ => None
    
    | pPointsto => Some (tyArr tyVal (tyArr tyString (tyArr tyVal tyAsn)))
    end.

Definition java_func_eq (a b : java_func) : option bool :=
  match a , b with
    | pVar a , pVar b => Some (a ?[ eq ] b)
    | pVarList a, pVarList b => Some (a ?[ eq ] b)
    | pString a, pString b => Some (a ?[ eq ] b)
    | pCmd a, pCmd b => Some (beq_cmd a b)
    | pExpr e1, pExpr e2 => Some (beq_dexpr e1 e2)
    | pProg a, pProg b => Some true (* THIS IS FALSE! We need an equivalence checker for programs. This should just be syntactic equality. *)
    | pEq a , pEq b => Some (a ?[ eq ] b)
        
    | pAp t u , pAp t' u' => Some (t ?[ eq ] t' && u ?[ eq ] u')%bool
    | pConst t, pConst u => Some (t ?[ eq ] u)
    | pUpdate t, pUpdate u => Some (t ?[ eq ] u)
    | pMethodSpec, pMethodSpec => Some true
    | pProgEq, pProgEq => Some true
    | pStackGet, pStackGet => Some true
    | pStackSet, pStackSet => Some true
    | pTriple, pTriple => Some true
    | pStar t, pStar u => Some (t ?[ eq ] u)
    | pPointsto, pPointsto => Some true
    | _, _ => None
  end.

Let update {T} (f : stack -> stack) (m : stack -> T) (l : stack) : T :=
  m (f l).

Instance RSym_imp_func : SymI.RSym java_func :=
{ typeof_sym := typeof_sym_java
; symD := fun ts f =>
            match f as f return match typeof_sym_java f with
                                  | None => unit
                                  | Some t => typD ts t
                                end
            with
              | pVar v => v
              | pString s => s
              | pProg p => p
              | pVal v => v
              | pVarList lst => lst
              | pCmd c => c
              | pExpr e => e
              | pEq t => @eq (typD ts t)
              
              | pAp t u => @Applicative.ap (Fun stack) (Applicative_Fun _) (typD ts t) (typD ts u)
              | pConst t => @Applicative.pure (Fun stack) (Applicative_Fun _) (typD ts t)
              | pUpdate t => update
              | pMethodSpec => method_spec
              | pProgEq => prog_eq
              | pStackGet => fun x s => s x
              | pStackSet => stack_add
              
              | pTriple => triple
              | pEval => eval
              
              | pStar tySasn => @sepSP _ BILOperatorsSAsn
              | pStar tyAsn => @sepSP _ BILOperatorsAsn
              | pStar _ => tt
              
              | pPointsto => pointsto
            end
; sym_eqb := java_func_eq
}.

Require Import Charge.Logics.ILInsts.

Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.

Definition fs : @SymEnv.functions typ _ :=
  SymEnv.from_list
    (@SymEnv.F typ _ (tyArr tyVar (tyArr tyVarList  tyProp))
               (fun _ => (@In (Lang.var))) ::
     @SymEnv.F typ _ (tyArr tyVarList tyProp)
               (fun _ => (@NoDup (Lang.var))) ::
     nil).

  Definition lops : logic_ops RType_typ :=
  fun t =>
    match t
          return option (forall ts, ILogic.ILogicOps (TypesI.typD ts t))
    with
      | tyProp => Some _
      | tyAsn => Some _
      | tySasn => Some (fun _ => @ILFun_Ops stack asn _)
      | tySpec => Some _
      | tyPure => Some (fun _ => @ILFun_Ops stack Prop _)
      | _ => None
    end.

Definition eops : embed_ops RType_typ :=
  fun t u =>
    match t as t , u as u
          return option
                   (forall ts : list Type,
                      ILEmbed.EmbedOp (TypesI.typD ts t) (TypesI.typD ts u))
    with
      | tyPure, tySasn => Some (fun _ => EmbedSasnPureOp)
      | _ , _ => None
    end.

Local Instance RSym_ilfunc : SymI.RSym (ilfunc typ) :=
  @ILogicFunc.RSym_ilfunc typ RType_typ RelDec_eq_typ lops eops Typ2_Fun Typ0_Prop.

Definition RS : SymI.RSym func :=
  SymSum.RSym_sum (SymSum.RSym_sum (SymEnv.RSym_func fs) _) _.
Local Existing Instance RS.

Instance RTypeOk_typ : @RTypeOk _ RType_typ.
Proof.
	admit.
Qed.

Instance Typ2Ok_typ : Typ2Ok Typ2_Fun.
Proof.
	admit.
Qed.

Instance RSym_ok : SymI.RSymOk RS.
Proof.
	admit.
Qed.

Let Expr_expr : ExprI.Expr _ (expr typ func) := Expr_expr _ _.
Let Expr_ok : @ExprI.ExprOk typ RType_typ (expr typ func) Expr_expr := ExprOk_expr nil.
Local Existing Instance Expr_expr.
Local Existing Instance Expr_ok.

Definition subst : Type :=
  FMapSubst.SUBST.raw (expr typ func).
Definition SS : SubstI.Subst subst (expr typ func) :=
  @FMapSubst.SUBST.Subst_subst _.
Definition SU : SubstI.SubstUpdate subst (expr typ func) :=
  FMapSubst.SUBST.SubstUpdate_subst (@instantiate typ func).
Definition SO : SubstI.SubstOk Expr_expr SS := 
  @FMapSubst.SUBST.SubstOk_subst typ RType_typ (expr typ func) _ _.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance SO.

Notation "'fMethodSpec'" := (Inj (inl (inr pMethodSpec))) (at level 0).
Notation "'fProgEq'" := (Inj (inl (inr pProgEq))) (at level 0).
Notation "'fTriple'" := (Inj (inl (inr pTriple))) (at level 0).
Notation "'fEval'" := (Inj (inl (inr pEval))) (at level 0).

Notation "'fEq' '[' t ']'" := (Inj (inl (inr (pEq t)))) (at level 0).
Notation "'fAp' '[' t ',' u ']'" := (Inj (inl (inr (pAp t u)))) (at level 0).
Notation "'fConst' '[' t ']'" := (Inj (inl (inr (pConst t)))) (at level 0).
Notation "'fstack_get'" := (Inj (inl (inr pStackGet))).
Notation "'fstack_set'" := (Inj (inl (inr pStackSet))).

Definition fupdate t : expr typ func := Inj (inl (inr (pUpdate t))).
Definition fPointsto : expr typ func := Inj (inl (inr (pPointsto))).

Notation "'mkAp' '[' t ',' u ',' a ',' b ']'" := (App (App (fAp [t, u]) a) b) (at level 0).
Notation "'mkMethodSpec' '[' C ',' m ',' args ',' r ',' p ',' q ']'" := 
    (App (App (App (App (App (App fMethodSpec C) m) args) r) p) q) (at level 0).
Notation "'mkTriple' '[' P ',' c ',' Q ']'" := (App (App (App fTriple P) Q) c) (at level 0).
	
Notation "'mkVar' '[' x ']'" := (Inj (inl (inr (pVar x)))) (at level 0).
Notation "'mkVal' '[' v ']'" := (Inj (inl (inr (pVal v)))) (at level 0).
Notation "'mkVarList' '[' lst ']'" := (Inj (inl (inr (pVarList lst)))) (at level 0).
Notation "'mkString' '[' s ']'" := (Inj (inl (inr (pString s)))) (at level 0).
Notation "'mkProg' '[' P ']'" := (Inj (inl (inr (pProg P)))) (at level 0).
Notation "'mkProgEq' '[' P ']'" := (App fProgEq P) (at level 0).
Notation "'mkCmd' '[' c ']'" := (Inj (inl (inr (pCmd c)))) (at level 0).
Notation "'mkExpr' '[' e ']'" := (Inj (inl (inr (pExpr e)))) (at level 0).

Notation "'mkConst' '[' t ',' a ']'" := (App (fConst [t]) a) (at level 0).
Notation "'mkEval' '[' e ',' s ']'" := (App (App fEval e) s) (at level 0).
	
Definition lexists (l t : typ) (e : expr typ func) : expr typ func :=
  App (Inj (inr (ilf_exists t l))) (Abs t e).
Definition land (l : typ) (e e' : expr typ func) : expr typ func :=
  App (App (Inj (inr (ilf_and l))) e) e'.
Definition ltrue (l : typ) : expr typ func :=
  Inj (inr (ilf_true l)).
Definition lfalse (l : typ) : expr typ func :=
  Inj (inr (ilf_false l)).
Notation "'mkEntails' '[' l ',' a ',' b ']'" := (App (App (Inj (inr (ilf_entails l))) a) b) (at level 0).
Definition limpl (l : typ) (e e' : expr typ func) : expr typ func :=
  App (App (Inj (inr (ilf_impl l))) e) e'.
Definition lor (l : typ) (e e' : expr typ func) : expr typ func :=
  App (App (Inj (inr (ilf_or l))) e) e'.
Definition lembed (f t : typ) (e : expr typ func) : expr typ func :=
  App (Inj (inr (ilf_embed f t))) e.
Definition lnot (t : typ) (e : expr typ func) : expr typ func := limpl t e (lfalse t).
Definition lupdate (t : typ) (a b : expr typ func) : expr typ func :=
  App (App (fupdate t) a) b.
Definition lstackGet (x s : expr typ func) := App (App fstack_get x) s.
Definition lstackSet (x v s : expr typ func) := App (App (App fstack_set x) v) s.

Definition lstar (l : typ) (e e' : expr typ func) : expr typ func :=
  App (App (Inj (inl (inr (pStar l)))) e) e'.
Definition lpointsto (v f v' : expr typ func) := 
	App (App (App fPointsto v) f) v'.
	
Definition test_lemma :=
  @lemmaD typ RType_typ (expr typ func) Expr_expr (expr typ func)
          (fun tus tvs e => exprD' nil tus tvs tyProp e)
          tyProp
          (fun x => x) nil nil.

          