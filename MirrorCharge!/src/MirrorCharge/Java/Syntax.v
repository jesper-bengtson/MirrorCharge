Require Import Coq.Strings.String.

Require Import Charge.Open.Stack.
Require Import Charge.Open.Subst.
Require Import Charge.Open.Open.
Require Import Charge.Logics.Later.
Require Import Charge.Logics.BILogic.

Require Import Java.Language.Lang.
Require Import Java.Logic.AssertionLogic.
Require Import Java.Logic.SpecLogic.
Require Import Java.Logic.AssertionLogic.
Require Import Java.Semantics.OperationalSemantics.
Require Import Java.Language.Program.
Require Import Java.Language.Lang.

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

Set Implicit Arguments.
Set Strict Implicit.

Local Instance Applicative_Fun A : Applicative (Fun A) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.

Inductive typ :=
| tyArr : typ -> typ -> typ
| tyList : typ -> typ
| tyPair : typ -> typ -> typ
| tyVal : typ
| tyString : typ
| tyNat : typ
| tyProp : typ
| tySpec : typ
| tyAsn : typ
| tyProg : typ
| tyStack : typ
| tyCmd : typ
| tyFields : typ
| tyExpr : typ
| tySubst : typ. 

Notation "'tyPure'" := (tyArr tyStack tyProp).
Notation "'tySasn'" := (tyArr tyStack tyAsn). 

Notation "'tyVarList'" := (tyList tyString).
Notation "'tyExprList'" := (tyList tyExpr).
Notation "'tySubstList'" := (tyList (tyPair tyString (tyArr tyStack tyVal))).

Fixpoint type_cast_typ (a b : typ) : option (a = b) :=
  match a as a , b as b return option (a = b) with
    | tyProp , tyProp => Some eq_refl
    | tySpec , tySpec => Some eq_refl
    | tyVal, tyVal => Some eq_refl
    | tyProg, tyProg => Some eq_refl
    | tyNat, tyNat => Some eq_refl
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
    | tyPair x y , tyPair a b =>
      match type_cast_typ x a , type_cast_typ y b with
        | Some pf , Some pf' =>
          Some (match pf in _ = t
                    , pf' in _ = t'
                      return tyPair x y = tyPair t t'
                with
                  | eq_refl , eq_refl => eq_refl
                end)
        | _ , _ => None
      end
    | tyList x, tyList y =>
    	match type_cast_typ x y with
          | Some pf =>
    		Some (match pf in _ = t return tyList x = tyList t with
    			    | eq_refl => eq_refl
    			  end)
          | None => None
       end  
    | tyString, tyString => Some eq_refl
    | tyCmd, tyCmd => Some eq_refl
    | tyExpr, tyExpr => Some eq_refl
    | tyStack, tyStack => Some eq_refl
    | tyAsn, tyAsn => Some eq_refl
    | tyFields, tyFields => Some eq_refl
    | tySubst, tySubst => Some eq_refl

    | _, _ => None
  end.
  
Lemma type_cast_typ_sound (a b : typ) :
	(exists pf, type_cast_typ a b = Some pf) <->
	a = b.
Proof.
  split; intros H.
  + destruct a, b; destruct H as [x _]; inversion x; subst; reflexivity.
  + subst. exists eq_refl. induction b; try reflexivity.
    simpl. rewrite IHb1, IHb2. reflexivity.
    simpl. rewrite IHb. reflexivity.
    simpl. rewrite IHb1, IHb2. reflexivity.
Qed.

Instance RelDec_eq_typ : RelDec (@eq typ) :=
{ rel_dec := fun a b => match type_cast_typ a b with
                          | None => false
                          | Some _ => true
                        end }.

Lemma type_cast_typ_refl (a : typ) : type_cast_typ a a = Some eq_refl.
Proof.
  induction a; simpl; try reflexivity.
  rewrite IHa1, IHa2; reflexivity.
  rewrite IHa. reflexivity.
  rewrite IHa1, IHa2; reflexivity.
Qed.

Instance RelDec_correct_typ : RelDec_Correct RelDec_eq_typ.
Proof.
	split; intros x y.
	destruct x, y; simpl; split; intro H; inversion H; subst; try reflexivity.
	+ remember (type_cast_typ x1 y1); destruct o; subst; [|inversion H].
	  remember (type_cast_typ x2 y2); destruct o; subst; [|inversion H].
	  reflexivity.
	+ do 2 rewrite type_cast_typ_refl; reflexivity.
	+ remember (type_cast_typ x y); destruct o; subst; [|inversion H].
	  reflexivity.
	+ rewrite type_cast_typ_refl. reflexivity.
	+ remember (type_cast_typ x1 y1); destruct o; subst; [|inversion H].
	  remember (type_cast_typ x2 y2); destruct o; subst; [|inversion H].
	  reflexivity.
	+ do 2 rewrite type_cast_typ_refl; reflexivity.	
Qed.

Fixpoint typD  (t : typ) : Type :=
  match t with
    | tyArr a b => typD a -> typD b
	| tyList a => @list (typD a)
	| tyPair a b => (typD a * typD b)%type
    | tyProp => Prop
    | tyNat => nat
    | tySpec => spec
    | tyAsn => asn
    | tyVal => sval
    | tyString => string
    | tyProg => Prog_wf
    | tyStack => stack
    | tyCmd => cmd
    | tyFields => SS.t
    | tyExpr => dexpr
    | tySubst => @Subst.subst (String.string) SVal
  end.

Definition inhabited_typ (t : typ) := true.

Require Import ILogic.

Lemma inhabited_typ_sound (t : typ) (H : inhabited_typ t = true) : Inhabited (typD t).
Proof.
  induction t; simpl in *.
  + assert (inhabited_typ t2 = true) by reflexivity.
    specialize (IHt2 H0). destruct IHt2; destruct cinhabited. 
    repeat split; intros; assumption.
  + repeat split. apply nil.
  + assert (inhabited_typ t1 = true) by reflexivity.
  	assert (inhabited_typ t2 = true) by reflexivity.
  	specialize (IHt1 H0); specialize (IHt2 H1).
  	destruct IHt1; destruct cinhabited as [a].
  	destruct IHt2; destruct cinhabited as [b].
  	repeat split; assumption.
  + repeat split; apply null.
  + repeat split; apply EmptyString.
  + apply _.
  + repeat split; apply True.
  + repeat split; apply ltrue.
  + repeat split; apply ltrue.
  + repeat split. admit.
  + repeat split; intros. intro. apply null.
  + repeat split; apply cskip.
  + repeat split; apply SS.empty.
  + repeat split; apply (E_val null).
  + repeat split; intros. intros x s. apply null.
Qed.

Inductive tyAcc_typ : typ -> typ -> Prop :=
| tyAcc_tyArrL : forall a b, tyAcc_typ a (tyArr a b)
| tyAcc_tyArrR : forall a b, tyAcc_typ a (tyArr b a).

Instance RType_typ : RType typ :=
{ typD := typD
; tyAcc := tyAcc_typ
; type_cast := type_cast_typ
}.

Instance Typ2_Fun : Typ2 _ Fun :=
{ typ2 := tyArr
; typ2_cast := fun _ _ => eq_refl
; typ2_match := fun T t tr =>
                  match t as t return T (typD t) -> T (typD t) with
                    | tyArr a b => fun _ => tr a b
                    | _ => fun fa => fa
                  end
}.

Instance Typ0_Prop : Typ0 _ Prop :=
{ typ0 := tyProp
; typ0_cast := eq_refl
; typ0_match := fun T t tr =>
                  match t as t return T (typD t) -> T (typD t) with
                    | tyProp => fun _ => tr
                    | _ => fun fa => fa
                  end
}.

Inductive java_func :=
| pString (_ : string)
| pVal (_ : sval)
| pVarList (_ : list String.string) 
| pProg (_ : Prog_wf)
| pCmd (_ : cmd)
| pExpr (_ : dexpr)
| pEq (_ : typ)
| pFields (_ : SS.t)

| pAp (_ _ : typ)
| pConst (_ : typ)
| pApplySubst (_ : typ)
| pMethodSpec
| pProgEq
| pTriple

| pTypeOf

| pStackGet
| pStackSet
| pEval

| pFieldLookup

| pSetFold (_ : typ)
| pSetFoldFun 

| pStar (_ : typ)
| pEmp (_ : typ)
| pLater (_ : typ)
| pPointsto

| pZip (_ _ : typ)
| pSubst
| pTruncSubst
| pSingleSubst

| pCons (_ : typ)
| pNil (_ : typ)
| pLength (_ : typ)
| pMap (_ _ : typ)

| pNull.

Definition func := (SymEnv.func + java_func + ilfunc typ)%type.

Definition typeof_sym_java (f : java_func) : option typ :=
  match f with
    | pString _ => Some tyString
    | pVal _ => Some tyVal
    | pVarList _ => Some tyVarList
    | pProg _ => Some tyProg
    | pCmd _ => Some tyCmd
    | pExpr _ => Some tyExpr
    | pFields _ => Some tyFields
    | pEq t => Some (tyArr t (tyArr t tyProp))
    | pAp t u => Some (tyArr (tyArr tyStack (tyArr t u)) (tyArr (tyArr tyStack t) (tyArr tyStack u)))
    | pApplySubst t => Some (tyArr (tyArr tyStack t) (tyArr tySubst (tyArr tyStack t)))

    | pConst t => Some (tyArr t (tyArr tyStack t))
    | pMethodSpec => Some (tyArr tyString (tyArr tyString (tyArr tyVarList
    	 (tyArr tyString (tyArr tySasn (tyArr tySasn tySpec))))))
    | pProgEq => Some (tyArr tyProg tySpec)
    | pStackGet => Some (tyArr tyString (tyArr tyStack tyVal))
    | pStackSet => Some (tyArr tyString (tyArr tyVal (tyArr tyStack tyStack)))
    | pTriple => Some (tyArr tySasn (tyArr tySasn (tyArr tyCmd tySpec)))
    | pEval => Some (tyArr tyExpr (tyArr tyStack tyVal))
    
    | pStar tySasn => Some (tyArr tySasn (tyArr tySasn tySasn))
    | pStar tyAsn => Some (tyArr tyAsn (tyArr tyAsn tyAsn))
    | pStar _ => None
    
    | pEmp tySasn => Some tySasn
    | pEmp tyAsn => Some tyAsn
    | pEmp _ => None

    | pLater tySpec => Some (tyArr tySpec tySpec)
    | pLater _ => None
    
    | pTypeOf => Some (tyArr tyString (tyArr tyVal tyProp))
    
    | pFieldLookup => Some (tyArr tyProg (tyArr tyString (tyArr tyFields tyProp)))
    
    | pSetFoldFun => Some (tyArr tyString (tyArr tyString (tyArr tySasn tySasn)))
    | pSetFold t => Some (tyArr (tyArr tyString (tyArr t t)) (tyArr tyFields (tyArr t t)))
    
    | pPointsto => Some (tyArr tyVal (tyArr tyString (tyArr tyVal tyAsn)))
    
    | pZip a b => Some (tyArr (tyList a) (tyArr (tyList b) (tyList (tyPair a b))))
    | pSubst => Some (tyArr tySubstList tySubst)
    | pTruncSubst => Some (tyArr tySubstList tySubst)
    | pSingleSubst => Some (tyArr (tyArr tyStack tyVal) (tyArr tyString tySubst))
    
    | pCons t => Some (tyArr t (tyArr (tyList t) (tyList t)))
    | pNil t => Some (tyList t)
    | pLength t => Some (tyArr (tyList t) tyNat)
    | pMap a b => Some (tyArr (tyArr a b) (tyArr (tyList a) (tyList b)))

    | pNull => Some tyVal
    end.
    
Fixpoint beq_list {A} (f : A -> A -> bool) (xs ys : list A) :=
	match xs, ys with
		| nil, nil => true
		| x::xs, y :: ys => andb (f x y) (beq_list f xs ys)
		| _, _ => false
	end.

Definition java_func_eq (a b : java_func) : option bool :=
  match a , b with
    | pString a, pString b => Some (a ?[ eq ] b)
	| pVal a, pVal b => Some (beq_val a b)
    | pVarList a, pVarList b => Some (beq_list beq_string a b)
    | pProg a, pProg b => Some true (* THIS IS FALSE! We need an equivalence checker for programs. This should just be syntactic equality. *)
    | pCmd a, pCmd b => Some (beq_cmd a b)
    | pExpr e1, pExpr e2 => Some (beq_dexpr e1 e2)
    | pEq a , pEq b => Some (a ?[ eq ] b)
    | pFields a, pFields b => Some (SS.equal a b)
        
    | pAp t u , pAp t' u' => Some (t ?[ eq ] t' && u ?[ eq ] u')%bool
    | pConst t, pConst u => Some (t ?[ eq ] u)
    | pApplySubst t, pApplySubst u => Some (t ?[ eq ] u)            
    | pMethodSpec, pMethodSpec => Some true
    | pProgEq, pProgEq => Some true
	| pTriple, pTriple => Some true

    | pTypeOf, pTypeOf => Some true

    | pStackGet, pStackGet => Some true
    | pStackSet, pStackSet => Some true
	| pEval, pEval => Some true

    | pStar t, pStar u => Some (t ?[ eq ] u)
    | pEmp t, pEmp u => Some (t ?[ eq ] u)
    | pLater t, pLater u => Some (t ?[ eq ] u)
    | pPointsto, pPointsto => Some true
    | pFieldLookup, pFieldLookup => Some true
    | pSetFold t, pSetFold u => Some (t ?[ eq ] u)
    | pSetFoldFun, pSetFoldFun => Some true

	| pZip a b, pZip c d => Some (a ?[ eq ] c && b ?[ eq ] d)%bool
        
    | pSubst, pSubst => Some true
    | pTruncSubst, pTruncSubst => Some true
    | pSingleSubst, pSingleSubst => Some true
    
    | pCons t, pCons u => Some (t ?[ eq ] u)
    | pNil t, pNil u => Some (t ?[ eq ] u)
    | pLength t, pLength u => Some (t ?[ eq ] u)
    | pMap a b, pMap c d => Some (a ?[ eq ] c && b ?[ eq ] d)%bool

    | pNull, pNull => Some true
    | _, _ => None
  end.

Definition java_func_eq_sound a b :
	java_func_eq a b = Some true <-> a = b.
Proof.
  split; intros H.
  + destruct a, b; simpl in *; inversion H; subst; clear H;
  	(try rewrite rel_dec_correct in H1); subst; try reflexivity; admit.
  + subst.
  	destruct b; simpl; try reflexivity; f_equal; 
  		try (apply rel_dec_eq_true; [apply _ | reflexivity]); admit.
Qed.

Definition set_fold_fun (x : String.string) (f : field) (P : sasn) :=
	(`pointsto) (x/V) `f `null ** P.

Definition stack_get (x : string) (s : stack) := s x.

Instance RSym_imp_func : SymI.RSym java_func :=
{ typeof_sym := typeof_sym_java
; symD := fun f =>
            match f as f return match typeof_sym_java f with
                                  | None => unit
                                  | Some t => typD t
                                end
            with
              | pString s => s
              | pProg p => p
              | pVal v => v
              | pVarList vs => vs
              | pCmd c => c
              | pExpr e => e
              | pFields fs => fs
              | pEq t => @eq (typD t)
              
              | pAp t u => @Applicative.ap (Fun stack) (Applicative_Fun _) (typD t) (typD u)
              | pConst t => @Applicative.pure (Fun stack) (Applicative_Fun _) (typD t)
              | pMethodSpec => method_spec
              | pProgEq => prog_eq
              | pStackGet => stack_get
              | pStackSet => stack_add
              
              | pApplySubst t => @apply_subst (String.string) SVal (typD t)
              
              | pTriple => triple
              | pEval => eval
              
              | pTypeOf => typeof
              
              | pStar tySasn => @sepSP _ _
              | pStar tyAsn => @sepSP _ _
              | pStar _ => tt
              
              | pEmp tySasn => @empSP _ _
              | pEmp tyAsn => @empSP _ _
              | pEmp _ => tt
              
              | pLater tySpec => @illater _ _
              | pLater _ => tt
              
              | pFieldLookup => field_lookup
              | pSetFold t => @SS.fold (typD t)
              | pSetFoldFun => set_fold_fun
              
              | pPointsto => pointsto
              
              | pZip a b => @zip (typD a) (typD b)
              | pSubst => @substl_aux  String.string _ SVal
              | pTruncSubst => @substl_trunc_aux String.string _ SVal
              | pSingleSubst => @subst1 String.string _ SVal
              
              | pCons t => @cons (typD t)
              | pNil t => @nil (typD t)
              | pLength t => @length (typD t)
              | pMap a b => @map (typD a) (typD b)
  
              | pNull => null
            end
; sym_eqb := java_func_eq
}.

Require Import Charge.Logics.ILInsts.

Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.

Definition fs : @SymEnv.functions typ _ :=
  SymEnv.from_list
    (@SymEnv.F typ _ (tyArr tyString (tyArr tyVarList  tyProp))
               (@In string) ::
     @SymEnv.F typ _ (tyArr tyVarList tyProp)
               (@NoDup string) ::
     nil).

Definition should_not_be_necessary : ILogicOps (TypesI.typD tySpec).
Proof.
  simpl.
  apply _.
Qed.

  Definition lops : logic_ops RType_typ :=
  fun t =>
    match t
          return option (ILogic.ILogicOps (TypesI.typD t))
    with
      | tyProp => Some _
      | tyAsn => Some _
      | tySasn => Some (@ILFun_Ops stack asn _)
      | tySpec => Some should_not_be_necessary
      | tyPure => Some ( @ILFun_Ops stack Prop _)
      | _ => None
    end.

Definition eops : embed_ops RType_typ :=
  fun t u =>
    match t as t , u as u
          return option
                   (ILEmbed.EmbedOp (TypesI.typD t) (TypesI.typD u))
    with
      | tyPure, tySasn => Some EmbedSasnPureOp
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

Let Expr_expr : ExprI.Expr _ (expr typ func) := @Expr_expr typ func _ _ _.
Let Expr_ok : @ExprI.ExprOk typ RType_typ (expr typ func) Expr_expr := ExprOk_expr.
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
(*
Definition fMethodSpec : expr typ func := Inj (inl (inr pMethodSpec)).
Definition fProgEq : expr typ func := Inj (inl (inr pProgEq)).
Definition fTriple : expr typ func := Inj (inl (inr pTriple)).
Definition fEval : expr typ func := Inj (inl (inr pEval)).

Definition fEq t : expr typ func := Inj (inl (inr (pEq t))).
Definition fAp t u : expr typ func := Inj (inl (inr (pAp t u))).
Definition fConst t : expr typ func := Inj (inl (inr (pConst t))).
Definition fStackGet : expr typ func := Inj (inl (inr pStackGet)).
Definition fStackSet : expr typ func := Inj (inl (inr pStackSet)).

Definition fFieldLookup : expr typ func := Inj (inl (inr pFieldLookup)).
Definition fSetFold : expr typ func := Inj (inl (inr pSetFold)).
Definition fSetFoldFun : expr typ func := Inj (inl (inr pSetFoldFun)).

Definition fLengthVarList : expr typ func := Inj (inl (inr pLengthVarList)).
Definition fLengthExprList : expr typ func := Inj (inl (inr pLengthExprList)).

Definition fTypeOf : expr typ func := Inj (inl (inr pTypeOf)).

Definition fApplySubst t : expr typ func := Inj (inl (inr (pApplySubst t))).
Definition fPointsto : expr typ func := Inj (inl (inr (pPointsto))).
Definition fNull : expr typ func := Inj (inl (inr pNull)).

Definition fNilVarList : expr typ func := Inj (inl (inr pNilVarList)).
Definition fNilExprList : expr typ func := Inj (inl (inr pNilExprList)).
Definition fConsVarList : expr typ func:= Inj (inl (inr pConsVarList)).
Definition fConsExprList : expr typ func:= Inj (inl (inr pConsExprList)).
	
Definition fVal v : expr typ func := Inj (inl (inr (pVal v))).
Definition fVarList lst : expr typ func := Inj (inl (inr (pVarList lst))).

Definition fString s : expr typ func:= Inj (inl (inr (pString s))).
Definition fProg P : expr typ func:= Inj (inl (inr (pProg P))).

Definition fCmd c : expr typ func := Inj (inl (inr (pCmd c))).
Definition fExpr e : expr typ func := Inj (inl (inr (pExpr e))).
Definition fFields fs : expr typ func := Inj (inl (inr (pFields fs))).

Definition fExprList lst : expr typ func := fold_right (fun e acc => App (App fConsExprList (App fEval (fExpr e))) acc) fNilExprList lst.

Definition fExists l t : expr typ func := Inj (inr (ilf_exists l t)).
Definition fForall l t : expr typ func := Inj (inr (ilf_forall l t)).
Definition fAnd l : expr typ func := Inj (inr (ilf_and l)).
Definition fOr l : expr typ func := Inj (inr (ilf_or l)).
Definition fImpl l : expr typ func := Inj (inr (ilf_impl l)).
Definition fTrue l : expr typ func := Inj (inr (ilf_true l)).
Definition fFalse l : expr typ func := Inj (inr (ilf_false l)).
Definition fEntails l : expr typ func := Inj (inr (ilf_entails l)).

Definition fEmbed (f t : typ) : expr typ func := Inj (inr (ilf_embed f t)).

Definition fSingleSubst : expr typ func := Inj (inl (inr pSingleSubst)).
Definition fSubst : expr typ func := Inj (inl (inr pSubst)).
Definition fTruncSubst : expr typ func := Inj (inl (inr pTruncSubst)).
                                                         
Definition fStar l : expr typ func := Inj (inl (inr (pStar l))).
Definition fEmp l : expr typ func:= Inj (inl (inr (pEmp l))).
	*)
	
Definition fMethodSpec : expr typ func := Inj (inl (inr pMethodSpec)).
Definition fProgEq : expr typ func := Inj (inl (inr pProgEq)).
Definition fTriple : expr typ func := Inj (inl (inr pTriple)).
Definition fEval : expr typ func := Inj (inl (inr pEval)).

Definition fEq t : expr typ func := Inj (inl (inr (pEq t))).
Definition fAp t u : expr typ func := Inj (inl (inr (pAp t u))).
Definition fConst t : expr typ func := Inj (inl (inr (pConst t))).
Definition fStackGet : expr typ func := Inj (inl (inr pStackGet)).
Definition fStackSet : expr typ func := Inj (inl (inr pStackSet)).

Definition fFieldLookup : expr typ func := Inj (inl (inr pFieldLookup)).
Definition fSetFold t : expr typ func := Inj (inl (inr (pSetFold t))).
Definition fSetFoldFun : expr typ func := Inj (inl (inr pSetFoldFun)).

Definition fLength t : expr typ func := Inj (inl (inr (pLength t))).
Definition fNil t : expr typ func := Inj (inl (inr (pNil t))).
Definition fCons t : expr typ func := Inj (inl (inr (pCons t))).
Definition fZip t u : expr typ func := Inj (inl (inr (pZip t u))).
Definition fMap t u : expr typ func := Inj (inl (inr (pMap t u))).

Definition fTypeOf : expr typ func := Inj (inl (inr pTypeOf)).

Definition fApplySubst t : expr typ func := Inj (inl (inr (pApplySubst t))).
Definition fPointsto : expr typ func := Inj (inl (inr (pPointsto))).
Definition fNull : expr typ func := Inj (inl (inr pNull)).

Definition fSingleSubst : expr typ func := Inj (inl (inr pSingleSubst)).
Definition fSubst : expr typ func := Inj (inl (inr pSubst)).
Definition fTruncSubst : expr typ func := Inj (inl (inr pTruncSubst)).

Definition mkAp t u a b : expr typ func := App (App (fAp t u) a) b.
Definition mkMethodSpec C m args r P Q : expr typ func := 
    App (App (App (App (App (App fMethodSpec C) m) args) r) P) Q.
Definition mkTriple P c Q : expr typ func := App (App (App fTriple P) Q) c.
Definition mkFieldLookup P C f : expr typ func := App (App (App fFieldLookup P) C) f.
Definition mkSetFold t x f P : expr typ func := App (App (App (fSetFold t) (App fSetFoldFun x)) f) P. 
Definition mkTypeOf C x : expr typ func := App (App fTypeOf C) x.

Definition mkCons t x xs : expr typ func := App (App (fCons t) x) xs.
Definition mkLength t lst : expr typ func := App (fLength t) lst.
Definition mkZip t u xs ys : expr typ func := App (App (fZip t u) xs) ys.

Definition mkVal v : expr typ func := Inj (inl (inr (pVal v))).
Definition mkVarList lst : expr typ func := Inj (inl (inr (pVarList lst))).

Definition mkString s : expr typ func := Inj (inl (inr (pString s))).
Definition mkProg P : expr typ func := Inj (inl (inr (pProg P))).
Definition mkProgEq P : expr typ func := App fProgEq P.
Definition mkCmd c : expr typ func := Inj (inl (inr (pCmd c))).
Definition mkExpr e : expr typ func := Inj (inl (inr (pExpr e))).
Definition mkFields fs : expr typ func := Inj (inl (inr (pFields fs))).

Definition mkExprList es : expr typ func :=
	(fold_right (fun (e : dexpr) (acc : expr typ func) => 
		mkCons tyExpr (mkExpr e) acc) (fNil tyExpr) es).


Definition mkConst t a : expr typ func := App (fConst t) a.
Definition mkEval e s : expr typ func := App (App fEval e) s.


Definition mkEq t a b : expr typ func := App (App (fEq t) a) b.

Definition fExists l t : expr typ func := Inj (inr (ilf_exists t l)).
Definition fForall l t : expr typ func := Inj (inr (ilf_forall t l)).
Definition fAnd l : expr typ func := Inj (inr (ilf_and l)).
Definition fOr l : expr typ func := Inj (inr (ilf_or l)).
Definition fImpl l : expr typ func := Inj (inr (ilf_impl l)).
Definition fEntails l : expr typ func := Inj (inr (ilf_entails l)).

Definition fLater l : expr typ func := Inj (inl (inr (pLater l))).

Definition mkExists l t f : expr typ func := App (fExists l t) (Abs t f).
Definition mkForall l t f : expr typ func := App (fForall l t) (Abs t f).
Definition mkAnd l P Q : expr typ func := App (App (fAnd l) P) Q.
Definition mkOr l P Q : expr typ func := App (App (fOr l) P) Q.
Definition mkImpl l P Q : expr typ func := App (App (fImpl l) P) Q.
Definition mkTrue l : expr typ func := Inj (inr (ilf_true l)).
Definition mkFalse l : expr typ func := Inj (inr (ilf_false l)).
Definition mkNot l P : expr typ func := mkImpl l P (mkFalse l).
Definition mkEntails l P Q : expr typ func := App (App (fEntails l) P) Q.

Definition fEmbed l1 l2 : expr typ func := (Inj (inr (ilf_embed l1 l2))).
Definition mkEmbed l1 l2 P : expr typ func := (App (fEmbed l1 l2) P).

Definition mkStackGet x s  := App (App fStackGet x) s.
Definition mkStackSet x v s : expr typ func := App (App (App fStackSet x) v) s.

Definition fApply t : expr typ func := Inj (inl (inr (pApplySubst t))).

Definition mkApplySubst t P s : expr typ func := App (App (fApplySubst t) P) s.

Definition mkSingleSubst x e : expr typ func := App (App fSingleSubst e) x.
Definition mkApplySingleSubst t P x e : expr typ func := mkApplySubst t P (mkSingleSubst e x).

Definition mkSubst s : expr typ func := App fSubst s.

Definition mkTruncSubst s : expr typ func := App fTruncSubst s.
Definition mkApplyTruncSubst t P s : expr typ func := mkApplySubst t P (mkTruncSubst s).

Definition mkSubstList vs es : expr typ func := mkZip tyString (tyArr tyStack tyVal) vs (mkExprList es).

Definition mkNull : expr typ func := Inj (inl (inr pNull)).

Definition fStar l : expr typ func := Inj (inl (inr (pStar l))).

Definition mkStar l P Q : expr typ func := App (App (fStar l) P) Q.
Definition mkEmp l : expr typ func := Inj (inl (inr (pEmp l))).
Definition mkPointsto (v f v' : expr typ func) := 
	App (App (App fPointsto v) f) v'.

Definition test_lemma :=
  @lemmaD typ RType_typ (expr typ func) Expr_expr (expr typ func)
          (fun tus tvs e => exprD' tus tvs tyProp e)
          tyProp
          (fun x => x) nil nil.

          