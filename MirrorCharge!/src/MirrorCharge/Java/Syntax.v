Require Import Java.Language.Lang.
Require Import Java.Logic.AssertionLogic.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.Subst.FMapSubst3.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCharge.ILogicFunc.

Set Implicit Arguments.
Set Strict Implicit.

Inductive typ :=
| tyArr : typ -> typ -> typ
| tyList : typ -> typ
| tyVar : typ
| tyProp : typ.

Fixpoint type_cast_typ (a b : typ) : option (a = b) :=
  match a as a , b as b return option (a = b) with
    | tyProp , tyProp => Some eq_refl
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
    | tyList t, tyList u =>
    	match type_cast_typ t u with
    		| Some pf => 
    		  Some (match pf in _ = a return tyList t = tyList a with
    			| eq_refl => eq_refl
    		  end)
    		| None => None
        end
    | _ , _ => None
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
    | tyList a => list (typD ls a)
    | tyVar => var
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
| pVar (_ : var)
| pEq (_ : typ)
| pNil (_ : typ)
| pCons (_ : typ)
| pAp (_ _ : typ).


Definition func := (SymEnv.func + java_func + ilfunc typ)%type.

Definition typeof_sym_java (f : java_func) : option typ :=
  match f with
    | pVar _ => Some tyVar
    | pNil t => Some (tyList t)
    | pEq t => Some (tyArr t (tyArr t tyProp))
    | pCons t => Some (tyArr t (tyArr (tyList t) (tyList t)))
    | pAp t u => Some (tyArr (tyArr t u) (tyArr t u))
  end.
  
Definition java_func_eq (a b : java_func) : option bool :=
  match a , b with
    | pVar a , pVar b => Some (a ?[ eq ] b)
    | pEq a , pEq b => Some (a ?[ eq ] b)
    | pNil t , pNil u => Some (t ?[ eq ] u)
    | pCons t , pCons u => Some (t ?[ eq ] u) 
    | pAp t u , pAp t' u' => Some (t ?[ eq ] t' && u ?[ eq ] u')%bool
    | _, _ => None
  end.

Instance RSym_imp_func : SymI.RSym java_func :=
{ typeof_sym := typeof_sym_java
; symD := fun ts f =>
            match f as f return match typeof_sym_java f with
                                  | None => unit
                                  | Some t => typD ts t
                                end
            with
              | pVar v => v
              | pEq t => @eq (typD ts t)
              | pNil t => @nil (typD ts t)
              | pCons t => @cons (typD ts t)
              | pAp t u => fun g a => g a
            end
; sym_eqb := java_func_eq
}.

Definition fs : @SymEnv.functions typ _ :=
  SymEnv.from_list
    (@SymEnv.F typ _ (tyArr tyVar (tyArr (tyList tyVar)  tyProp))
               (fun _ => (@In var)) ::
     nil).
     
Definition lops : logic_ops _ :=
  fun t =>
    match t
          return option (forall ts, ILogic.ILogicOps (TypesI.typD ts t))
    with
      | tyProp => Some _
      | _ => None
    end.

Definition eops : embed_ops _ :=
  fun t u =>
    match t as t , u as u
          return option
                   (forall ts : list Type,
                      ILEmbed.EmbedOp (TypesI.typD ts t) (TypesI.typD ts u))
    with
      | _ , _ => None
    end.

Definition subst : Type :=
  FMapSubst3.SUBST.raw (expr typ func).
Definition SS : SubstI3.Subst subst (expr typ func) :=
  @FMapSubst3.SUBST.Subst_subst _.
Definition SU : SubstI3.SubstUpdate subst (expr typ func) :=
  @FMapSubst3.SUBST.SubstUpdate_subst (expr typ func)
                                      (@mentionsU typ func)
                                      (@instantiate typ func).


Local Instance RSym_ilfunc : SymI.RSym (ilfunc typ) :=
  @ILogicFunc.RSym_ilfunc typ _ _ lops eops _ _.

Definition RS : SymI.RSym func :=
  SymSum.RSym_sum (SymSum.RSym_sum (SymEnv.RSym_func fs) _) _.
Local Existing Instance RS.

Let Expr_expr : ExprI.Expr _ (expr typ func) := Expr_expr _ _.
Local Existing Instance Expr_expr.

Definition fVar (v : var) : expr typ func := Inj (inl (inr (pVar v))).
Definition fIn : expr typ func := Inj (inl (inl 1%positive)).
Definition fAp (t u : typ) : expr typ func := Inj (inl (inr (pAp t u))).
Definition fNil t : expr typ func := Inj (inl (inr (pNil t))).
Definition fCons t : expr typ func := Inj (inl (inr (pCons t))).

Definition leq (t : typ) : expr typ func := Inj (inl (inr (pEq t))).
Definition lap (t u : typ) (a b : expr typ func) : expr typ func :=
  App (App (fAp t u) a) b.
Definition mkCons (t : typ) (x xs : expr typ func) :=
  lap (tyList t) (tyList t) (lap t (tyArr (tyList t) (tyList t)) (fCons t) x) xs.
Definition mkIn (x lst : expr typ func) :=
  lap (tyList tyVar) tyProp (lap tyVar (tyArr (tyList tyVar) tyProp) fIn x) lst.

Definition land (l : typ) (e e' : expr typ func) : expr typ func :=
  App (App (Inj (inr (ilf_and l))) e) e'.
Definition ltrue (l : typ) : expr typ func :=
  Inj (inr (ilf_true l)).
Definition lfalse (l : typ) : expr typ func :=
  Inj (inr (ilf_false l)).
Definition lentails (l : typ) (e e' : expr typ func) : expr typ func :=
  App (App (Inj (inr (ilf_entails l))) e) e'.
Definition limpl (l : typ) (e e' : expr typ func) : expr typ func :=
  App (App (Inj (inr (ilf_impl l))) e) e'.
Definition lor (l : typ) (e e' : expr typ func) : expr typ func :=
  App (App (Inj (inr (ilf_or l))) e) e'.
Definition lembed (t f : typ) (e : expr typ func) : expr typ func :=
  App (Inj (inr (ilf_embed f t))) e.
Definition lnot (t : typ) (e : expr typ func) : expr typ func := limpl t e (lfalse t).
Definition lneq (t u : typ) (e e' : expr typ func) : expr typ func :=
	lnot t (lap u t (lap u (tyArr u t) (leq u) e) e').
	
Definition mkeq (t : typ) (e1 e2 : expr typ func) :=
	lap t tyProp (lap t (tyArr t tyProp) (leq t) e1) e2.

