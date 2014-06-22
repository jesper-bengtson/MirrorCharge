Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Nat.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.STac.STac.
Require Import MirrorCore.provers.DefaultProver.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.Subst.FMapSubst3.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCharge.ILogicFunc.
Require Import MirrorCharge.Imp.Imp.

Set Implicit Arguments.
Set Strict Implicit.

Inductive typ :=
| tyArr : typ -> typ -> typ
| tyLocals
| tyCmd
| tyHProp
| tyProp
| tyVariable
| tyExpr
| tyNat.

Fixpoint type_cast_typ (a b : typ) : option (a = b) :=
  match a as a , b as b return option (a = b) with
    | tyLocals , tyLocals => Some eq_refl
    | tyCmd , tyCmd => Some eq_refl
    | tyHProp , tyHProp => Some eq_refl
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
    | tyExpr , tyExpr => Some eq_refl
    | tyNat , tyNat => Some eq_refl
    | tyVariable , tyVariable => Some eq_refl
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
    | tyLocals => locals
    | tyCmd => icmd
    | tyHProp => HProp
    | tyProp => Prop
    | tyVariable => var
    | tyExpr => iexpr
    | tyNat => nat
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


Inductive imp_func :=
| pVar (_ : var)
| pNat (_ : nat)
| pLocals_get | pLocals_upd
| pEq (_ : typ)
| pEval_expri
| eVar | eConst
  (** Below here isn't really imp functions **)
| pAp (_ _ : typ)
| pPure (_ : typ)
| pUpdate (_ : typ)
| pEmp (_ : typ)
| pStar (_ : typ).

Definition func := (SymEnv.func + imp_func + ilfunc typ)%type.

Definition typeof_sym_imp (f : imp_func) : option typ :=
  match f with
    | pVar _ => Some tyVariable
    | pNat _ => Some tyNat
    | pLocals_get => Some (tyArr tyVariable (tyArr tyLocals tyNat))
    | pLocals_upd => Some (tyArr tyVariable (tyArr tyNat (tyArr tyLocals tyLocals)))
    | pEq t => Some (tyArr t (tyArr t tyProp))
    | pEval_expri => Some (tyArr tyExpr (tyArr tyLocals tyNat))
    | eVar => Some (tyArr tyVariable tyExpr)
    | eConst => Some (tyArr tyNat tyExpr)
    | pAp t u => Some (tyArr (tyArr tyLocals (tyArr t u)) (tyArr (tyArr tyLocals t) (tyArr tyLocals u)))
    | pPure t => Some (tyArr t (tyArr tyLocals t))
    | pUpdate t => Some (tyArr (tyArr tyLocals tyLocals)
                               (tyArr (tyArr tyLocals t)
                                      (tyArr tyLocals t)))
    | pStar tyHProp =>
      let t := tyHProp in
      Some (tyArr t (tyArr t t))
    | pStar (tyArr tyLocals tyHProp) =>
      let t := (tyArr tyLocals tyHProp) in
      Some (tyArr t (tyArr t t))
    | pStar _ => None
    | pEmp tyHProp =>
      let t := tyHProp in Some t
    | pEmp (tyArr tyLocals tyHProp) =>
      let t := (tyArr tyLocals tyHProp) in Some t
    | pEmp _ => None
  end.

Definition imp_func_eq (a b : imp_func) : option bool :=
  match a , b with
    | pVar a , pVar b => Some (a ?[ eq ] b)
    | pNat a , pNat b => Some (a ?[ eq ] b)
    | pLocals_get , pLocals_get => Some true
    | pLocals_upd , pLocals_upd => Some true
    | pEq a , pEq b => Some (a ?[ eq ] b)
    | pEval_expri , pEval_expri => Some true
    | eVar , eVar => Some true
    | eConst , eConst => Some true
    | pAp t u , pAp t' u' => Some (t ?[ eq ] t' && u ?[ eq ] u')%bool
    | pPure t , pPure t' => Some (t ?[ eq ] t')
    | pUpdate t , pUpdate t' => Some (t ?[ eq ] t')
    | pStar t , pStar t' => Some (t ?[ eq ] t')
    | pEmp t , pEmp t' => Some (t ?[ eq ] t')
    | _ , _ => Some false
  end.

Let update {T} (f : locals -> locals) (m : locals -> T) (l : locals) : T :=
  m (f l).

Instance RSym_imp_func : SymI.RSym imp_func :=
{ typeof_sym := typeof_sym_imp
; symD := fun ts f =>
            match f as f return match typeof_sym_imp f with
                                  | None => unit
                                  | Some t => typD ts t
                                end
            with
              | pVar v => v
              | pNat n => n
              | pLocals_get => locals_get
              | pLocals_upd => locals_upd
              | pEq t => @eq _
              | pEval_expri => eval_iexpr
              | eVar => iVar
              | eConst => iConst
              | pPure t =>
                @Applicative.pure (Fun locals) (Applicative_Fun _) (typD ts t)
              | pAp t u =>
                @Applicative.ap (Fun locals) (Applicative_Fun _) (typD ts t) (typD ts u)
              | pUpdate t => update
              | pStar tyHProp => BILogic.sepSP
              | pStar (tyArr tyLocals tyHProp) =>
                @BILogic.sepSP _ BILOps
              | pStar _ => tt
              | pEmp tyHProp => BILogic.empSP
              | pEmp (tyArr tyLocals tyHProp) =>
                @BILogic.empSP _ BILOps
              | pEmp _ => tt

            end
; sym_eqb := imp_func_eq
}.

Definition subst : Type :=
  FMapSubst3.SUBST.raw (expr typ func).
Definition SS : SubstI3.Subst subst (expr typ func) :=
  @FMapSubst3.SUBST.Subst_subst _.
Definition SU : SubstI3.SubstUpdate subst (expr typ func) :=
  @FMapSubst3.SUBST.SubstUpdate_subst (expr typ func)
                                      (@mentionsU typ func)
                                      (@instantiate typ func).
Local Existing Instance SS.
Local Existing Instance SU.

Definition tyLProp := tyArr tyLocals tyHProp.

Definition fs : @SymEnv.functions typ _ :=
  SymEnv.from_list
    (@SymEnv.F typ _ (tyArr tyLProp (tyArr tyCmd (tyArr tyLProp tyProp)))
               (fun _ => triple) ::
     @SymEnv.F typ _ (tyArr tyCmd (tyArr tyCmd tyCmd))
               (fun _ => Seq) ::
     @SymEnv.F typ _ (tyArr tyVariable (tyArr tyExpr tyCmd))
               (fun _ => Assign) ::
     @SymEnv.F typ _ (tyArr tyVariable (tyArr tyExpr tyCmd))
               (fun _ => Read) ::
     @SymEnv.F typ _ (tyArr tyExpr (tyArr tyExpr tyCmd))
               (fun _ => Write) ::
     @SymEnv.F typ _ tyCmd
               (fun _ => Skip) ::
     @SymEnv.F typ _ (tyArr tyNat (tyArr tyNat tyHProp))
               (fun _ => PtsTo) ::
     nil).

Definition lops : logic_ops _ :=
  fun t =>
    match t
          return option (forall ts, ILogic.ILogicOps (TypesI.typD ts t))
    with
      | tyProp => Some _
      | tyHProp => Some _
      | tyArr tyLocals tyHProp => Some (fun _ => ILogicOps_lprop)
      | _ => None
    end.

Definition eops : embed_ops _ :=
  fun t u =>
    match t as t , u as u
          return option
                   (forall ts : list Type,
                      ILEmbed.EmbedOp (TypesI.typD ts t) (TypesI.typD ts u))
    with
      | tyProp , tyHProp =>
        Some (fun _ => EmbedOp_Prop_HProp)
      | tyHProp , tyArr tyLocals tyHProp =>
        Some (fun ts => EmbedOp_HProp_lprop)
      | tyProp , tyArr tyLocals tyHProp =>
        Some (fun _ => @ILInsts.EmbedILFunDropOp _ _ EmbedOp_Prop_HProp _)
      | _ , _ => None
    end.

Local Instance RSym_ilfunc : SymI.RSym (ilfunc typ) :=
  @ILogicFunc.RSym_ilfunc typ _ _ lops eops _ _.

Definition RS : SymI.RSym func :=
  SymSum.RSym_sum (SymSum.RSym_sum (SymEnv.RSym_func fs) _) _.
Local Existing Instance RS.

Let Expr_expr : ExprI.Expr _ (expr typ func) := Expr_expr _ _.
Local Existing Instance Expr_expr.

Definition fTriple : expr typ func := Inj (inl (inl 1%positive)).
Definition fSeq : expr typ func := Inj (inl (inl 2%positive)).
Definition fAssign : expr typ func := Inj (inl (inl 3%positive)).
Definition fRead : expr typ func := Inj (inl (inl 4%positive)).
Definition fWrite : expr typ func := Inj (inl (inl 5%positive)).
Definition fSkip : expr typ func := Inj (inl (inl 6%positive)).
Definition fPtsTo : expr typ func := Inj (inl (inl 7%positive)).

Definition fVar (v : var) : expr typ func := Inj (inl (inr (pVar v))).
Definition fConst (c : nat) : expr typ func := Inj (inl (inr (pNat c))).
Definition fAp (t u : typ) : expr typ func := Inj (inl (inr (pAp t u))).
Definition fPure (t : typ) : expr typ func := Inj (inl (inr (pPure t))).
Definition flocals_get : expr typ func := Inj (inl (inr pLocals_get)).
Definition flocals_upd : expr typ func := Inj (inl (inr pLocals_upd)).
Definition fupdate t : expr typ func := Inj (inl (inr (pUpdate t))).
Definition feval_iexpr : expr typ func := Inj (inl (inr pEval_expri)).
Definition fEq (t : typ) : expr typ func := Inj (inl (inr (pEq t))).
Definition fStar (t : typ) : expr typ func := Inj (inl (inr (pStar t))).
Definition fEmp (t : typ) : expr typ func := Inj (inl (inr (pEmp t))).

Definition mkTriple (P c Q : expr typ func) : expr typ func :=
  App (App (App fTriple P) c) Q.
Definition mkSeq (a b : expr typ func) : expr typ func :=
  App (App fSeq a) b.
Definition mkAssign (a b : expr typ func) : expr typ func :=
  App (App fAssign a) b.
Definition mkRead (a b : expr typ func) : expr typ func :=
  App (App fRead a) b.
Definition mkWrite (a b : expr typ func) : expr typ func :=
  App (App fWrite a) b.
Definition mkSkip : expr typ func := fSkip.

Definition lex (l t : typ) (e : expr typ func) : expr typ func :=
  App (Inj (inr (ilf_exists t l))) (Abs t e).

Definition lstar (l : typ) (e e' : expr typ func) : expr typ func :=
  App (App (fStar l)  e) e'.
Definition lemp (l : typ) : expr typ func := fEmp l.
Definition land (l : typ) (e e' : expr typ func) : expr typ func :=
  App (App (Inj (inr (ilf_and l))) e) e'.
Definition ltrue (l : typ) : expr typ func :=
  Inj (inr (ilf_true l)).
Definition lentails (l : typ) (e e' : expr typ func) : expr typ func :=
  App (App (Inj (inr (ilf_entails l))) e) e'.
Definition lor (l : typ) (e e' : expr typ func) : expr typ func :=
  App (App (Inj (inr (ilf_or l))) e) e'.
Definition lembed (t f : typ) (e : expr typ func) : expr typ func :=
  App (Inj (inr (ilf_embed f t))) e.
Definition lPtsTo (a b : expr typ func) : expr typ func :=
  App (App fPtsTo a) b.

Definition lap (t u : typ) (a b : expr typ func) : expr typ func :=
  App (App (fAp t u) a) b.
Definition lpure (t : typ) (a : expr typ func) : expr typ func :=
  App (fPure t) a.
Definition lupdate (t : typ) (a b : expr typ func) : expr typ func :=
  App (App (fupdate t) a) b.

(** Testing function **)
Definition test_lemma :=
  @lemmaD typ RType_typ (expr typ func) Expr_expr (expr typ func)
          (fun tus tvs e => exprD' nil tus tvs tyProp e)
          tyProp
          (fun x => x) nil nil.
