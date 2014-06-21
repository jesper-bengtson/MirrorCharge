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
Require Import MirrorCharge.Imp.Imp.
Require Import MirrorCharge.ILogicFunc.

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
| pEval_expri.

(** TODO: This also needs to include logic stuff! **)
Definition func := (SymEnv.func + imp_func + ilfunc typ)%type.

Definition typeof_sym_imp (f : imp_func) : option typ :=
  Some match f with
         | pVar _ => tyVariable
         | pNat _ => tyNat
         | pLocals_get => tyArr tyVariable (tyArr tyLocals tyNat)
         | pLocals_upd => tyArr tyVariable (tyArr tyNat (tyArr tyLocals tyLocals))
         | pEq t => tyArr t (tyArr t tyProp)
         | pEval_expri => tyArr tyExpr (tyArr tyLocals tyNat)
       end.

Definition imp_func_eq (a b : imp_func) : option bool :=
  match a , b with
    | pVar a , pVar b => Some (a ?[ eq ] b)
    | pNat a , pNat b => Some (a ?[ eq ] b)
    | pLocals_get , pLocals_get => Some true
    | pLocals_upd , pLocals_upd => Some true
    | pEq a , pEq b => Some (a ?[ eq ] b)
    | pEval_expri , pEval_expri => Some true
    | _ , _ => Some false
  end.

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
            end
; sym_eqb := imp_func_eq
}.

Section tactic.
  Let subst : Type :=
    FMapSubst3.SUBST.raw (expr typ func).
  Let SS : SubstI3.Subst subst (expr typ func) :=
    @FMapSubst3.SUBST.Subst_subst _.
  Let SU : SubstI3.SubstUpdate subst (expr typ func) :=
    @FMapSubst3.SUBST.SubstUpdate_subst (expr typ func)
                                        (@mentionsU typ func)
                                        (@instantiate typ func).
  Local Existing Instance SS.
  Local Existing Instance SU.

  Let tyLProp := tyArr tyLocals tyHProp.

  Let fs : @SymEnv.functions typ _ :=
    SymEnv.from_list
      (@SymEnv.F typ _ (tyArr tyLProp (tyArr tyCmd (tyArr tyLProp tyProp)))
                 (fun _ => triple) ::
       @SymEnv.F typ _ (tyArr tyCmd (tyArr tyCmd tyCmd))
                 (fun _ => Seq) ::
       @SymEnv.F typ _ (tyArr tyVariable (tyArr tyExpr tyCmd))
                 (fun _ => Assign) ::
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

  Definition eops : embed_ops _.
  red. refine
    (fun t u =>
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
      end).
  Defined.

  Local Instance RSym_ilfunc : SymI.RSym (ilfunc typ) :=
    @ILogicFunc.RSym_ilfunc typ _ _ lops eops _ _.

  Definition RS : SymI.RSym func :=
    SymSum.RSym_sum (SymSum.RSym_sum (SymEnv.RSym_func fs) _) _.
  Local Existing Instance RS.

  Definition fTriple : expr typ func := Inj (inl (inl 1%positive)).
  Definition fSeq : expr typ func := Inj (inl (inl 2%positive)).
  Definition fAssign : expr typ func := Inj (inl (inl 3%positive)).
  Definition fVar (v : var) : expr typ func := Inj (inl (inr (pVar v))).
  Definition fConst (c : nat) : expr typ func := Inj (inl (inr (pNat c))).
  Definition flocals_get : expr typ func := Inj (inl (inr pLocals_get)).
  Definition flocals_upd : expr typ func := Inj (inl (inr pLocals_upd)).
  Definition feval_iexpr : expr typ func := Inj (inl (inr pEval_expri)).
  Definition fEq (t : typ) : expr typ func := Inj (inl (inr (pEq t))).

  Definition mkTriple (P c Q : expr typ func) : expr typ func :=
    App (App (App fTriple P) c) Q.
  Definition mkSeq (a b : expr typ func) : expr typ func :=
    App (App fSeq a) b.
  Definition mkAssign (a b : expr typ func) : expr typ func :=
    App (App fAssign a) b.

  (** NOTE: Manual lemma reification for the time being **)
  Definition seq_lemma : lemma typ (expr typ func) (expr typ func) :=
  {| vars := tyLProp :: tyLProp :: tyLProp :: tyCmd :: tyCmd :: nil
   ; premises := mkTriple (Var 0) (Var 3) (Var 1) ::
                 mkTriple (Var 1) (Var 4) (Var 2) :: nil
   ; concl := mkTriple (Var 0) (mkSeq (Var 3) (Var 4)) (Var 2)
   |}.

  Definition seq_assoc_lemma : lemma typ (expr typ func) (expr typ func) :=
  {| vars := tyLProp :: tyLProp :: tyCmd :: tyCmd :: tyCmd :: nil
   ; premises :=
       mkTriple (Var 0) (mkSeq (Var 2) (mkSeq (Var 3) (Var 4))) (Var 1) :: nil
   ; concl :=
       mkTriple (Var 0) (mkSeq (mkSeq (Var 2) (Var 3)) (Var 4)) (Var 1)
   |}.

  Let eapply_other :=
    @eapply_other typ (expr typ func) subst tyProp vars_to_uvars
                  (fun tus tvs n e1 e2 t s =>
                     @exprUnify subst typ func _ _ RS SS SU 3 nil
                                tus tvs n s e1 e2 t)
                  (@instantiate typ func) SS SU.

  Definition seq_case : stac typ (expr typ func) subst :=
    FIRST (   eapply_other seq_assoc_lemma (@IDTAC _ _ _)
           :: eapply_other seq_lemma (@IDTAC _ _ _)
           :: nil).

  Definition lex (l t : typ) (e : expr typ func) : expr typ func :=
    App (Inj (inr (ilf_exists t l))) (Abs t e).

  Definition land (l : typ) (e e' : expr typ func) : expr typ func :=
    App (App (Inj (inr (ilf_and l))) e) e'.
  Definition lor (l : typ) (e e' : expr typ func) : expr typ func :=
    App (App (Inj (inr (ilf_or l))) e) e'.
  Definition lembed (t f : typ) (e : expr typ func) : expr typ func :=
    App (Inj (inr (ilf_embed f t))) e.

  (** Assignment **)
  Definition assign_lemma : lemma typ (expr typ func) (expr typ func) :=
  {| vars := tyLProp :: tyVariable :: tyExpr :: nil
   ; premises := nil
   ; concl :=
       mkTriple (Var 0)
                (mkAssign (Var 1) (Var 2))
                (Abs tyLocals
                     (lex tyHProp tyNat
                          (land tyHProp
                                (lembed tyHProp tyProp
                                        (App (App (fEq tyNat)
                                                  (App (App flocals_get (Var 3)) (Var 1)))
                                             (App (App feval_iexpr (Var 4)) (Var 1))))
                                (App (Var 2) (App (App (App flocals_upd (Var 3)) (Var 0)) (Var 1))))))
   |}.

  Let Expr_expr : ExprI.Expr _ (expr typ func) := Expr_expr _ _.
  Local Existing Instance Expr_expr.

  Definition test_lemma :=
    @lemmaD typ RType_typ (expr typ func) Expr_expr (expr typ func)
            (fun tus tvs e => exprD' nil tus tvs tyProp e)
            tyProp
            (fun x => x) nil nil.

(*
  Eval compute
    in test_lemma seq_lemma.
*)

  Definition assign_case : stac typ (expr typ func) subst :=
    FIRST (   eapply_other assign_lemma (@IDTAC _ _ _)
           :: nil).

  Definition all_cases : stac typ (expr typ func) subst :=
    REC 2 (fun rec =>
             let rec := rec in
             REPEAT 2
                    (FIRST (   eapply_other seq_assoc_lemma rec
                            :: eapply_other seq_lemma rec
                            :: eapply_other assign_lemma rec
                            :: nil)))
        (@FAIL _ _ _).

  Definition test :=
    let vars := tyLProp :: tyCmd :: tyCmd :: tyCmd :: tyLProp :: nil in
    let goal :=
        mkTriple (Var 0)
                 (mkSeq (mkSeq (Var 1) (Var 2)) (Var 3))
                 (Var 4)
    in
    @seq_case goal (SubstI3.empty (expr :=expr typ func))
              nil vars.

  Definition XXX := eapply_other.

  Definition test' :=
    let uvars := tyLProp :: nil in
    let vars := tyLProp :: tyVariable :: tyCmd :: tyCmd :: tyLProp :: tyExpr :: nil in
    let goal :=
        mkTriple (Var 0)
                 (mkSeq (mkAssign (Var 1) (Var 5)) (Var 2))
                 (UVar 0)
    in
    @all_cases goal (SubstI3.empty (expr :=expr typ func))
               uvars vars.

  Time Eval vm_compute in test'.

End tactic.
