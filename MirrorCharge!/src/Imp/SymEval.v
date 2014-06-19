Require Import BinPos.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.STac.STac.
Require Import MirrorCore.provers.DefaultProver.
Require MirrorCore.syms.SymEnv.
Require Import MirrorCore.Subst.FMapSubst3.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCharge.Imp.Imp.

Set Implicit Arguments.
Set Strict Implicit.

Definition func := SymEnv.func.

Inductive typ :=
| tyArr : typ -> typ -> typ
| tyLocals : typ
| tyCmd : typ
| tyHProp : typ
| tyProp : typ.

Fixpoint typD (ls : list Type) (t : typ) : Type :=
  match t with
    | tyArr a b => typD ls a -> typD ls b
    | tyLocals => locals
    | tyCmd => icmd
    | tyHProp => HProp
    | tyProp => Prop
  end.

Inductive tyAcc_typ : typ -> typ -> Prop :=
| tyAcc_tyArrL : forall a b, tyAcc_typ a (tyArr a b)
| tyAcc_tyArrR : forall a b, tyAcc_typ a (tyArr b a).

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
    | _ , _ => None
  end.

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


Section tactic.
  Let subst : Type :=
    @FMapSubst3.SUBST.raw (expr typ func).
  Instance SS : SubstI3.Subst subst (expr typ func) :=
    FMapSubst3.SUBST.Subst_subst _.
  Instance SU : SubstI3.SubstUpdate subst (expr typ func) :=
    FMapSubst3.SUBST.SubstUpdate_subst (@mentionsU typ func)
                                       (@instantiate typ func).

  Let tyLProp := tyArr tyLocals tyHProp.

  Let fs : @SymEnv.functions typ _ :=
    SymEnv.from_list
      (@SymEnv.F typ _ (tyArr tyLProp (tyArr tyCmd (tyArr tyLProp tyProp)))
                 (fun _ => triple) ::
       @SymEnv.F typ _ (tyArr tyCmd (tyArr tyCmd tyCmd))
                 (fun _ => Seq) ::
       nil).

  Definition RS : SymI.RSym func := SymEnv.RSym_func fs.
  Definition EP : EProver2.EProver (typ := typ) (expr typ func) :=
    EProver2.from_Prover (DefaultProver (expr typ func)).

  Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.

  Definition fTriple : expr typ func := Inj 1%positive.
  Definition fSeq : expr typ func := Inj 2%positive.

  Definition mkTriple (P c Q : expr typ func) : expr typ func :=
    App (App (App fTriple P) c) Q.
  Definition mkSeq (a b : expr typ func) : expr typ func :=
    App (App fSeq a) b.

  (** NOTE: Manual lemma reification for the time being **)
  Definition seq_lemma : lemma typ (expr typ func) (expr typ func) :=
  {| vars := tyArr tyLocals tyHProp :: tyArr tyLocals tyHProp ::
             tyArr tyLocals tyHProp :: tyCmd :: tyCmd :: nil
   ; premises := mkTriple (Var 4) (Var 1) (Var 3) ::
                 mkTriple (Var 3) (Var 0) (Var 2) :: nil
   ; concl := mkTriple (Var 4) (mkSeq (Var 1) (Var 0)) (Var 2)
   |}.

  Definition seq_assoc_lemma : lemma typ (expr typ func) (expr typ func) :=
  {| vars := tyArr tyLocals tyHProp :: tyArr tyLocals tyHProp ::
             tyCmd :: tyCmd :: tyCmd :: nil
   ; premises :=
       mkTriple (Var 0) (mkSeq (Var 2) (mkSeq (Var 3) (Var 4))) (Var 1) :: nil
   ; concl :=
       mkTriple (Var 0) (mkSeq (mkSeq (Var 2) (Var 3)) (Var 4)) (Var 1)
   |}.

  Let eapply_other :=
    @eapply_other typ (expr typ func) subst tyProp vars_to_uvars
                  (fun tus tvs n e1 e2 t s =>
                     @exprUnify subst typ func _ _ RS SS SU 1 nil
                                tus tvs n s e1 e2 t) SS SU.

  Definition seq_case : branch typ (expr typ func) subst :=
    FIRST (   eapply_other seq_assoc_lemma EP
           :: eapply_other seq_lemma EP
           :: nil).

  Let goal : expr typ func :=
    mkTriple (Var 0)
             (mkSeq (mkSeq (Var 1) (Var 2)) (Var 3))
             (Var 4).

  Definition test :=
    @seq_case goal (SubstI3.empty (expr :=expr typ func))
              nil (tyLProp :: tyCmd :: tyCmd :: tyCmd :: tyLProp :: nil).

  Time Eval vm_compute in test.

End tactic.