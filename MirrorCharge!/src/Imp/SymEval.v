Require Import MirrorCore.Lemma.
Require Import MirrorCore.Lambda.TypesI2.
Require Import MirrorCore.Lambda.Expr.
Require Import McExamples.STac.STac.
Require Import MirrorCharge.ILogicFunc.
Require Import MirrorCharge.Imp.Imp.

Set Implicit Arguments.
Set Strict Implicit.

Section tactic.
  Variable RType_typ : TypesI2.RType.
  Variable Typ2_arr : Typ2 _ Fun.
  Variable subst : Type.
  
  Let tyArr : typ -> typ -> typ := @typ2 _ _ _.

  Axiom tyLocals : typ.
  Axiom tyCmd : typ.
  Axiom tyHProp : typ.
  Axiom tyProp : typ.

  Axiom fTriple : expr typ ilfunc.
  Axiom fSeq : expr typ ilfunc.

  Definition mkTriple (P c Q : expr typ ilfunc) : expr typ ilfunc :=
    App (App (App fTriple P) c) Q.
  Definition mkSeq (a b : expr typ ilfunc) : expr typ ilfunc :=
    App (App fSeq a) b.

  Definition seq_lemma : lemma typ (expr typ ilfunc) (expr typ ilfunc) :=
  {| vars := tyArr tyLocals tyHProp :: tyArr tyLocals tyHProp ::
             tyArr tyLocals tyHProp :: tyCmd :: tyCmd :: nil
   ; premises := mkTriple (Var 4) (Var 1) (Var 3) ::
                mkTriple (Var 3) (Var 0) (Var 2) :: nil
   ; concl := mkTriple (Var 4) (mkSeq (Var 1) (Var 0)) (Var 2)
   |}.

  Definition seq_assoc_lemma : lemma typ (expr typ ilfunc) (expr typ ilfunc) :=
  {| vars := tyArr tyLocals tyHProp :: tyArr tyLocals tyHProp ::
             tyCmd :: tyCmd :: tyCmd :: nil
   ; premises := mkTriple (Var 4) (mkSeq (Var 2) (mkSeq (Var 1) (Var 0))) (Var 3) :: nil
   ; concl := mkTriple (Var 4) (mkSeq (mkSeq (Var 2) (Var 1)) (Var 0)) (Var 3)
   |}.

  Require Import MirrorCore.Lambda.ExprLift.
  Require Import MirrorCore.Lambda.ExprUnify_simul.

  Let eapply_other :=
    @eapply_other typ (expr typ ilfunc) subst tyProp vars_to_uvars.
  Check eapply_other.
  Check exprUnify.
  Check (@exprUnify subst ilfunc _ _).


  Definition seq_case : branch typ (expr typ ilfunc) subst :=
    FIRST (   eapply_other seq_assoc_lemma _
           :: eapply_other seq_lemma _
           :: nil).