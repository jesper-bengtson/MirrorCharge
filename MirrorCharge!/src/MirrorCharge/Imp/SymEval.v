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
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCharge.Imp.Imp.
Require Import MirrorCharge.ILogicFunc.

Set Implicit Arguments.
Set Strict Implicit.

Section tactic.

  Let subst : Type :=
    FMapSubst.SUBST.raw (expr typ func).
  Let SS : SubstI.Subst subst (expr typ func) :=
    @FMapSubst.SUBST.Subst_subst _.
  Let SU : SubstI.SubstUpdate subst (expr typ func) :=
    FMapSubst.SUBST.SubstUpdate_subst (@instantiate typ func).

  Local Existing Instance SS.
  Local Existing Instance SU.

  Definition test_lemma :=
    @lemmaD typ RType_typ (expr typ func) Expr_expr (expr typ func)
            (fun tus tvs e => exprD' tus tvs e tyProp)
            tyProp
            (fun x => x) nil nil.


  Definition fTriple : expr typ func := Inj (inl (inl 1%positive)).
  Definition fSeq : expr typ func := Inj (inl (inl 2%positive)).
  Definition fAssign : expr typ func := Inj (inl (inl 3%positive)).
  Definition fRead : expr typ func := Inj (inl (inl 4%positive)).
  Definition fVar (v : var) : expr typ func := Inj (inl (inr (pVar v))).
  Definition fConst (c : nat) : expr typ func := Inj (inl (inr (pNat c))).
  Definition fStar : expr typ func := Inj (inl (inl 5%positive)).
  Definition fPtsTo : expr typ func := Inj (inl (inl 6%positive)).
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
  Definition mkRead (a b : expr typ func) : expr typ func :=
    App (App fRead a) b.

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

  Let APPLY :=
    @APPLY typ (expr typ func) subst _ Typ0_Prop
           vars_to_uvars
           (fun tus tvs n e1 e2 t s =>
              @exprUnify subst typ func _ _ RS SS SU 3 nil
                         tus tvs n s e1 e2 t)
           (@instantiate typ func) SS SU.

  Definition lex (l t : typ) (e : expr typ func) : expr typ func :=
    App (Inj (inr (ilf_exists t l))) (Abs t e).

  Definition lstar (l : typ) (e e' : expr typ func) : expr typ func :=
    App (App fStar e) e'.
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

  Definition read_lemma : lemma typ (expr typ func) (expr typ func) :=
  {| vars := tyLProp :: tyVariable :: tyExpr ::
             tyArr tyLocals tyNat :: nil
   ; premises :=
       lentails tyLProp
                (Var 0)
                (Abs tyLocals
                     (lstar tyHProp
                            (App (App fPtsTo (App (App feval_iexpr (Var 3)) (Var 0))) (App (Var 4) (Var 0)))
                            (ltrue tyHProp)))
        :: nil
   ; concl :=
       mkTriple (Var 0)
                (mkRead (Var 1) (Var 2))
                (Abs tyLocals
                     (lex tyHProp tyNat
                          (land tyHProp
                                (lembed tyHProp tyProp
                                        (App (App (fEq tyNat)
                                                  (App (App flocals_get (Var 3)) (Var 1)))
                                             (App (Var 5) (App (App (App flocals_upd (Var 3)) (Var 0)) (Var 1)))))
                                (App (Var 2) (App (App (App flocals_upd (Var 3)) (Var 0)) (Var 1))))))
   |}.

  Definition all_cases : stac typ (expr typ func) subst :=
    REC 3 (fun rec =>
             let rec := rec in
             REPEAT 5
                    (FIRST (   APPLY seq_assoc_lemma (apply_to_all rec)
                            :: APPLY seq_lemma (apply_to_all rec)
                            :: APPLY assign_lemma (apply_to_all rec)
                            :: APPLY read_lemma (apply_to_all rec)
                            :: nil)))
        (@FAIL _ _ _).

  Definition test :=
    let vars := tyLProp :: tyCmd :: tyCmd :: tyCmd :: tyLProp :: nil in
    let goal :=
        mkTriple (Var 0)
                 (mkSeq (mkSeq (Var 1) (Var 2)) (Var 3))
                 (Var 4)
    in
    @all_cases nil vars (SubstI.empty (expr :=expr typ func)) nil goal.

  Time Eval vm_compute in test.

  Definition test' :=
    let uvars := tyLProp :: nil in
    let vars := tyLProp :: tyVariable :: tyCmd :: tyCmd :: tyLProp :: tyExpr :: nil in
    let goal :=
        mkTriple (Var 0)
                 (mkSeq (mkAssign (Var 1) (Var 5)) (Var 2))
                 (UVar 0)
    in
    @all_cases uvars vars (SubstI.empty (expr :=expr typ func)) nil goal.

  Time Eval vm_compute in test'.

  Local Notation "a @ b" := (@App typ _ a b) (at level 30).
  Local Notation "\ t -> e" := (@Abs typ _ t e) (at level 40).

  Definition test_read :=
    let uvars := tyLProp :: nil in
    let vars := tyVariable :: tyExpr :: nil in
    let goal :=
        mkTriple (Abs tyLocals (lPtsTo (App (App flocals_get (Var 1)) (Var 0)) (fConst 1)))
                 (mkRead (Var 0) (Var 1))
                 (UVar 0)
    in
    let tac :=
        APPLY read_lemma (apply_to_all (@IDTAC _ _ _))
    in
    @tac uvars vars (SubstI.empty (expr :=expr typ func)) nil goal.
(*
  Time Eval cbv beta iota zeta delta - [ IDTAC ] in test_read.
*)

  (** The next task is to automate the entailment
   ** I'm going to have a goal that looks like this:
   **   P |- Q
   ** There are two approaches:
   ** 1) Expose lambdas and go under the state.
   **    This has the benefit that [star] looks like [star], there isn't
   **    a bunch of lifting going on.
   ** 2) Reason about the lifted logics explicitly.
   **    This has the drawback that everything is lifted, so, e.g. instead
   **    of seeing
   **        (star P Q)
   **    you will see
   **        (ap (ap (pure star) P) Q)
   ** If we do the former, then we need a way to put things back into a good
   ** representation.
   ** More of a problem is the fact that our unification variables will
   ** need to mention the heap explicitly, i.e. we'll be working in two
   ** unification contexts which substitutions can not handle at the moment.
   ** ^--- This suggests that I *must* do the later.
   **)

End tactic.
