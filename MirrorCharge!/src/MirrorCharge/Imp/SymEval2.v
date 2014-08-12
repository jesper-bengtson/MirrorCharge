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
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCharge.ILogicFunc.
Require Import MirrorCharge.OrderedCanceller.
Require Import MirrorCharge.BILNormalize.
Require Import MirrorCharge.SynSepLog.
Require Import MirrorCharge.SepLogFold.
Require Import MirrorCharge.Imp.Imp.
Require Import MirrorCharge.Imp.Syntax.
Require Import MirrorCharge.Imp.STacSimplify.
(*Require Import MirrorCharge.Imp.STacCancel. *)
Require Import MirrorCharge.Imp.STacCancelEx.

Set Implicit Arguments.
Set Strict Implicit.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance Expr_expr.

Local Notation "a @ b" := (@App typ _ a b) (at level 30).
Local Notation "'Ap' '[' x , y ']'" := (Inj (inl (inr (pAp x y)))) (at level 0).
Local Notation "'Pure' '[' x ']'" := (Inj (inl (inr (pPure x)))) (at level 0).
Local Notation "x '|-' y" :=
  (App (App (Inj (inr (ilf_entails (tyArr tyLocals tyHProp)))) x) y) (at level 10).
Local Notation "'{{'  P  '}}'  c  '{{'  Q  '}}'" :=
  (Inj (inl (inl 1%positive)) @ P @ c @ Q) (at level 20).
Local Notation "c1 ;; c2" := (Inj (inl (inl 2%positive)) @ c1 @ c2) (at level 30).

Let EAPPLY lem tac :=
  @EAPPLY typ (expr typ func) subst _ _ ExprLift.vars_to_uvars
                (fun tus tvs n e1 e2 t s =>
                   @exprUnify subst typ func _ _ RS SS SU 3 nil
                              tus tvs n s e1 e2 t)
                (@ExprSubst.instantiate typ func) SS SU
                lem (apply_to_all tac).

(** NOTE: Manual lemma reification for the time being **)
(** Pull Ex **)
Definition pull_nat_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyArr tyNat tyLProp :: tyLProp :: tyCmd :: nil
 ; premises := App (Inj (inr (ilf_forall tyNat tyProp))) (Abs tyNat (mkTriple (App (Var 1) (Var 0)) (Var 3) (Var 2))) :: nil
 ; concl := mkTriple (App (Inj (inr (ilf_exists tyNat tyLProp))) (Var 0)) (Var 2) (Var 1)
 |}.

Definition to_skip : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyLProp :: tyCmd :: tyLProp :: tyLProp :: nil
 ; premises := mkTriple (Var 0) (Var 1) (Var 3) ::
               lentails tyLProp (Var 2) (Var 3) :: nil
 ; concl := mkTriple (Var 0) (Var 1) (Var 2)
 |}.

(** Skip **)
Definition skip_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyLProp :: tyLProp :: nil
 ; premises := lentails tyLProp (Var 0) (Var 1) :: nil
 ; concl := mkTriple (Var 0) mkSkip (Var 1)
 |}.

Definition skip_lemma2 : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyLProp :: nil
 ; premises := nil
 ; concl := mkTriple (Var 0) mkSkip (Var 0)
 |}.

(** Sequence **)
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

(** Assignment **)
Definition assign_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyLProp :: tyVariable :: tyExpr :: nil
 ; premises := nil
 ; concl :=
     mkTriple (Var 0)
              (mkAssign (Var 1) (Var 2))
              (lex tyLProp tyNat
                   (land tyLProp
                         (lap tyProp tyHProp
                              (lpure (tyArr tyProp tyHProp) ((Inj (inr (ilf_embed tyProp tyHProp)))))
                              (lap tyNat tyProp (lap tyNat (tyArr tyNat tyProp) (lpure (tyArr tyNat (tyArr tyNat tyProp))
                                                                                       (fEq tyNat))
                                                     (App flocals_get (Var 2)))
                                   (lupdate tyNat (App (App flocals_upd (Var 2)) (Var 0)) (App feval_iexpr (Var 3)))))
                         (lupdate tyHProp (App (App flocals_upd (Var 2)) (Var 0)) (Var 1))))
 |}.

(** Read **)
Definition read_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyLProp :: tyVariable :: tyExpr ::
                   tyArr tyLocals tyNat :: nil
 ; premises :=
     lentails tyLProp
              (Var 0)
              (lstar tyLProp
                     (lap tyNat tyHProp (lap tyNat (tyArr tyNat tyHProp) (lpure (tyArr tyNat (tyArr tyNat tyHProp)) fPtsTo) (feval_iexpr @ Var 2)) (Var 3))
                     (ltrue tyLProp))
              :: nil
 ; concl :=
     mkTriple (Var 0)
              (mkRead (Var 1) (Var 2))
              (lex tyLProp tyNat
                   (land tyLProp
                         (lap tyProp tyHProp
                              (lpure (tyArr tyProp tyHProp) ((Inj (inr (ilf_embed tyProp tyHProp)))))
                              (lap tyNat tyProp (lap tyNat (tyArr tyNat tyProp) (lpure (tyArr tyNat (tyArr tyNat tyProp))
                                                                                       (fEq tyNat))
                                                     (App flocals_get (Var 2)))
                                   (lupdate tyNat (App (App flocals_upd (Var 2)) (Var 0)) (Var 4))))
                         (lupdate tyHProp (App (App flocals_upd (Var 2)) (Var 0)) (Var 1))))
 |}.

(** Write **)
Definition write_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyLProp :: tyLProp :: tyExpr :: tyExpr :: nil
 ; premises :=
     lentails tyLProp
              (Var 0)
              (lex tyLProp tyNat
                   (lstar tyLProp
                          (lap tyNat tyHProp (lap tyNat (tyArr tyNat tyHProp)
                                                  (lpure (tyArr tyNat (tyArr tyNat tyHProp)) fPtsTo)
                                                  (feval_iexpr @ Var 3))
                               (lpure tyNat (Var 0)))
                          (Var 2)))
     :: nil
 ; concl :=
     mkTriple (Var 0)
              (mkWrite (Var 2) (Var 3))
              (lstar tyLProp
                     (lap tyNat tyHProp (lap tyNat (tyArr tyNat tyHProp) (lpure (tyArr tyNat (tyArr tyNat tyHProp)) fPtsTo) (feval_iexpr @ Var 2)) (feval_iexpr @ Var 3))
                     (Var 1))
 |}.

Definition solve_entailment :=
  THEN (SIMPLIFY (fun _ _ _ => beta_all simplify nil nil))
       stac_cancel.

Definition all_cases : stac typ (expr typ func) subst :=
  REC 2 (fun rec =>
            let rec := rec in
            REPEAT 5
                   (FIRST (   EAPPLY seq_assoc_lemma rec
                           :: EAPPLY seq_lemma rec
                           :: EAPPLY assign_lemma rec
                           :: EAPPLY read_lemma solve_entailment
                           :: EAPPLY write_lemma solve_entailment
                           :: EAPPLY skip_lemma solve_entailment
                           :: EAPPLY to_skip rec
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

Definition test_read :=
  let uvars := tyLProp :: nil in
  let vars := nil in
  let goal :=
      mkTriple (lap tyNat tyHProp (lap tyNat (tyArr tyNat tyHProp) (lpure (tyArr tyNat (tyArr tyNat tyHProp)) fPtsTo)
                                       (flocals_get @ fVar "p"))%string
                    (lpure tyNat (fConst 1)))
               (mkRead (fVar "x") (Inj (inl (inr eVar)) @ (fVar "p")))%string
               (UVar 0)
  in
  let tac := all_cases in
  @tac uvars vars (SubstI.empty (expr :=expr typ func)) nil goal.

Time Eval vm_compute  in test_read.

Definition lifted_ptsto (a b : expr typ func) : expr typ func :=
  lap tyNat tyHProp (lap tyNat (tyArr tyNat tyHProp)
                         (lpure (tyArr tyNat (tyArr tyNat tyHProp)) fPtsTo)
                         a) b.

Definition test_read2 :=
  let uvars := tyLProp :: nil in
  let vars := tyNat :: tyNat :: nil in
  let goal :=
      (mkTriple
         (lstar tyLProp
                (lifted_ptsto (flocals_get @ fVar "p1") (lpure tyNat (Var 0)))
                (lifted_ptsto (flocals_get @ fVar "p2") (lpure tyNat (Var 1))))
         (mkSeq (mkRead (fVar "t1") (Inj (inl (inr eVar)) @ (fVar "p1")))
                (mkRead (fVar "t2") (Inj (inl (inr eVar)) @ (fVar "p2"))))
         (UVar 0))%string
  in
  let tac := all_cases in
  @tac uvars vars (SubstI.empty (expr :=expr typ func)) nil goal.

Eval cbv beta iota zeta delta in test_read2.

Definition test_swap :=
  let uvars := nil in
  let vars := tyNat :: tyNat :: nil in
  let goal :=
      (mkTriple
         (lstar tyLProp
                (lifted_ptsto (flocals_get @ fVar "p1") (lpure tyNat (Var 0)))
                (lifted_ptsto (flocals_get @ fVar "p2") (lpure tyNat (Var 1))))
         (mkSeq (mkRead (fVar "t1") (Inj (inl (inr eVar)) @ (fVar "p1")))
         (mkSeq (mkRead (fVar "t2") (Inj (inl (inr eVar)) @ (fVar "p2")))
         (mkSeq (mkWrite (Inj (inl (inr eVar)) @ fVar "p2") (Inj (inl (inr eVar)) @ (fVar "t1")))
                (mkWrite (Inj (inl (inr eVar)) @ fVar "p1") (Inj (inl (inr eVar)) @ (fVar "t2"))))))
         (lstar tyLProp
                (lifted_ptsto (flocals_get @ fVar "p1") (lpure tyNat (Var 1)))
                (lifted_ptsto (flocals_get @ fVar "p2") (lpure tyNat (Var 0)))))%string
  in
  let tac := all_cases in
  @tac uvars vars (SubstI.empty (expr :=expr typ func)) nil goal.

Eval vm_compute in test_swap.
(** This is not the strongest post condition because we forgot the pure facts.
 ** This is likely a problem with the cancellation algorithm.
 **)
