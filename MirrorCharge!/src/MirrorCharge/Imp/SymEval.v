Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Nat.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.provers.DefaultProver.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
(*
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCharge.ILogicFunc.
Require Import MirrorCharge.OrderedCanceller.
Require Import MirrorCharge.BILNormalize.
*)
Require Import MirrorCharge.SynSepLog.
Require Import MirrorCharge.SepLogFold.
Require Import MirrorCharge.Imp.Reify.
Require Import MirrorCharge.Imp.Imp.
Require Import MirrorCharge.Imp.Syntax.
Require Import MirrorCharge.Imp.ImpTac.
Require Import MirrorCharge.Imp.STacCancel.

Set Implicit Arguments.
Set Strict Implicit.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance Expr_expr.

Fixpoint get_alls (e : expr typ func) : list typ * expr typ func :=
  match e with
    | ExprCore.App (@ExprCore.Inj (inr (ILogicFunc.ilf_forall t tyProp)))
                   (ExprCore.Abs _ e) =>
      let (alls,e) := get_alls e in
      (t :: alls, e)
    | _ => (nil, e)
  end.

Fixpoint get_impls (e : expr typ func) : list (expr typ func) * expr typ func :=
  match e with
    | ExprCore.App (ExprCore.App (Inj (inr (ILogicFunc.ilf_impl tyProp))) P) Q =>
      let (impls,e) := get_impls Q in
      (P :: impls,e)
    | _ => (nil, e)
  end.

Definition convert_to_lemma (e : expr typ func)
: lemma typ (expr typ func) (expr typ func) :=
  let (alls, e) := get_alls e in
  let (impls, e) := get_impls e in
  {| vars := rev alls
   ; premises := impls
   ; concl := e |}.

Ltac reify_lemma e :=
  match type of e with
    | ?T =>
      (let k e :=
           let e := constr:(convert_to_lemma e) in
           let e := eval unfold convert_to_lemma in e in
           let e := eval simpl in e in
           refine e
       in
       reify_expr Reify.reify_imp k [ True ] [ T ])
  end.

(*
Definition to_skip : lemma typ (expr typ func) (expr typ func) :=
{| vars     := tyLProp :: tyCmd :: tyLProp :: tyLProp :: tySProp :: nil
 ; premises := (Var 4 |- {{ Var 0 }} (Var 1) {{ Var 3 }}) ::
               (Var 4 |- embed ((Var 2 : texp tyLProp) |- (Var 3))) :: nil
 ; concl    := (Var 4 |- {{ Var 0 }} (Var 1) {{ Var 2 }}) : expr _ _
 |}.

Eval hnf in test_lemma to_skip.
*)

(** Skip **)
Definition Skip_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Skip_rule.
Defined.
Print Skip_lemma.

Theorem Skip_rule2
: forall (G : SProp) P,
    ILogic.lentails G (triple P Skip P).
Proof.
  intros. eapply Skip_rule.
  Local Existing Instance Embed_Prop_SProp.
  Local Existing Instance Embed_Prop_HProp.
  apply ILEmbed.embedPropR.

Admitted.

Definition Skip_lemma2 : lemma typ (expr typ func) (expr typ func).
reify_lemma Skip_rule2.
Defined.
Print Skip_lemma2.

(** Sequence **)
Definition Seq_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Seq_rule.
Defined.
Print Seq_lemma.

Definition SeqA_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma SeqA_rule.
Defined.

(** Pull Existential **)
Definition triple_exL_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma triple_exL.
Defined.
Print triple_exL_lemma.

Definition triple_pureL_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma triple_pureL.
Defined.
Print triple_pureL_lemma.

(** Assignment **)
Definition Assign_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Assign_rule.
Defined.
Print Assign_lemma.
(*
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
*)

(** Read **)
Definition Read_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Read_rule.
Defined.
Print Read_lemma.
(*
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
*)

(** Write **)
Definition Write_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Write_rule.
Defined.
Print Write_lemma.
(*
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
*)

(** Call **)
Definition Call_lemma : lemma typ (expr typ func) (expr typ func).
Abort.

Definition solve_find_spec : rtac typ (expr typ func) := FAIL.

Definition solve_entailment :=
  THEN SIMPLIFY (runOnGoals stac_cancel).

Definition all_cases : rtac typ (expr typ func) :=
  REC 2 (fun rec =>
            let rec := rec in
            REPEAT 5
                   (FIRST (   EAPPLY SeqA_lemma
                           :: EAPPLY Seq_lemma
                           :: EAPPLY Assign_lemma
                           :: EAPPLY Read_lemma
                           :: EAPPLY Write_lemma
                           :: EAPPLY Skip_lemma
(*                           :: EAPPLY to_skip rec *)
                           :: nil)))
      (FAIL).

Definition runRtac (tus tvs : tenv typ) (goal : expr typ func) (tac : rtac typ (expr typ func)) :=
  tac tus tvs (length tus) (length tvs) _ (TopSubst _ tus tvs) goal.

Definition test :=
  let vars := tyLProp :: tyCmd :: tyCmd :: tyCmd :: tyLProp :: tySProp :: nil in
  let goal :=
      Syntax.lentails tySProp
                      (Var 5) (mkTriple (Var 0)
                                        (mkSeq (mkSeq (Var 1) (Var 2)) (Var 3))
                                        (Var 4))
  in
  runRtac nil vars goal all_cases.

Time Eval vm_compute in test.

Definition test' :=
  let uvars := tyLProp :: nil in
  let vars := tyLProp :: tyVariable :: tyCmd :: tyCmd :: tyLProp :: tyExpr :: nil in
  let goal :=
      mkTriple (Var 0)
               (mkSeq (mkAssign (Var 1) (Var 5)) (Var 2))
               (UVar 0)
  in
  runRtac uvars vars goal all_cases.

Time Eval vm_compute in test'.

(*
Definition test_read_goal : expr typ func.
  Print Ltac reify_imp.
  reify_imp (True).
*)


Local Notation "a @ b" := (@App typ _ a b) (at level 30).
Local Notation "'Ap' '[' x , y ']'" := (Inj (inl (inr (pAp x y)))) (at level 0).
Local Notation "'Pure' '[' x ']'" := (Inj (inl (inr (pPure x)))) (at level 0).

Definition test_read :=
  let uvars := tyLProp :: nil in
  let vars := tySProp :: nil in
  let goal :=
      (Inj (inr (ILogicFunc.ilf_entails tySProp)))
      @ Var 0
      @ mkTriple (lap tyNat tyHProp (lap tyNat (tyArr tyNat tyHProp) (lpure (tyArr tyNat (tyArr tyNat tyHProp)) fPtsTo)
                                       (flocals_get @ fVar "p"))%string
                    (lpure tyNat (fConst 1)))
               (mkRead (fVar "x") (Inj (inl (inr eVar)) @ (fVar "p")))%string
               (UVar 0)
  in
  let tac := all_cases in
  runRtac uvars vars goal tac.

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
  runRtac uvars vars goal tac.

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
  runRtac uvars vars goal tac.

Eval vm_compute in test_swap.
(** This is not the strongest post condition because we forgot the pure facts.
 ** This is likely a problem with the cancellation algorithm.
 **)
