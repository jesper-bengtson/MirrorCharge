Require Import MirrorCore.RTac.RTac.
Require Import MirrorCharge.Imp.Goal.
Require Import MirrorCharge.Imp.ImpTac.
Require Import MirrorCharge.Imp.SymEvalLemmas.
Require MirrorCharge.Imp.STacCancel.
Require Import MirrorCharge.Imp.Syntax.

Definition entailment_tac : imp_tac := THEN SIMPLIFY (runOnGoals STacCancel.stac_cancel).
Definition simplify_tac : imp_tac := SIMPLIFY.

Definition entailment_tac_solve : imp_tac := SOLVE entailment_tac.

Definition runTacK (tac : imp_tacK) : imp_tac :=
  fun a b c d e f g => tac a b c d e f (GGoal g).

Definition EAPPLY_THEN a (b : imp_tac) : imp_tac :=
  runTacK (THENK (EAPPLY a : imp_tacK) (runOnGoals b)).


Definition EAPPLY_THEN_1 a (side : imp_tac) (b : imp_tacK) : imp_tac :=
  runTacK (THENK (THENK (EAPPLY a : imp_tacK) (runOnGoals (TRY (SOLVE side))))
                 (THENK (@MINIFY _ _ _)
                        (runOnGoals (AT_GOAL (fun _ _ goal =>
                                                match goal with
                                                  | App (App entails _) (App (App (App triple _) _) _) =>
                                                    runTacK b
                                                  | _ => FAIL
                                                end))))).

Definition sym_eval_mem (n : nat) : imp_tac :=
  REC_N n (fun rec : imp_tac =>
           let rec := THEN simplify_tac (runOnGoals rec) in
           FIRST (   EAPPLY_THEN SeqA_lemma rec
                  :: EAPPLY_THEN Assign_seq_lemma rec
                  :: EAPPLY_THEN_1 Read_seq_lemma entailment_tac (runOnGoals rec)
                  :: EAPPLY_THEN_1 Write_seq_lemma entailment_tac (runOnGoals rec)
                  :: EAPPLY_THEN Skip_seq_lemma rec
                  :: EAPPLY_THEN_1 Assert_seq_lemma entailment_tac (runOnGoals rec)
                  :: EAPPLY_THEN Assign_tail_lemma (TRY entailment_tac_solve)
                  :: EAPPLY_THEN Read_tail_lemma (TRY entailment_tac_solve)
                  :: EAPPLY_THEN Write_tail_lemma (TRY entailment_tac_solve)
                  :: EAPPLY_THEN Skip_tail_lemma (TRY entailment_tac_solve)
                  :: EAPPLY_THEN Assert_tail_lemma (TRY entailment_tac_solve)
                  :: nil))
      IDTAC.



Definition Prove P c Q :=
  App
    (App
       (Reify._Inj (inr (ILogicFunc.ilf_entails Syntax.tySProp)))
       (Reify._Inj (inr (ILogicFunc.ilf_true Syntax.tySProp))))
    (App (App (App Syntax.fTriple P) c) Q).

Fixpoint skips (n : nat) :=
  match n with
    | 0 => Syntax.fSkip
    | S n => App (App Syntax.fSeq Syntax.fSkip) (skips n)
  end.

Require Import Coq.Strings.String.

Fixpoint adds_syn (n : nat) :=
  match n with
    | 0 => Syntax.fSkip
    | S n => Syntax.mkSeq (Syntax.mkAssign (Syntax.fVar "x") (Syntax.fVar "x")) (adds_syn n)
  end%string.

Time Eval vm_compute in
    let tus := nil in
    let tvs := nil in
    let goal := Prove (Syntax.ltrue Syntax.tyLProp) Syntax.fSkip (Syntax.ltrue Syntax.tyLProp) in
    runImpTac tus tvs goal (sym_eval_mem 5).

Time Eval vm_compute in
    let tus := nil in
    let tvs := nil in
    let goal := Prove (Syntax.ltrue Syntax.tyLProp) (skips 800) (Syntax.ltrue Syntax.tyLProp) in
    runImpTac tus tvs goal (sym_eval_mem 810).

Time Eval vm_compute in
    let n := 100 in
    let tus := nil in
    let tvs := nil in
    let goal := Prove (Syntax.ltrue Syntax.tyLProp) (adds_syn n) (Syntax.ltrue Syntax.tyLProp) in
    runImpTac tus tvs goal (sym_eval_mem n).

Fixpoint adds (n : nat) :=
  match n with
    | 0 => Imp.Skip
    | S n => Imp.Seq (Imp.Assign "x" (Imp.iVar "x")) (adds n)
  end%string.

Goal @ILogic.lentails Imp.SProp Imp.ILogicOps_SProp (@ILogic.ltrue Imp.SProp Imp.ILogicOps_SProp)
     (Imp.triple (@ILogic.ltrue Imp.lprop Imp.ILogicOps_lprop)
        (adds 10)
        (@ILogic.ltrue Imp.lprop Imp.ILogicOps_lprop)).
unfold adds.
match goal with
  | |- ?goal =>
    let k g :=
        pose g
    in
    reify_expr Reify.reify_imp k [ True ] [ goal ]
end.