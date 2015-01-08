Require Import MirrorCore.RTac.RTac.
Require Import MirrorCharge.Imp.Goal.
Require Import MirrorCharge.Imp.ImpTac.
Require Import MirrorCharge.Imp.SymEvalLemmas.
Require MirrorCharge.Imp.STacCancel.
Require Import MirrorCharge.Imp.Syntax.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance RSOk.
Local Existing Instance Expr_expr.
Local Existing Instance ExprOk_expr.

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
  REC n (fun rec : imp_tac =>
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

Lemma runTacK_sound : forall t, rtacK_sound t -> rtac_sound (runTacK t).
Proof.
  unfold rtacK_sound, rtac_sound, runTacK, rtac_spec, rtacK_spec. intros.
  eapply H; eauto.
Qed.

Lemma simplify_tac_sound : rtac_sound simplify_tac.
apply SIMPLIFY_sound.
Qed.

Lemma entailment_tac_sound : rtac_sound entailment_tac.
Admitted.

Lemma entailment_tac_solve_sound : rtac_sound entailment_tac_solve.
apply SOLVE_sound. apply entailment_tac_sound.
Qed.


Ltac rtac_derive_soundness' tac tacK lems :=
  let lems := (auto ; lems) in
  let rec rtac :=
      try first [ simple eapply IDTAC_sound
                | simple eapply FAIL_sound
                | simple eapply FIRST_sound ; Forall_rtac
                | simple eapply SOLVE_sound ; rtac
                | simple eapply THEN_sound ;
                  [ rtac
                  | rtacK ]
                | simple eapply TRY_sound ; rtac
                | simple eapply REPEAT_sound ; rtac
                | simple eapply REC_sound ; intros; rtac
                | simple eapply AT_GOAL_sound ; [ intros ; rtac ]
                | simple eapply APPLY_sound ; [ lems ]
                | simple eapply EAPPLY_sound ; [ lems ]
                | simple eapply runTacK_sound ; [ rtacK ]
                | solve [ eauto ]
                | tac rtac rtacK lems
                ]
  with rtacK :=
      try first [ simple eapply runOnGoals_sound ; rtac
                | simple eapply MINIFY_sound
                | simple eapply THENK_sound ; [ try rtacK | try rtacK ]
                | solve [ eauto ]
                | tacK rtac rtacK lems
                | eapply runOnGoals_sound ; rtac
                ]
  with Forall_rtac :=
      repeat first [ eapply Forall_nil
                   | eapply Forall_cons ;
                     [ rtac
                     | Forall_rtac ]
                   | solve [ eauto ] ]
  in
  match goal with
    | |- rtac_sound _ => rtac
    | |- rtacK_sound _ => rtacK
    | |- Forall rtac_sound _ => Forall_rtac
  end.

Ltac rtac_derive_soundness_default :=
  rtac_derive_soundness' ltac:(fun rtac _ _ =>
                                 match goal with
                                   | |- rtac_sound match ?X with _ => _ end =>
                                     destruct X; rtac
                                 end)
                         ltac:(fun _ _ _ => fail)
                         ltac:(idtac).

Lemma EAPPLY_THEN_sound : forall lem tac,
                            Lemma.lemmaD (exprD'_typ0 (T:=Prop)) nil nil lem -> rtac_sound tac -> 
                            rtac_sound (EAPPLY_THEN lem tac).
Proof. intros; unfold EAPPLY_THEN.
       rtac_derive_soundness_default.
Qed.

Lemma EAPPLY_THEN_1_sound
: forall lem tac1 tac2,
    Lemma.lemmaD (exprD'_typ0 (T:=Prop)) nil nil lem ->
    rtac_sound tac1 -> rtacK_sound tac2 ->
    rtac_sound (EAPPLY_THEN_1 lem tac1 tac2).
Proof. intros; unfold EAPPLY_THEN_1.
       rtac_derive_soundness_default.
Qed.

Ltac one_of lems :=
  match lems with
    | (?X,?Y) => first [ one_of X | one_of Y ]
    | _ => exact lems
  end.

Ltac red_lemma :=
  unfold Lemma.lemmaD, Lemma.lemmaD'; simpl;
  unfold ExprDsimul.ExprDenote.exprT_App, ExprDsimul.ExprDenote.exprT_Abs, exprT_Inj, SymEnv.funcD, ExprDsimul.ExprDenote.Rcast_val, ExprDsimul.ExprDenote.Rcast; simpl.

Hint Immediate Imp.SeqA_rule
     Imp.Assign_seq_rule Imp.Assign_tail_rule
     Imp.Read_seq_rule Imp.Read_tail_rule
     Imp.Write_seq_rule Imp.Write_tail_rule : the_hints.

Ltac rtac_derive_soundness_with :=
  rtac_derive_soundness' ltac:(fun rtac rtacK lem =>
                                 first [ eapply EAPPLY_THEN_sound ; [ lem | rtac ]
                                       | eapply EAPPLY_THEN_1_sound ; [ lem | rtac | rtacK ]
                                       | eapply simplify_tac_sound
                                       | eapply entailment_tac_sound
                                       | eapply entailment_tac_solve_sound
                                       | match goal with
                                           | |- rtac_sound match ?X with _ => _ end =>
                                             destruct X; rtac
                                         end ])
                         ltac:(fun _ _ => fail)
                         ltac:(idtac "lemma"; try solve [ red_lemma; eauto with the_hints ]).

Goal forall n, rtac_sound (sym_eval_mem n).
intros. unfold sym_eval_mem.
rtac_derive_soundness_with.
exact Imp.Read_seq_rule.
exact Imp.Skip_seq_rule.
exact Imp.Assert_seq_rule.
exact Imp.Read_tail_rule.
exact Imp.Skip_tail_rule.
exact Imp.Assert_tail_rule.
Qed.

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

(*
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
*)

Fixpoint adds (n : nat) :=
  match n with
    | 0 => Imp.Skip
    | S n => Imp.Seq (Imp.Assign "x" (Imp.iVar "x")) (adds n)
  end%string.

Goal @ILogic.lentails Imp.SProp Imp.ILogicOps_SProp (@ILogic.ltrue Imp.SProp Imp.ILogicOps_SProp)
     (Imp.triple (@ILogic.ltrue Imp.lprop Imp.ILogicOps_lprop)
        (adds 1)
        (@ILogic.ltrue Imp.lprop Imp.ILogicOps_lprop)).
unfold adds.
match goal with
  | |- ?goal =>
    let k g :=
        pose g
    in
    reify_expr Reify.reify_imp k [ True ] [ goal ]
end.


Check rtac_Solved_closed_soundness.
pose (runRtac typ (expr typ func) nil nil e (sym_eval_mem 2)).
assert (r = Fail).
vm_compute.
vm_compute in r.
let result := constr:(runRtac typ (expr typ func) nil nil e (sym_eval_mem 100)) in
let resultV := eval vm_compute in result in
idtac resultV ;
match resultV with
| Solved _ => idtac "Solved"
| More_ _ _ => idtac "More_"
end.