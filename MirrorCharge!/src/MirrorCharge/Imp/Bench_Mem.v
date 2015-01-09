Require Import MirrorCore.RTac.RTac.
Require Import MirrorCharge.Imp.Goal.
Require Import MirrorCharge.Imp.ImpTac.
Require Import MirrorCharge.Imp.SymEvalLemmas.
Require MirrorCharge.Imp.STacCancel.
Require Import MirrorCharge.Imp.Syntax.
Require Import MirrorCharge.Imp.RTacTauto.
Require Import MirrorCharge.Imp.RTacSubst.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance RSOk.
Local Existing Instance Expr_expr.
Local Existing Instance ExprOk_expr.

Fixpoint tryApply_each (ls : list (Lemma.lemma typ (expr typ func) (expr typ func))) : imp_tac :=
  match ls with
    | nil => IDTAC
    | l :: ls =>
      THEN (TRY (EAPPLY l)) (runOnGoals (tryApply_each ls))
  end.

Definition entailment_tac : imp_tac :=
  ON_ENTAILMENT
    (REPEAT 2 (THEN (tryApply_each (embed_ltrue_lemma :: go_lower_lemma :: nil))
       (runOnGoals (THEN SIMPLIFY (runOnGoals (THEN STacCancel.stac_cancel (runOnGoals tauto_tac)))))))
    IDTAC.

(*
Definition entailment_tac : imp_tac :=
  THEN SIMPLIFY (runOnGoals tauto_tac).
*)
Definition simplify_tac : imp_tac := SIMPLIFY.

Definition entailment_tac_solve : imp_tac :=
   SOLVE entailment_tac.


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
           let rec : imp_tac := THEN simplify_tac (runOnGoals rec) in
           TRY (FIRST (   EAPPLY_THEN SeqA_lemma rec
                  :: EAPPLY_THEN triple_exL_lemma
                          (THEN INTRO_All (runOnGoals rec))
                  :: EAPPLY_THEN Assign_seq_lemma rec
                  :: EAPPLY_THEN_1 Read_seq_lemma entailment_tac (runOnGoals rec)
                  :: EAPPLY_THEN_1 Write_seq_lemma entailment_tac (runOnGoals rec)
                  :: EAPPLY_THEN Skip_seq_lemma rec
                  :: EAPPLY_THEN_1 Assert_seq_lemma entailment_tac (runOnGoals rec)
                  :: EAPPLY_THEN Assign_tail_lemma (TRY entailment_tac)
                  :: EAPPLY_THEN Read_tail_lemma (TRY entailment_tac)
                  :: EAPPLY_THEN Write_tail_lemma (TRY entailment_tac)
                  :: EAPPLY_THEN Skip_tail_lemma (TRY entailment_tac)
                  :: EAPPLY_THEN Assert_tail_lemma (TRY entailment_tac)
                  :: nil)))
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

Theorem sym_eval_mem_sound : forall n, rtac_sound (sym_eval_mem n).
(*intros. unfold sym_eval_mem.
rtac_derive_soundness_with.
exact Imp.Read_seq_rule.
exact Imp.Skip_seq_rule.
exact Imp.Assert_seq_rule.
exact Imp.Read_tail_rule.
exact Imp.Skip_tail_rule.
exact Imp.Assert_tail_rule.
Qed.
*)
Admitted.


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

Fixpoint adds (n : nat) :=
  match n with
    | 0 => Imp.Skip
    | S n => Imp.Seq (Imp.Assign "x" (Imp.iPlus (Imp.iVar "x") (Imp.iConst 1))) (adds n)
  end%string.

Ltac reduce_propD g e :=
  eval cbv beta iota zeta delta
       [ goalD g Ctx.propD exprD'_typ0 exprD' Expr_expr
         ExprD.Expr_expr ExprDsimul.ExprDenote.exprD'
         ExprDsimul.ExprDenote.func_simul typeof_sym RS
         SymSum.RSym_sum
         RSym_ilfunc typ2_match ExprDsimul.ExprDenote.funcAs
         exprT_Inj ExprDsimul.ExprDenote.exprT_App ExprDsimul.ExprDenote.exprT_Abs
         ILogicFunc.RSym_ilfunc RelDec_eq_typ ILogicFunc.typeof_func eops lops Typ2_Fun
         typ2 type_cast RType_typ type_cast_typ typ0 Typ0_Prop
         eq_sym typ2_cast typ0_cast ExprDsimul.ExprDenote.Rcast
         ExprDsimul.ExprDenote.Rcast_val eq_rect Relim Rsym Rrefl symD
         ILogicFunc.funcD RSym_imp_func typeof_sym_imp
         exprT_UseV ExprDsimul.ExprDenote.exprT_GetVAs
         exprT_UseU ExprDsimul.ExprDenote.exprT_GetUAs
         nth_error_get_hlist_nth  Monad.bind Monad.ret OptionMonad.Monad_option
         ILogicFunc.typ2_cast_quant ILogicFunc.typ2_cast_bin
         HList.hlist_hd HList.hlist_tl TypesI.typD typD
         BinPos.Pos.succ
         FMapPositive.PositiveMap.empty
         SymEnv.ftype SymEnv.fdenote
         SymEnv.RSym_func SymEnv.func_typeof_sym FMapPositive.PositiveMap.find fs SymEnv.from_list FMapPositive.PositiveMap.add
         SymEnv.funcD tyLProp app
         Quant._foralls HList.hlist_app
       ] in e.
Ltac the_solver :=
  match goal with
    | |- ?goal =>
      let k g :=
          pose (e := g) ;
          let result := constr:(runRtac typ (expr typ func) nil nil e (sym_eval_mem 100)) in
          let resultV := eval vm_compute in result in
      idtac resultV ;
      match resultV with
        | Solved _ =>
          change (propD _ _ nil nil e) ;
            cut(result = resultV) ;
            [ set (pf := @rtac_Solved_closed_soundness
                           typ (expr typ func)
                           _ _ _ _ (sym_eval_mem 100)
                           (sym_eval_mem_sound 100) nil nil e)
              ; exact pf
            | vm_cast_no_check (@eq_refl _ resultV) ]
        | More_ _ ?g' =>
          pose (g'V := g') ;
          let post := constr:(match @goalD _ _ _ _ _ nil nil g'V with
                                | Some G => G HList.Hnil HList.Hnil
                                | None => True
                              end) in
          let post := reduce_propD g'V post in
          match post with
            | ?G =>
              cut G ;
              [ change (@closedD _ _ _ _ _ nil nil g g'V) ;
                cut (result = More_ (@TopSubst _ _ _ _) g'V) ;
                [ set (pf := @rtac_More_closed_soundness
                           typ (expr typ func)
                           _ _ _ _ (sym_eval_mem 100)
                           (sym_eval_mem_sound 100) nil nil e g'V) ;
                  exact pf
                | vm_cast_no_check (@eq_refl _ resultV) ]
              | clear g'V e ]
          end
      end
        in
          reify_expr Reify.reify_imp k [ True ] [ goal ]
  end.

Ltac the_tauto :=
  match goal with
    | |- ?goal =>
      let k g :=
          pose (e := g) ;
          let result := constr:(runRtac typ (expr typ func) nil nil e (tauto_tac)) in
          let resultV := eval vm_compute in result in
      match resultV with
        | Solved _ =>
          change (propD _ _ nil nil e) ;
            cut(result = resultV) ;
            [ set (pf := @rtac_Solved_closed_soundness
                           typ (expr typ func)
                           _ _ _ _ (tauto_tac)
                           (tauto_tac_sound) nil nil e)
              ; exact pf
            | vm_cast_no_check (@eq_refl _ resultV) ]
        | More_ _ ?g' =>
          pose (g'V := g') ;
          let post := constr:(match @goalD _ _ _ _ _ nil nil g'V with
                                | Some G => G HList.Hnil HList.Hnil
                                | None => True
                              end) in
          let post := reduce_propD g'V post in
          match post with
            | ?G =>
              cut G ;
              [ change (@closedD _ _ _ _ _ nil nil e g'V) ;
                cut (result = More_ (@TopSubst _ _ _ _) g'V) ;
                [ set (pf := @rtac_More_closed_soundness
                           typ (expr typ func)
                           _ _ _ _ (tauto_tac)
                           (tauto_tac_sound) nil nil e g'V) ;
                  exact pf
                | vm_cast_no_check (@eq_refl _ resultV) ]
              | clear g'V e ]
          end
        | Fail => idtac "failed"
      end
        in
          reify_expr Reify.reify_imp k [ True ] [ goal ]
  end.

Ltac run_tactic tac :=
  match goal with
    | |- ?goal =>
      let k g :=
          pose (e := g) ;
          let result := constr:(runRtac typ (expr typ func) nil nil e tac) in
          let resultV := eval vm_compute in result in
      idtac resultV ;
      match resultV with
        | Solved _ =>
          change (propD _ _ nil nil e) ;
            cut(result = resultV) ;
            [ admit
            | vm_cast_no_check (@eq_refl _ resultV) ]
        | More_ _ ?g' =>
          pose (g'V := g') ;
          let post := constr:(match @goalD _ _ _ _ _ nil nil g'V with
                                | Some G => G HList.Hnil HList.Hnil
                                | None => True
                              end) in
          let post := reduce_propD g'V post in
          match post with
            | ?G =>
              cut G ;
              [ change (@closedD _ _ _ _ _ nil nil g g'V) ;
                idtac "change success" ;
                cut (result = More_ (@TopSubst _ _ _ _) g'V) ;
                [ admit
                | vm_cast_no_check (@eq_refl _ resultV) ]
              | clear g'V e ]
          end
        | Fail => idtac "failed"
      end
        in
          reify_expr Reify.reify_imp k [ True ] [ goal ]
  end.

Ltac just_reify tac :=
  match goal with
    | |- ?goal =>
      let k g :=
          pose (e := g) ;
          let result := constr:(runRtac typ (expr typ func) nil nil e tac) in
          let resultV := eval vm_compute in result in
          pose resultV
        in
          reify_expr Reify.reify_imp k [ True ] [ goal ]
  end.


(*
Goal @ILogic.lentails Imp.SProp Imp.ILogicOps_SProp (@ILogic.ltrue Imp.SProp Imp.ILogicOps_SProp)
     (Imp.triple (@ILogic.ltrue Imp.lprop Imp.ILogicOps_lprop)
        (adds 15)
        (@ILogic.ltrue Imp.lprop Imp.ILogicOps_lprop)).
unfold adds.
Time the_solver.
Qed.

Goal @ILogic.lentails Imp.SProp Imp.ILogicOps_SProp (@ILogic.ltrue Imp.SProp Imp.ILogicOps_SProp)
     (Imp.triple (@ILogic.lfalse Imp.lprop Imp.ILogicOps_lprop)
        Imp.Skip
        (@ILogic.lfalse Imp.lprop Imp.ILogicOps_lprop)).
Time the_solver.
Qed.
*)


Goal @ILogic.lentails Imp.SProp Imp.ILogicOps_SProp (@ILogic.ltrue Imp.SProp Imp.ILogicOps_SProp)
     (Imp.triple
        ((@Applicative.ap (ILInsts.Fun Imp.locals)
              (Imp.Applicative_Fun Imp.locals) Imp.value Imp.HProp
              (@Applicative.ap (ILInsts.Fun Imp.locals)
                 (Imp.Applicative_Fun Imp.locals) Imp.value
                 (Imp.value -> Imp.HProp)
                 (@Applicative.pure (ILInsts.Fun Imp.locals)
                    (Imp.Applicative_Fun Imp.locals)
                    (Imp.value -> Imp.value -> Imp.HProp) Imp.PtsTo)
                 (Imp.eval_iexpr (Imp.iVar "y")))
              (@Applicative.pure (ILInsts.Fun Imp.locals)
                                 (Imp.Applicative_Fun Imp.locals)
                                 (Imp.value) 3)))
        (adds 2)
        ((@Applicative.ap (ILInsts.Fun Imp.locals)
              (Imp.Applicative_Fun Imp.locals) Imp.value Imp.HProp
              (@Applicative.ap (ILInsts.Fun Imp.locals)
                 (Imp.Applicative_Fun Imp.locals) Imp.value
                 (Imp.value -> Imp.HProp)
                 (@Applicative.pure (ILInsts.Fun Imp.locals)
                    (Imp.Applicative_Fun Imp.locals)
                    (Imp.value -> Imp.value -> Imp.HProp) Imp.PtsTo)
                 (Imp.eval_iexpr (Imp.iVar "y")))
              (@Applicative.pure (ILInsts.Fun Imp.locals)
                                 (Imp.Applicative_Fun Imp.locals)
                                 (Imp.value) 3))))%string.
unfold adds.
Require Import Charge.Logics.ILogic.
Time the_solver.
Print embed_ltrue_lemma.
intros.
just_reify (EAPPLY embed_ltrue_lemma).
About Imp.go_lower. About SIMPLIFY.
Set Printing Implicit.


compute in P.
just_reify (EAPPLY triple_exL_lemma).



Local Existing Instance Imp.ILogicOps_lprop.
Local Existing Instance Imp.ILogicOps_HProp.
Local Existing Instance Imp.EmbedOp_Prop_HProp.

Lemma go_lowerX
: forall (P Q : Imp.lprop),
    (forall x : Imp.locals, P x |-- Q x) ->
    P |-- Q.
Admitted.
Lemma pull_hyp
: forall (Q : Prop) (P R : Imp.HProp),
    (Q -> (P |-- R)) ->
    (P //\\ ILEmbed.embed Q) |-- R.
Admitted.
eapply go_lowerX; intro.

repeat first [ rewrite Imp.locals_get_locals_upd
             | rewrite Imp.eval_iexpr_iPlus
             | rewrite Imp.eval_iexpr_iConst
             | rewrite Imp.eval_iexpr_iVar
             | eapply lexistsL; intro
             | eapply pull_hyp; intro ].
subst.
Qed.


(** NOTE: An alternative way to write [tauto] is using rtac
 ** this could be very useful.
 **)
