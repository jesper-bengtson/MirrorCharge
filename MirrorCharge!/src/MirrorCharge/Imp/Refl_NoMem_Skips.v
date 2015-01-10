Require Import MirrorCore.RTac.RTac.
Require Import MirrorCharge.Imp.Goal.
Require Import MirrorCharge.Imp.ImpTac.
Require Import MirrorCharge.Imp.SymEvalLemmas.
Require MirrorCharge.Imp.STacCancel.
Require Import MirrorCharge.Imp.Syntax.
Require Import MirrorCharge.Imp.RTacTauto.
Require Import MirrorCharge.Imp.RTacSubst.
Require Import Coq.Strings.String.

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

Definition runTacK (tac : imp_tacK) : imp_tac :=
  fun a b c d e f g => tac a b c d e f (GGoal g).

Fixpoint THENS (ls : list imp_tac) : imp_tac :=
  match ls with
    | nil => IDTAC
    | l :: ls => THEN l (runOnGoals (THENS ls))
  end.

Definition side_solver : imp_tac :=
  THENS (TRY (THENS (EAPPLY go_lower_lemma ::
                            INTRO_All ::
                            BETA_REDUCE :: nil)) ::
             TRY (EAPPLY embed_ltrue_lemma) ::
             SIMPLIFY ::
             STacCancel.stac_cancel ::
             SIMPLIFY :: tauto_tac :: nil).

Definition entailment_tac : imp_tac :=
  ON_ENTAILMENT
    (THENS (TRY (EAPPLY embed_ltrue_lemma) ::
            TRY (THENS (EAPPLY entails_exL_lemma ::
                 INTRO_All ::
                 BETA_REDUCE :: nil)) ::
            TRY (THENS (EAPPLY go_lower_raw_lemma ::
                        BETA_REDUCE :: INTRO_All ::
                        BETA_REDUCE :: nil)) ::
            SIMPLIFY :: SIMPLIFY ::
            REPEAT 25
               (THENS (APPLY pull_embed_hyp_lemma :: INTRO_Hyp :: nil)) ::
            tauto_tac :: nil))
    IDTAC.

Definition simplify_tac : imp_tac := SIMPLIFY.

Definition entailment_tac_solve : imp_tac :=
   SOLVE entailment_tac.

Definition EAPPLY_THEN a (b : imp_tac) : imp_tac :=
  runTacK (THENK (EAPPLY a : imp_tacK) (runOnGoals b)).


Definition EAPPLY_THEN_1 a (side : imp_tac) (b : imp_tacK) : imp_tac :=
  THEN (THEN (EAPPLY a) (runOnGoals (TRY (SOLVE side))))
       (THENK (@MINIFY _ _ _)
              (runOnGoals (AT_GOAL (fun _ _ goal =>
                                      match goal with
                                        | App (App entails _) (App (App (App triple _) _) _) =>
                                          runTacK b
                                        | _ => IDTAC
                                      end)))).

Definition sym_eval_no_mem (n : nat) : imp_tac :=
  REC n (fun rec : imp_tac =>
           let rec : imp_tac := THEN simplify_tac (runOnGoals rec) in
           TRY (FIRST (   EAPPLY_THEN SeqA_lemma rec
                  :: EAPPLY_THEN triple_exL_lemma
                          (THEN INTRO_All (runOnGoals rec))
                  :: EAPPLY_THEN Assign_seq_lemma rec
                  :: EAPPLY_THEN Skip_seq_lemma rec
                  :: EAPPLY_THEN_1 Assert_seq_lemma entailment_tac (runOnGoals rec)
                  :: EAPPLY_THEN Assign_tail_lemma (entailment_tac)
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

Ltac one_of lems :=
  match lems with
    | (?X,?Y) => first [ one_of X | one_of Y ]
    | _ => exact lems
  end.

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

Ltac red_lemma :=
  unfold Lemma.lemmaD, Lemma.lemmaD'; simpl;
  unfold ExprDsimul.ExprDenote.exprT_App, ExprDsimul.ExprDenote.exprT_Abs, exprT_Inj, SymEnv.funcD, ExprDsimul.ExprDenote.Rcast_val, ExprDsimul.ExprDenote.Rcast; simpl.

Lemma EAPPLY_THEN_1_sound
: forall lem tac1 tac2,
    Lemma.lemmaD (exprD'_typ0 (T:=Prop)) nil nil lem ->
    rtac_sound tac1 -> rtacK_sound tac2 ->
    rtac_sound (EAPPLY_THEN_1 lem tac1 tac2).
Proof. intros; unfold EAPPLY_THEN_1.
       rtac_derive_soundness_default.
Qed.

Hint Immediate Imp.SeqA_rule
     Imp.Assign_seq_rule Imp.Assign_tail_rule
     Imp.Read_seq_rule Imp.Read_tail_rule
     Imp.Write_seq_rule Imp.Write_tail_rule
     Imp.triple_exL Imp.Skip_seq_rule
     Imp.Assert_seq_rule
     Imp.Assert_tail_rule Imp.Skip_tail_rule
: the_hints.

Ltac rtac_derive_soundness_with :=
  rtac_derive_soundness' ltac:(fun rtac rtacK lem =>
                                 first [ eapply EAPPLY_THEN_sound ; [ lem | rtac ]
                                       | eapply EAPPLY_THEN_1_sound ; [ lem | rtac | rtacK ]
                                       | eapply simplify_tac_sound
                                       | eapply entailment_tac_sound
                                       | eapply entailment_tac_solve_sound
                                       | eapply INTRO_All_sound
                                       | match goal with
                                           | |- rtac_sound match ?X with _ => _ end =>
                                             destruct X; rtac
                                         end ])
                         ltac:(fun _ _ => fail)
                         ltac:(try solve [ red_lemma; eauto with the_hints
                                         | one_of Imp.triple_exL ]).

Theorem sym_eval_mem_sound : forall n, rtac_sound (sym_eval_no_mem n).
(*
intros. unfold sym_eval_no_mem.
rtac_derive_soundness_with.
Qed.
*)
Admitted.

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
         Traversable.mapT
         Option.Applicative_option List.Traversable_list
         List.mapT_list map Quant._impls
         amap_substD FMapSubst.SUBST.raw_substD UVarMap.MAP.fold
         FMapPositive.PositiveMap.fold FMapPositive.PositiveMap.xfoldi
         FMapPositive.append Quant._exists
         UVarMap.MAP.from_key pred BinPos.Pos.to_nat BinPos.Pos.iter_op
         Applicative.ap Applicative.pure
       ] in e.

Ltac the_solver :=
  match goal with
    | |- ?goal =>
      let k g :=
          pose (e := g) ;
          let result := constr:(runRtac typ (expr typ func) nil nil e (sym_eval_no_mem 100)) in
          let resultV := eval vm_compute in result in
      match resultV with
        | Solved _ =>
          change (propD _ _ nil nil e) ;
            cut(result = resultV) ;
            [ set (pf := @rtac_Solved_closed_soundness
                           typ (expr typ func)
                           _ _ _ _ (sym_eval_no_mem 100)
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
                           _ _ _ _ (sym_eval_no_mem 100)
                           (sym_eval_mem_sound 100) nil nil e g'V) ;
                  exact pf
                | vm_cast_no_check (@eq_refl _ resultV) ]
              | clear g'V e ]
          end
      end
        in
          reify_expr Reify.reify_imp k [ True ] [ goal ]
  end.

Goal @ILogic.lentails Imp.SProp Imp.ILogicOps_SProp (@ILogic.ltrue Imp.SProp Imp.ILogicOps_SProp)
     (Imp.triple (@ILogic.ltrue Imp.lprop Imp.ILogicOps_lprop)
        (skips 5)
        (@ILogic.ltrue Imp.lprop Imp.ILogicOps_lprop)).
unfold skips.
Time the_solver.
Time Qed.

Goal @ILogic.lentails Imp.SProp Imp.ILogicOps_SProp (@ILogic.ltrue Imp.SProp Imp.ILogicOps_SProp)
     (Imp.triple (@ILogic.ltrue Imp.lprop Imp.ILogicOps_lprop)
        (skips 10)
        (@ILogic.ltrue Imp.lprop Imp.ILogicOps_lprop)).
unfold skips.
Time the_solver.
Time Qed.

Goal @ILogic.lentails Imp.SProp Imp.ILogicOps_SProp (@ILogic.ltrue Imp.SProp Imp.ILogicOps_SProp)
     (Imp.triple (@ILogic.ltrue Imp.lprop Imp.ILogicOps_lprop)
        (skips 15)
        (@ILogic.ltrue Imp.lprop Imp.ILogicOps_lprop)).
unfold skips.
Time the_solver.
Time Qed.

Goal @ILogic.lentails Imp.SProp Imp.ILogicOps_SProp (@ILogic.ltrue Imp.SProp Imp.ILogicOps_SProp)
     (Imp.triple (@ILogic.ltrue Imp.lprop Imp.ILogicOps_lprop)
        (skips 20)
        (@ILogic.ltrue Imp.lprop Imp.ILogicOps_lprop)).
unfold skips.
Time the_solver.
Time Qed.
