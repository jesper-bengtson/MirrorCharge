Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCharge.Imp.ImpTac.
Require Import MirrorCharge.Imp.Syntax.
Require Import MirrorCharge.Imp.SymEvalLemmas.

Require Import MirrorCharge.Imp.incr_demo_stuff.

Require Import Even.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance RSOk.
Local Existing Instance Expr_expr.
Local Existing Instance ExprOk_expr.

Definition EAUTO_using (depth : nat) (lems : list lemma) : imp_tac :=
  REC depth
      (fun rec : imp_tac =>
         FIRST (List.map (fun lem => SOLVE (THEN (EAPPLY lem) rec)) lems))
      IDTAC.


Theorem EAUTO_sound
: forall depth lems,
    Forall ProvableLemma lems ->
    rtac_sound (EAUTO_using depth lems).
Proof.
  intros. unfold EAUTO_using.
  rtac_derive_soundness_with.
  induction H.
  - constructor.
  - constructor; try auto.
    rtac_derive_soundness_with.
Qed.























Definition even_O_lemma : lemma.
reify_lemma even_O.
Defined.
Definition even_S_lemma : lemma.
reify_lemma even_S.
Defined.
Definition odd_S_lemma : lemma.
reify_lemma odd_S.
Defined.


Definition the_tactic : imp_tac :=
       (EAUTO_using 500 (even_S_lemma :: odd_S_lemma :: even_O_lemma :: nil)).

Goal even 400.
  Time repeat constructor.
Time Qed.

Goal even 400.
(*  Time run_tactic the_tactic. *)




Fixpoint make_nat (n : nat) : expr typ func :=
  match n with
    | 0 => fConst 0
    | S n => App fS (make_nat n)
  end.

Fixpoint convert_S (e : expr typ func) : expr typ func :=
  match e with
    | App l r => App (convert_S l) (convert_S r)
    | Abs t e => Abs t (convert_S e)
    | Inj (inl (inr (pNat n))) => make_nat n
    | _ => e
  end.

Definition convert_to_S : imp_tac :=
  fun _ _ _ _ _ sub g =>
    More_ sub (GGoal (convert_S g)).
(** Need to prove this sound... **)

Definition the_tactic' : imp_tac :=
  THEN convert_to_S
       (EAUTO_using 500 (even_S_lemma :: odd_S_lemma :: even_O_lemma :: nil)).

Time run_tactic the_tactic'.
Time Qed.

































































Eval vm_compute in
doIt (THENS (   SIMPLIFY
             :: EAPPLY entails_exL_lemma :: BETA_REDUCE :: INTRO_All :: BETA_REDUCE
              :: EAPPLY go_lower_raw_lemma
              :: BETA_REDUCE :: INTRO_All :: BETA_REDUCE
              :: REPEAT 200
                   (THENS (APPLY pull_embed_hyp_lemma :: INTRO_Hyp :: nil))
              :: TRY (THENS (EAPPLY pull_embed_last_lemma :: INTRO_Hyp :: nil))
              :: TRY (EAPPLY prove_Prop_lemma)
              :: TRY (THENS (EAPPLY eq_trans_hyp_lemma ::
                             TRY EASSUMPTION :: nil))
              :: INSTANTIATE
              :: TRY prove_eq_tac
              :: nil)).



Definition PHASE3_tauto : imp_tac :=
  let leaf :=
      (THENS (   SIMPLIFY

              :: EAPPLY go_lower_raw_lemma
              :: BETA_REDUCE :: INTRO_All :: BETA_REDUCE
              :: REPEAT 200
                   (THENS (APPLY pull_embed_hyp_lemma :: INTRO_Hyp :: nil))
              :: TRY (THENS (EAPPLY pull_embed_last_lemma :: INTRO_Hyp :: nil))
              :: TRY (EAPPLY prove_Prop_lemma)
              :: TRY (THENS (EAPPLY eq_trans_hyp_lemma ::
                             TRY EASSUMPTION :: nil))
              :: INSTANTIATE
              :: TRY prove_eq_tac
              :: nil))
  in
  sym_eval_only 100
     (THENS (   SIMPLIFY
             :: EAPPLY embed_ltrue_lemma
             :: EAPPLY entails_exL_lemma
             :: BETA_REDUCE :: INTRO_All :: BETA_REDUCE
             :: tauto_tac leaf :: nil)).

Fixpoint parse_ands (e : expr typ func) : list (expr typ func) :=
  match e with
    | App (App (Inj (inr (ILogicFunc.ilf_and tyProp))) P) Q =>
      parse_ands P ++ parse_ands Q
    | _ => e :: nil
  end.

Definition intro_hyps : imp_tac :=
  fun _ _ _ _ _ sub g =>
    match g with
      | App (App (Inj (inr (ILogicFunc.ilf_entails tyProp))) P) Q =>
        let hyps := parse_ands P in
        let goals := parse_ands Q in
        More sub (List.fold_right GHyp (GConj_list (List.map GGoal goals)) hyps)
      | _ => More_ sub (GGoal g)
    end.

Definition PHASE3_tauto2 : imp_tac :=
  let leaf :=
      (THENS ( intro_hyps ::
               EAPPLY eq_trans_hyp_lemma ::
               TRY EASSUMPTION :: INSTANTIATE ::
               TRY prove_eq_tac
              :: nil))
  in
  sym_eval_only 100
     (THENS (   SIMPLIFY
             :: EAPPLY embed_ltrue_lemma
             :: EAPPLY entails_exL_lemma
             :: BETA_REDUCE :: INTRO_All :: BETA_REDUCE
             :: EAPPLY go_lower_raw_lemma :: INTRO_All :: BETA_REDUCE
             :: SIMPLIFY :: BETA_REDUCE :: tauto_tac leaf :: nil)).
(*
Definition the_final_tactic : imp_tac :=
  THEN (THENS (sym_eval_no_mem 100 ::
                 REPEAT 1000 (EAPPLY andI_lemma) ::
                 TRY (EAPPLY prove_Prop_lemma) ::
                 TRY (THENS (EAPPLY eq_trans_hyp_lemma ::
                             TRY EASSUMPTION :: nil)) ::
                 INSTANTIATE :: TRY prove_eq_tac :: nil)) (MINIFY).
*)

Fixpoint tryApply_each lems : imp_tac :=
  match lems with
    | nil => IDTAC
    | l :: ls =>
      THEN (TRY (EAPPLY l)) (runOnGoals (tryApply_each ls))
  end.

(*
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
            REPEAT 200
               (THENS (APPLY pull_embed_hyp_lemma :: INTRO_Hyp :: nil)) ::
            TRY (THENS (EAPPLY pull_embed_last_lemma :: INTRO_Hyp :: nil)) ::
            (* tauto_tac :: *) nil))
    IDTAC.

Definition entailment_tac_solve : imp_tac :=
   SOLVE entailment_tac.

*)

(*
Lemma entailment_tac_sound : rtac_sound entailment_tac.
  unfold entailment_tac.
  About ON_ENTAILMENT.
Admitted.

Lemma entailment_tac_solve_sound : rtac_sound entailment_tac_solve.
apply SOLVE_sound. apply entailment_tac_sound.
Qed.
*)

(*
Lemma runTacK_sound : forall t, rtacK_sound t -> rtac_sound (runTacK t).
Proof.
  unfold rtacK_sound, rtac_sound, runTacK, rtac_spec, rtacK_spec. intros.
  eapply H; eauto.
Qed.
*)

(*
Lemma simplify_tac_sound : rtac_sound simplify_tac.
apply SIMPLIFY_sound.
Qed.
*)

(*
Definition PHASE2 : imp_tac :=
  sym_eval_only 100 SIMPLIFY.

