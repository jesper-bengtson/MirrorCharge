(** This file implements an interface to [expr] that
 ** makes star, emp, and pure assertions apparent.
 **)
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.
Require Import BILogic.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.AppFull.
Require Import ILogicFunc.

Set Implicit Arguments.
Set Strict Implicit.

Section seplog_fold.
  Variable ts : types.
  Variable sym : Type.
  Variable RSym_sym : RSym (typD ts) sym.

  Variable T : Type.
  Variable SL : typ.

  Record SepLogArgs : Type :=
  { do_atomic_app : expr sym -> list (expr sym) -> T
  ; do_pure : expr sym -> T
  ; do_emp : T
  ; do_star : T -> T -> T
  }.

  Record SepLogSpec : Type :=
  { is_pure : expr sym -> bool
  ; is_emp : sym -> bool
  ; is_star : sym -> bool
  }.

  Variable sla : SepLogArgs.
  Variable sls : SepLogSpec.

  Record SepLogArgsOk (R_t : expr sym -> T -> tenv typ -> tenv typ -> Prop) : Type :=
  { atomic_appOk
    : forall e es tus tvs,
        typeof_apps _ tus tvs e es = Some SL ->
        R_t (apps e es) (sla.(do_atomic_app) e es) tus tvs
  ; pureOk
    : forall e tus tvs,
        typeof_expr tus tvs e = Some SL ->
        sls.(is_pure) e = true ->
        R_t e (sla.(do_pure) e) tus tvs
  ; empOk
    : forall e tus tvs,
        typeof_sym e = Some SL ->
        sls.(is_emp) e = true ->
        R_t (Inj e) sla.(do_emp) tus tvs
  ; starOk
    : forall e l r l_res r_res tus tvs,
        typeof_sym e = Some (tyArr SL (tyArr SL SL)) ->
        typeof_expr tus tvs l = Some SL ->
        typeof_expr tus tvs r = Some SL ->
        sls.(is_star) e = true ->
        R_t l l_res tus tvs ->
        R_t r r_res tus tvs ->
        R_t (apps (Inj e) (l :: r :: nil)) (sla.(do_star) l_res r_res) tus tvs
  }.

  Definition AppFullFoldArgs_SepLogArgs (sla : SepLogArgs) : AppFullFoldArgs sym T :=
    match sla , sls with
      | {| do_atomic_app := do_atomic_app
         ; do_pure := do_pure
         ; do_star := do_star
         ; do_emp := do_emp |}
      , {| is_pure := is_pure
         ; is_star := is_star
         ; is_emp := is_emp |} =>
        {| do_var := fun v _ _ => do_atomic_app (Var v) nil
         ; do_uvar := fun u _ _ => do_atomic_app (UVar u) nil
         ; do_inj := fun i _ _ =>
                       if is_emp i then
                         do_emp
                       else
                         do_atomic_app (Inj i) nil
         ; do_abs := fun t e _ _ _ => do_atomic_app (Abs t e) nil
         ; do_app := fun f _ args tus tvs =>
                       match f with
                         | Inj i =>
                           if is_star i then
                             match args with
                               | (_,l) :: (_,r) :: nil =>
                                 do_star (l tus tvs) (r tus tvs)
                               | _ => do_emp
                             end
                           else
                             do_atomic_app f (map fst args)
                         | _ =>
                           do_atomic_app f (map fst args)
                       end
        |}
    end.

  Section sound.
    Context R_t `{slaok : SepLogArgsOk R_t}.

    Lemma atomic_ok
    : forall (tus tvs : tenv typ) e (t : typ),
        typeof_expr tus tvs e = Some t ->
        t = SL ->
        R_t e (sla.(do_atomic_app) e nil) tus tvs.
    Proof.
      destruct slaok. simpl; intros. subst.
      change e with (apps e nil) at 1.
      eapply atomic_appOk0. unfold typeof_apps.
      simpl. rewrite H. auto.
    Qed.

    Hypothesis BILOps : BILOperators (typD ts nil SL).
    Hypothesis is_starOk
    : forall i,
        sls.(is_star) i = true ->
        typeof_sym i = Some (tyArr SL (tyArr SL SL)).

    Definition AppFullFoldArgsOk_SepLogsOk
    : AppFullFoldArgsOk _ (AppFullFoldArgs_SepLogArgs sla)
                        (fun t e res tus tvs =>
                           t = SL ->
                           R_t e res tus tvs).
    Proof.
      remember sla as s; destruct s; simpl; remember sls as s; destruct s.
      constructor.
      { simpl; intros.
        replace do_atomic_app0 with (sla.(do_atomic_app)).
        eapply atomic_ok; eauto. rewrite <- Heqs; reflexivity. }
      { simpl; intros.
        replace do_atomic_app0 with (sla.(do_atomic_app)).
        eapply atomic_ok; eauto. rewrite <- Heqs; reflexivity. }
      { simpl; intros.
        consider (is_emp0 v); intros.
        { replace do_emp0 with (sla.(do_emp)).
          eapply (@empOk _ slaok); eauto.
          Cases.rewrite_all_goal. auto.
          rewrite <- Heqs0. simpl. auto.
          rewrite <- Heqs. reflexivity. }
        { replace do_atomic_app0 with (sla.(do_atomic_app)).
          eapply atomic_ok; eauto. rewrite <- Heqs; reflexivity. } }
      { simpl; intros.
        replace do_atomic_app0 with (sla.(do_atomic_app)).
        eapply atomic_ok; eauto. rewrite <- Heqs; reflexivity. }
      { intros. subst ft. simpl.
        assert (typeof_apps RSym_sym tus tvs l (map fst rs) = Some SL).
        { rewrite <- typeof_expr_apps. congruence. }
        generalize (atomic_appOk slaok). rewrite <- Heqs. simpl.
        destruct l; auto.
        consider (is_star0 s); eauto; intros.
        { generalize H4. eapply is_starOk in H4.
          unfold typeof_apps in H3.
          simpl in H3. rewrite H4 in *.
          inversion H1; clear H1; try subst.
          { subst rs ts0; intros.
            simpl in *. clear - H3. inv_all.
            symmetry in H3. eapply tyArr_circ_L in H3. intuition. }
          { subst rs ts0. inversion H7; clear H7.
            { subst l l'; intros; simpl in *.
              rewrite H4 in *. forward.
              intuition. inv_all. subst y t0.
              clear - H8. symmetry in H8.
              eapply tyArr_circ_L in H8. intuition. }
            { subst l l'. inversion H8; clear H8.
              { subst l0 l'0. intuition. subst t.
                destruct y, y0; simpl in *.
                rewrite H8 in *. rewrite H6 in *. rewrite H4 in *.
                unfold type_of_apply in *. forward.
                inv_all.
                subst x0 x t1 t2 t3 p0 p.
                replace do_star0 with (sla.(do_star));
                  [ | rewrite <- Heqs; reflexivity ].
                eapply (starOk slaok); eauto.
                rewrite <- Heqs0. auto. }
              { exfalso. clear Heqs Heqs0. subst.
                simpl in H3. intuition.
                rewrite H2 in *. rewrite H6 in *. rewrite H1 in *.
                forward. inv_all; try subst.
                clear H15 H13. subst x x0 x1.
                clear - H14.
                eapply type_of_applys_circle_False in H14. auto. } } } } }
    Qed.

    Definition seplog_fold (sla : SepLogArgs) : expr sym -> tenv typ -> tenv typ -> T :=
      app_fold_args (AppFullFoldArgs_SepLogArgs sla).

    Theorem seplog_fold_sound
    : forall e tus tvs result,
        seplog_fold sla e tus tvs = result ->
        typeof_expr tus tvs e = Some SL ->
        R_t e result tus tvs.
    Proof.
      intros.
      eapply (app_fold_args_sound AppFullFoldArgsOk_SepLogsOk) in H; eauto. 
    Qed.
  End sound.
End seplog_fold.
