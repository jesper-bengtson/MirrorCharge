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

  Record SepLogArgs : Type :=
  { do_atomic_app : expr sym -> list (expr sym) -> T
  ; do_pure : expr sym -> T
  ; do_emp : T
  ; do_star : T -> T -> T
  }.

  Variable is_pure : expr sym -> bool.
  Variable is_emp : sym -> bool.
  Variable is_star : sym -> bool.

  Record SepLogArgsOk (ST : typ) (sla : SepLogArgs) : Type :=
  { R_t : expr sym -> T -> tenv typ -> tenv typ -> Prop
  ; Hatomic_app
    : forall e es tus tvs,
        typeof_apps _ tus tvs e es = Some ST ->
        R_t (apps e es) (sla.(do_atomic_app) e es) tus tvs
  ; Hpure
    : forall e tus tvs,
        typeof_expr tus tvs e = Some ST ->
        is_pure e = true ->
        R_t e (sla.(do_pure) e) tus tvs
  ; Hemp
    : forall e tus tvs,
        typeof_sym e = Some ST ->
        is_emp e = true ->
        R_t (Inj e) sla.(do_emp) tus tvs
  ; Hstar
    : forall e l r l_res r_res tus tvs,
        typeof_sym e = Some (tyArr ST (tyArr ST ST)) ->
        typeof_expr tus tvs l = Some ST ->
        typeof_expr tus tvs r = Some ST ->
        is_star e = true ->
        R_t l l_res tus tvs ->
        R_t r r_res tus tvs ->
        R_t (apps (Inj e) (l :: r :: nil)) (sla.(do_star) l_res r_res) tus tvs
  }.

  Definition AppFullFoldArgs_SepLogArgs (sla : SepLogArgs) : AppFullFoldArgs sym T :=
    match sla with
      | {| do_atomic_app := do_atomic_app
         ; do_pure := do_pure
         ; do_star := do_star
         ; do_emp := do_emp |} =>
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
    Context SL sla `{slaok : SepLogArgsOk SL sla}.

    Lemma atomic_ok
    : forall (tus tvs : tenv typ) e (t : typ),
        typeof_expr tus tvs e = Some t ->
        t = SL ->
        R_t slaok e (sla.(do_atomic_app) e nil) tus
            tvs.
    Proof.
      destruct sla; simpl; intros; subst.
      change e with (apps e nil) at 1.
      eapply Hatomic_app. unfold typeof_apps.
      simpl. rewrite H. auto.
    Qed.

    Hypothesis BILOps : BILOperators (typD ts nil SL).
    Hypothesis is_starOk
    : forall i,
        is_star i = true ->
        let starT := tyArr SL (tyArr SL SL) in
        exists pf : typeof_sym i = Some starT,
          sepSP = match pf in _ = u
                        return match u with
                                 | Some t => typD ts nil t
                                 | None => unit
                               end
                  with
                    | eq_refl => symD i
                  end.

    Definition AppFullFoldArgsOk_SepLogsOk
    : AppFullFoldArgsOk _ (AppFullFoldArgs_SepLogArgs sla).
    Proof.
      refine (
          @Build_AppFullFoldArgsOk _ _ _ _ _
                                   (fun t e res tus tvs =>
                                      t = SL ->
                                      slaok.(R_t) e res tus tvs)
                                   _ _ _ _ _).
      { destruct sla; simpl; intros; subst.
        change (Var v) with (apps (@Var sym v) nil) at 1.
        eapply Hatomic_app. unfold typeof_apps.
        simpl; rewrite H; auto. }
      { destruct sla; simpl; intros; subst.
        change (UVar v) with (apps (@UVar sym v) nil) at 1.
        eapply Hatomic_app. unfold typeof_apps.
        simpl. rewrite H. auto. }
      { destruct sla; simpl; intros; subst.
        change (Inj v) with (apps (@Inj sym v) nil) at 1.
        consider (is_emp v); intros.
        { eapply Hemp; eauto. }
        { eapply Hatomic_app. unfold typeof_apps.
          simpl. rewrite H. auto. } }
      { destruct sla; simpl; intros; subst.
        change (Abs t e) with (apps (Abs t e) nil) at 1.
        eapply Hatomic_app. unfold typeof_apps.
        simpl. rewrite H. auto. }
      { intros. subst ft. subst.
        destruct sla; simpl.
        assert (typeof_apps RSym_sym tus tvs l (map fst rs) = Some SL).
        { rewrite <- typeof_expr_apps. auto. }
        destruct l; try solve [ eapply Hatomic_app; eauto ].
        consider (is_star s); intros.
        { generalize H3. eapply is_starOk in H3. destruct H3.
          unfold typeof_apps in H2.
          simpl in H2. rewrite x in H2.
          destruct rs; simpl in *.
          { rewrite x in H. clear - H. inv_all.
            symmetry in H. eapply tyArr_circ_L in H. intuition. }
          { inversion H1; clear H1; subst.
            inversion H8; clear H8; subst.
            { subst. simpl in *. forward; inv_all; try subst.
              exfalso. eapply tyArr_circ_L; eauto. }
            { subst. inversion H4; clear H4; subst.
              { forward. subst. simpl in *.
                inv_all; subst.
                intuition. inv_all; subst.
                unfold type_of_apply in *.
                rewrite x in *. rewrite H7 in *. rewrite H in *.
                forward. inv_all. clear H13. revert H6 H10. subst.
                intros.
                eapply Hstar; eauto. }
              { intuition. simpl in *.
                rewrite typeof_expr_apps in H.
                unfold typeof_apps in H. simpl in H.
                rewrite H8 in *. rewrite H7 in *. rewrite H1 in *.
                rewrite x in *.
                unfold type_of_apply in *.
                forward; inv_all; subst. inv_all; subst.
                eapply type_of_applys_circle_False in H14. intuition. } } } }
        { eapply Hatomic_app; eauto. } }
    Defined.

    Definition seplog_fold (sla : SepLogArgs) : expr sym -> tenv typ -> tenv typ -> T :=
      app_fold_args (AppFullFoldArgs_SepLogArgs sla).

    Theorem seplog_fold_sound
    : forall e tus tvs result,
        seplog_fold sla e tus tvs = result ->
        typeof_expr tus tvs e = Some SL ->
        slaok.(R_t) e result tus tvs.
    Proof.
      intros.
      eapply app_fold_args_sound in H. 2: eapply H0.
      revert H. instantiate (1 := AppFullFoldArgsOk_SepLogsOk).
      simpl. intuition.
    Qed.
  End sound.
End seplog_fold.
