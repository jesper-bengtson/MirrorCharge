(** This file implements an interface to [expr] that
 ** makes star, emp, and pure assertions apparent.
 **)
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Tactics.
Require Import BILogic Pure.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.AppFull.

Set Implicit Arguments.
Set Strict Implicit.

Section seplog_fold.
  Variable ts : types.
  Variable sym : Type.
  Variable RSym_sym : RSym (typD ts) sym.

  Variable T : Type.
  Variable SL : typ.

  Record SepLogArgs : Type :=
  { do_other : expr sym -> list (expr sym * T) -> T
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

  Record SepLogSpecOk (sls : SepLogSpec)
         (OPS : ILogic.ILogicOps (typD ts nil SL))
         (BI : BILOperators (typD ts nil SL)) : Type :=
  { _PureOp : @PureOp (typD ts nil SL)
  ; _Pure : @Pure _ OPS BI _PureOp
  ; His_pure : forall e,
                 sls.(is_pure) e = true ->
                 forall us vs val,
                   exprD us vs e SL = Some val ->
                   pure val
  ; His_emp : forall e,
                sls.(is_emp) e = true ->
                forall us vs,
                  exprD us vs (Inj e) SL = Some empSP
  ; His_star : forall e,
                 sls.(is_star) e = true ->
                 forall us vs,
                   exprD us vs (Inj e) (tyArr SL (tyArr SL SL)) = Some sepSP
  }.

  Record SepLogArgsOk (R_t : expr sym -> T -> tenv typ -> tenv typ -> Prop) :=
  { otherOk
    : forall e es tus tvs,
        typeof_apps _ tus tvs e (List.map fst es) = Some SL ->
        (forall x y,
           In (x,y) es ->
           typeof_expr tus tvs x = Some SL ->
           R_t x y tus tvs) ->
        R_t (apps e (List.map fst es)) (sla.(do_other) e es) tus tvs
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

  Definition AppFullFoldArgs_SepLogArgs (sla : SepLogArgs)
  : AppFullFoldArgs sym T :=
    match sla , sls with
      | {| do_other := do_other
         ; do_pure := do_pure
         ; do_star := do_star
         ; do_emp := do_emp |}
      , {| is_pure := is_pure
         ; is_star := is_star
         ; is_emp := is_emp |} =>
        {| do_var := fun v _ _ => do_other (Var v) nil
         ; do_uvar := fun u _ _ => do_other (UVar u) nil
         ; do_inj := fun i _ _ =>
                       if is_emp i then
                         do_emp
                       else
                         do_other (Inj i) nil
         ; do_abs := fun t e _ _ _ => do_other (Abs t e) nil
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
                             do_other f (List.map (fun x => (fst x, snd x tus tvs)) args)
                         | _ =>
                           do_other f (List.map (fun x => (fst x, snd x tus tvs)) args)
                       end
        |}
    end.

  Section sound.
    Context R_t `{slaok : SepLogArgsOk R_t}.

    Lemma atomic_ok
    : forall (tus tvs : tenv typ) e (t : typ),
        typeof_expr tus tvs e = Some t ->
        t = SL ->
        R_t e (sla.(do_other) e nil) tus tvs.
    Proof.
      destruct slaok. simpl; intros. subst.
      change e with (apps e nil) at 1.
      eapply (otherOk0 e nil tus tvs); simpl.
      { unfold typeof_apps. simpl. rewrite H. reflexivity. }
      { intuition. }
    Qed.

    Hypothesis BILOps : BILOperators (typD ts nil SL).
    Hypothesis is_starOk
    : forall i,
        sls.(is_star) i = true ->
        typeof_sym i = Some (tyArr SL (tyArr SL SL)).

    Lemma lem_other
    : forall ts0 t rs tus tvs l_res do_atomic_app0,
        Forall2
          (fun (t0 : typ) (x : expr sym * (tenv typ -> tenv typ -> T)) =>
             typeof_expr tus tvs (fst x) = Some t0 /\
             (t0 = SL -> R_t (fst x) (snd x tus tvs) tus tvs)) ts0 rs ->
        forall e : expr sym,
          typeof_expr tus tvs (apps e (map fst rs)) = Some t ->
          (fold_right tyArr t ts0 = SL -> R_t e (l_res tus tvs) tus tvs) ->
          typeof_apps RSym_sym tus tvs e (map fst rs) = Some SL ->
          (forall (e0 : expr sym) (es : list (expr sym * T)) (tus0 tvs0 : tenv typ),
             typeof_apps RSym_sym tus0 tvs0 e0 (map fst es) = Some SL ->
             (forall (x : expr sym) (y : T),
                In (x, y) es -> typeof_expr tus0 tvs0 x = Some SL -> R_t x y tus0 tvs0) ->
             R_t (apps e0 (map fst es)) (do_atomic_app0 e0 es) tus0 tvs0) ->
          R_t (apps e (map fst rs))
              (do_atomic_app0 e
                              (map
                                 (fun x : expr sym * (tenv typ -> tenv typ -> T) =>
                                    (fst x, snd x tus tvs)) rs)) tus tvs.
    Proof.
      intros.
      specialize (H3 e (map
                          (fun x : expr sym * (tenv typ -> tenv typ -> T) =>
                             (fst x, snd x tus tvs)) rs) tus tvs).
      rewrite map_map in *. simpl in *.
      eapply H3; eauto.
      clear - H. induction H; simpl; intuition.
      inv_all. subst. rewrite H1 in *. inv_all; subst.
      eauto.
    Qed.

    Definition AppFullFoldArgsOk_SepLogsOk
    : AppFullFoldArgsOk _ (AppFullFoldArgs_SepLogArgs sla)
                        (fun t e res tus tvs =>
                           t = SL ->
                           R_t e res tus tvs).
    Proof.
      remember sla as s; destruct s; simpl; remember sls as s; destruct s.
      constructor.
      { simpl; intros.
        replace do_other0 with (sla.(do_other)).
        eapply atomic_ok; eauto. rewrite <- Heqs; reflexivity. }
      { simpl; intros.
        replace do_other0 with (sla.(do_other)).
        eapply atomic_ok; eauto. rewrite <- Heqs; reflexivity. }
      { simpl; intros.
        consider (is_emp0 v); intros.
        { replace do_emp0 with (sla.(do_emp)).
          eapply (@empOk _ slaok); eauto.
          Cases.rewrite_all_goal. auto.
          rewrite <- Heqs0. simpl. auto.
          rewrite <- Heqs. reflexivity. }
        { replace do_other0 with (sla.(do_other)).
          eapply atomic_ok; eauto. rewrite <- Heqs; reflexivity. } }
      { simpl; intros.
        replace do_other0 with (sla.(do_other)).
        eapply atomic_ok; eauto. rewrite <- Heqs; reflexivity. }
      { intros. subst ft. simpl.
        assert (typeof_apps RSym_sym tus tvs l (map fst rs) = Some SL).
        { rewrite <- typeof_expr_apps. congruence. }
        generalize (otherOk slaok). rewrite <- Heqs. simpl.
        destruct l; eauto using lem_other.
        consider (is_star0 s); eauto using lem_other; intros.
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

(*
  Variable OPS : ILogic.ILogicOps (typD ts nil SL).
  Variable BI : BILOperators (typD ts nil SL).
  Variable slsok : SepLogSpecOk sls OPS BI.

  Require Import Relations.
  Require Import ExtLib.Data.HList.

  Record SepLogArgsSemOk
         (TD : T -> forall tus tvs, tenv typ -> tenv typ -> option (typD ts nil SL))
         (R : forall tus tvs,
                relation (hlist (typD ts nil) tus ->
                          hlist (typD ts nil) tvs ->
                          typD ts nil SL)) :=
  { atomic_appOk
    : forall e es tus tvs val,
        exprD' tus tvs (apps e es) SL = Some val ->
        R tus tvs val (TD (sla.(do_other) e es))
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
*)

End seplog_fold.
