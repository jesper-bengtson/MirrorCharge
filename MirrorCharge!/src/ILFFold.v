Require Import ILogicFunc.
Require Import MirrorCore.SymI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.AppFull.

Set Implicit Arguments.
Set Strict Implicit.

Section fold.
  Variable ts : types.
  Variable fs : fun_map ts.
  Variable gs : logic_ops ts.
  Variable es : embed_ops ts.

  Variable T' : Type.
  Let T : Type := tenv typ -> tenv typ -> T'.

  Variable do_var : var -> T.
  Variable do_uvar : uvar -> T.
  Variable do_inj : ilfunc -> T.
  Variable do_abs : typ -> expr ilfunc -> T -> T.
  Variable do_app : expr ilfunc -> T ->
                    list (expr ilfunc * T) -> T.
  Variable do_ex : typ -> typ -> expr ilfunc -> T -> T.
  Variable do_all : typ -> typ -> expr ilfunc -> T -> T.

  Fixpoint app_fold (e : expr ilfunc) : T :=
    match e with
      | Var v => do_var v
      | UVar u => do_uvar u
      | Inj i => do_inj i
      | Abs t e =>
        @do_abs t e (app_fold e)
      | App (Inj (ilf_exists t t')) (Abs _ e) =>
        do_ex t t' e (app_fold e)
      | App (Inj (ilf_forall t t')) (Abs _ e) =>
        do_all t t' e (app_fold e)
      | App l r =>
        (fix gather e (ls : list (expr ilfunc * T)) :=
           match e with
             | App a b =>
               gather a ((b, app_fold b) :: ls)
             | e => do_app e (app_fold e) ls
           end) l ((r,app_fold r) :: nil)
    end.

  Local Instance RSym_ilfunc' : RSym (typD ts) ilfunc :=
    RSym_ilfunc fs gs es.

  Variable R_t : typ -> expr ilfunc -> T' -> tenv typ -> tenv typ -> Prop.

  Hypothesis Hvar
  : forall tus tvs v t,
      typeof_expr tus tvs (Var v) = Some t ->
      R_t t (Var v) (do_var v tus tvs) tus tvs.
  Hypothesis Huvar
  : forall tus tvs v t,
      typeof_expr tus tvs (UVar v) = Some t ->
      R_t t (UVar v) (do_uvar v tus tvs) tus tvs.
  Hypothesis Hinj
  : forall tus tvs v t,
      typeof_expr tus tvs (Inj v) = Some t ->
      R_t t (Inj v) (do_inj v tus tvs) tus tvs.
  Hypothesis Habs
  : forall tus tvs t t' e e_res,
      typeof_expr tus tvs (Abs t e) = Some (tyArr t t') ->
      R_t t' e (e_res tus (t :: tvs)) tus (t :: tvs) ->
      R_t (tyArr t t') (Abs t e) (do_abs t e e_res tus tvs) tus tvs.
  Hypothesis Happ
  : forall tus tvs l l_res rs t ts,
      typeof_expr tus tvs (apps l (map fst rs)) = Some t ->
      let ft := fold_right tyArr t ts in
      R_t ft l (l_res tus tvs) tus tvs ->
      Forall2 (fun t x => R_t t (fst x) (snd x tus tvs) tus tvs)
              ts rs ->
      R_t t (apps l (map fst rs)) (do_app l l_res rs tus tvs) tus tvs.
  Hypothesis Hex
  : forall tus tvs t t_logic e e_res,
      typeof_expr tus tvs (App (Inj (ilf_exists t t_logic)) (Abs t e)) = Some t_logic ->
      R_t t_logic e (e_res tus (t :: tvs)) tus (t :: tvs) ->
      R_t t_logic
          (App (Inj (ilf_exists t t_logic)) (Abs t e))
          (do_ex t t_logic e e_res tus tvs) tus tvs.
  Hypothesis Hall
  : forall tus tvs t t_logic e e_res,
      typeof_expr tus tvs (App (Inj (ilf_forall t t_logic)) (Abs t e)) = Some t_logic ->
      R_t t_logic e (e_res tus (t :: tvs)) tus (t :: tvs) ->
      R_t t_logic
          (App (Inj (ilf_forall t t_logic)) (Abs t e))
          (do_all t t_logic e e_res tus tvs) tus tvs.

  Require Import ExtLib.Tactics.

  Lemma app_fold_sound_do_app
  : forall e,
    forall e2 tus tvs (t : typ),
      match typeof_expr tus tvs e with
        | Some tf =>
          match typeof_expr tus tvs e2 with
            | Some tx => type_of_apply tf tx
            | None => None
          end
        | None => None
      end = Some t ->
      (forall y : expr ilfunc,
         SolveTypeClass
           (TransitiveClosure.rightTrans (expr_acc (func:=ilfunc)) y (App e e2)) ->
         forall (tus0 tvs0 : tenv typ) (t0 : typ) (result : T'),
           app_fold y tus0 tvs0 = result ->
           typeof_expr tus0 tvs0 y = Some t0 -> R_t t0 y result tus0 tvs0) ->
      R_t t (App e e2)
          (do_app e (app_fold e) ((e2, app_fold e2) :: nil) tus tvs) tus tvs.
  Proof.
    intros. unfold type_of_apply in *.
    forward; inv_all; subst.
    assert (Forall2 (fun t x => R_t t (fst x) (snd x tus tvs) tus tvs)
                    (t1 :: nil)
                    ((e2, app_fold e2) :: nil)).
    { constructor; [ simpl | constructor ].
      eapply H0; eauto with typeclass_instances. }
    generalize (H0 e _ tus tvs _ _ eq_refl H2).
    assert (forall y : expr ilfunc,
              SolveTypeClass
                (TransitiveClosure.rightTrans (expr_acc (func:=ilfunc)) y e) ->
              forall (tus tvs : tenv typ) (t : typ) (result : T'),
                app_fold y tus tvs = result ->
                typeof_expr tus tvs y = Some t ->
                R_t t y result tus tvs).
    { clear - H0. intuition.
      eapply H0; eauto.
      eapply TransitiveClosure.RTStep. eauto. constructor. }
    assert (typeof_expr tus tvs (apps e (map fst ((e2, app_fold e2) :: nil))) 
            = Some t).
    { simpl. rewrite H1. rewrite H2. simpl. forward. }
    revert H0 H H3 H4.
    change (App e e2)
    with (apps e (map fst ((e2, app_fold e2) :: nil))).
    change (tyArr t1 t)
    with (fold_right tyArr t (t1 :: nil)).
    generalize ((e2, app_fold e2) :: nil).
    generalize (t1 :: nil).
    clear - Happ. specialize (@Happ tus tvs).
    induction e; simpl; intros; eauto.
  Qed.


  Theorem app_fold_sound
  : forall e tus tvs t result,
      app_fold e tus tvs = result ->
      typeof_expr tus tvs e = Some t ->
      R_t t e result tus tvs.
  Proof.
    refine (expr_strong_ind _ _).
    destruct e; simpl; intros; subst; eauto.
    { destruct e1; eauto using app_fold_sound_do_app.
      { destruct i; eauto using app_fold_sound_do_app.
        { destruct e2; eauto using app_fold_sound_do_app.
          { unfold type_of_apply in *.
            forward; inv_all; subst.
            simpl in *. forward; inv_all; subst.
            inv_all; subst.
            eapply Hex.
            { rewrite H0. rewrite H1. simpl. forward. }
            { eapply H; eauto with typeclass_instances. } } }
        { destruct e2; eauto using app_fold_sound_do_app.
          { unfold type_of_apply in *.
            forward; inv_all; subst.
            simpl in *. forward; inv_all; subst.
            inv_all; subst.
            eapply Hall.
            { rewrite H0. rewrite H1. simpl. forward. }
            { eapply H; eauto with typeclass_instances. } } } }
      { change (
            R_t t (App (App e1_1 e1_2) e2)
                ((fix gather (e : expr ilfunc) (ls : list (expr ilfunc * T)) {struct e} :
                    T :=
                    match e with
                      | Var _ => do_app e (app_fold e) ls
                      | Inj _ => do_app e (app_fold e) ls
                      | App a b => gather a ((b, app_fold b) :: ls)
                      | Abs _ _ => do_app e (app_fold e) ls
                      | UVar _ => do_app e (app_fold e) ls
                    end) (App e1_1 e1_2) ((e2, app_fold e2) :: nil) tus
                         tvs) tus tvs).
        generalize dependent (App e1_1 e1_2). clear e1_1 e1_2.
        intros. unfold type_of_apply in *.
        forward; inv_all; subst.
        assert (Forall2 (fun t x => R_t t (fst x) (snd x tus tvs) tus tvs)
                        (t1 :: nil)
                        ((e2, app_fold e2) :: nil)).
        { constructor; [ simpl | constructor ].
          eapply H; eauto with typeclass_instances. }
        generalize (H e _ tus tvs _ _ eq_refl H2).
        assert (forall y : expr ilfunc,
                  SolveTypeClass
                    (TransitiveClosure.rightTrans (expr_acc (func:=ilfunc)) y e) ->
                  forall (tus tvs : tenv typ) (t : typ) (result : T'),
                    app_fold y tus tvs = result ->
                    typeof_expr tus tvs y = Some t ->
                    R_t t y result tus tvs).
        { clear - H. intuition.
          eapply H; eauto.
          eapply TransitiveClosure.RTStep. eauto. constructor. }
        assert (typeof_expr tus tvs (apps e (map fst ((e2, app_fold e2) :: nil))) 
                = Some t).
        { simpl. rewrite H1. rewrite H2. simpl. forward. }
        revert H0 H H3 H4 H1 H2.
        change (App e e2)
          with (apps e (map fst ((e2, app_fold e2) :: nil))).
        change (tyArr t1 t)
          with (fold_right tyArr t (t1 :: nil)).
        generalize ((e2, app_fold e2) :: nil).
        generalize (t1 :: nil).
        clear - Happ. specialize (@Happ tus tvs).
        Opaque app_fold.
        revert e2 t t1.
        induction e; simpl; intros; eauto.
        { change (apps (App e1 e2) (map fst l0))
            with (apps e1 (map fst ((e2, app_fold e2) :: l0))).
          unfold type_of_apply in *.
          forward; inv_all; subst.
          
          eapply IHe1; eauto with typeclass_instances.
          { intros. eapply H3; eauto with typeclass_instances.
            eapply TransitiveClosure.RTStep. eauto. constructor. } } } }
    { forward; inv_all; subst.
      specialize (H e _ tus (t :: tvs) _ _ eq_refl H0).
      eapply Habs; eauto. simpl. rewrite H0. auto. }
  Qed.
End fold.