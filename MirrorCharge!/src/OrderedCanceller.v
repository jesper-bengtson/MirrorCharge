(** This is a simple cancellation procedure based on
 ** an ordering of the elements on the right hand side.
 **)
Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Subst.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.AppFull.
Require Import MirrorCore.Ext.ExprSem.
Require Import MirrorCore.EnvI.
Require Import ILogic BILogic Pure.
Require Import BILNormalize.
Require Import Iterated.
Require Import SynSepLog.

Set Implicit Arguments.
Set Strict Implicit.

Section ordered_cancel.
  Variable ts : types.
  Variable func : Type.
  Variable RSym_func : RSym (typD ts) func.

  Inductive Conjuncts : Type :=
  | Pure (_ : expr func) (c : Conjuncts)
  | Impure (f : expr func) (xs : list (expr func)) (c : Conjuncts)
  | Emp
  | Tru.

  Variable subst : Type.
  Variable Subst_subst : Subst subst (expr func).
  Hypothesis SubstOk_subst : SubstOk _ Subst_subst.

  Fixpoint findWithRest {T U} (f : T -> option U) (ls acc : list T) {struct ls}
  : option (T * U * list T) :=
    match ls with
      | nil => None
      | l :: ls =>
        match f l with
          | None => findWithRest f ls (l :: acc)
          | Some u => Some (l, u, rev_append acc ls)
        end
    end.

  Theorem findWithRest_spec
  : forall T U f ls acc a s b,
      @findWithRest T U f ls acc = Some (a,s,b) ->
      f a = Some s /\
      exists before after,
        b = before ++ after /\ rev_append acc ls = before ++ a :: after.
  Proof.
    clear. induction ls; simpl; intros; try congruence.
    consider (f a); intros.
    { inv_all; subst. split; auto.
      exists (rev acc). exists ls.
      repeat rewrite rev_append_rev. auto. }
    { eapply IHls in H0. intuition. }
  Qed.

  Variable doUnifySepLog : subst -> expr func -> expr func -> option subst.

  Fixpoint cancel (rhs : Conjuncts) (lhs : conjunctives func)
           (rem : conjunctives func) (s : subst) {struct rhs}
  : conjunctives func * conjunctives func * subst :=
    match rhs with
      | Emp => (lhs, rem, s)
      | Tru => (lhs, {| spatial := rem.(spatial)
                      ; pure := rem.(pure)
                      ; star_true := true
                      |}, s)
      | Pure p cs =>
        cancel cs lhs {| spatial := rem.(spatial)
                       ; star_true := rem.(star_true)
                       ; pure := p :: rem.(pure)
                       |} s
      | Impure f xs cs =>
        let Z := apps f xs in
        let test x := doUnifySepLog s Z (apps (fst x) (snd x)) in
        match findWithRest test lhs.(spatial) nil with
          | None =>
            cancel cs lhs {| spatial := (f,xs) :: rem.(spatial)
                           ; star_true := rem.(star_true)
                           ; pure := rem.(pure)
                           |} s
          | Some (_, s', rst) =>
            cancel cs {| spatial := rst
                       ; star_true := lhs.(star_true)
                       ; pure := lhs.(pure)
                       |}
                      rem s'
        end
    end.

  Variable tySL : typ.
  Variable ILogicOps_SL : ILogicOps (typD ts nil tySL).
  Variable BILOperators_SL : BILOperators (typD ts nil tySL).
  Hypothesis ILogic_SL : @ILogic _ ILogicOps_SL.
  Hypothesis BILogic_SL : @BILogic _ ILogicOps_SL BILOperators_SL.

  Variable us vs : EnvI.env (typD ts).

  (** TODO: this can be generalized to handle entailment with a remainder **)
  Hypothesis doUnifySepLogOk : forall s e e' s',
    doUnifySepLog s e e' = Some s' ->
    WellTyped_expr (typeof_env us) (typeof_env vs) e tySL ->
    WellTyped_expr (typeof_env us) (typeof_env vs) e' tySL ->
    WellTyped_subst (typeof_env us) (typeof_env vs) s ->
    substD us vs s' ->
    exprD us vs e tySL = exprD us vs e' tySL /\
    substD us vs s.


  Variable SSL : SynSepLog func.
  Variable SSLO : SynSepLogOk _ _ _ _ SSL.

  Fixpoint ConjunctsD (ls : Conjuncts) : option (typD ts nil tySL) :=
    match ls with
      | Emp => Some empSP
      | Tru => Some ltrue
      | Pure p ls =>
        match exprD us vs p tySL , ConjunctsD ls with
          | Some a , Some b => Some (sepSP (land a empSP) b)
          | _ , _ => None
        end
      | Impure f xs ls =>
        match exprD us vs (apps f xs) tySL , ConjunctsD ls with
          | Some a , Some b => Some (sepSP a b)
          | _ , _ => None
        end
    end.

  Variable PureOp_SL : @Pure.PureOp (typD ts nil tySL).
  Variable Pure_SL : Pure.Pure PureOp_SL.
  Hypothesis Pure_ltrue : Pure.pure ltrue.
  Hypothesis Pure_land : forall a b, Pure.pure a -> Pure.pure b -> Pure.pure (a //\\ b).

  Section well_formed_Conjuncts.
    Variable us' vs' : EnvI.env (typD ts).

    Fixpoint well_formed_Conjuncts (ls : Conjuncts) : Prop :=
      match ls with
        | Emp => True
        | Tru => True
        | Pure p ls =>
          match exprD us' vs' p tySL with
            | None => False
            | Some p => Pure.pure p
          end /\ well_formed_Conjuncts ls
        | Impure _ _ ls => well_formed_Conjuncts ls
      end.
  End well_formed_Conjuncts.

  Fixpoint Conjuncts_to_expr (ls : Conjuncts) : expr func :=
    match ls with
      | Emp => SSL.(e_emp)
      | Tru => SSL.(e_true)
      | Pure p ls =>
        SSL.(e_star) (SSL.(e_and) p SSL.(e_emp)) (Conjuncts_to_expr ls)
      | Impure f xs ls =>
        SSL.(e_star) (apps f xs) (Conjuncts_to_expr ls)
    end.

  Definition sentails : env (typD ts) -> env (typD ts) -> expr func -> expr func -> Prop :=
    @Sem_equiv ts func _ tySL lentails.

  Lemma exprD'_iterated_base_cons_Some
  : forall us tvs a b x,
      exprD' us tvs (iterated_base SSL.(e_emp) SSL.(e_star) (a :: b)) tySL = Some x ->
      exists aV bV,
        exprD' us tvs a tySL = Some aV /\
        exprD' us tvs (iterated_base SSL.(e_emp) SSL.(e_star) b) tySL = Some bV /\
        (forall vs, ((x vs) -|- sepSP (aV vs) (bV vs))).
  Proof.
    clear Pure_SL PureOp_SL Pure_ltrue Pure_land.
    unfold iterated_base. simpl.
    intros.
    destruct (iterated (e_star SSL) b).
    { go_crazy SSL SSLO; eauto. }
    { exists x.
      destruct (SSLO.(e_empOk) us0 tvs) as [ ? [ ? ? ] ].
      eexists x0. split; auto. split; auto. intros.
      rewrite H1. rewrite empSPR; eauto. }
  Qed.

  Lemma exprD'_iterated_base_cons_None
  : forall us tvs a b,
      exprD' us tvs (iterated_base SSL.(e_emp) SSL.(e_star) (a :: b)) tySL = None <->
      exprD' us tvs a tySL = None \/
      exprD' us tvs (iterated_base SSL.(e_emp) SSL.(e_star) b) tySL = None.
  Proof.
    clear Pure_SL PureOp_SL Pure_ltrue Pure_land.
    unfold iterated_base. simpl.
    intros.
    destruct (iterated (e_star SSL) b); auto.
    { split; intros; repeat (go_crazy SSL SSLO); auto.
      consider (exprD' us0 tvs (e_star SSL a e) tySL); intros; auto.
      exfalso. go_crazy SSL SSLO. destruct H; congruence. }
    { split; intros; repeat (go_crazy SSL SSLO); auto.
      destruct H; auto.
      exfalso.
      destruct (SSLO.(e_empOk) us0 tvs). intuition. congruence. }
  Qed.

  Lemma exprD'_iterated_base_app_Some
  : forall us tvs a b x,
      exprD' us tvs (iterated_base SSL.(e_emp) SSL.(e_star) (a ++ b)) tySL = Some x ->
      exists aV bV,
        exprD' us tvs (iterated_base SSL.(e_emp) SSL.(e_star) a) tySL = Some aV /\
        exprD' us tvs (iterated_base SSL.(e_emp) SSL.(e_star) b) tySL = Some bV /\
        (forall vs, ((x vs) -|- sepSP (aV vs) (bV vs))).
  Proof.
    clear Pure_SL PureOp_SL doUnifySepLogOk Pure_ltrue Pure_land.
    induction a; simpl; intros.
    { destruct (SSLO.(e_empOk) us0 tvs) as [ ? [ ? ? ] ].
      exists x0. exists x.
      split; eauto. split; eauto.
      intros. rewrite H1. rewrite empSPL. reflexivity. }
    { eapply exprD'_iterated_base_cons_Some in H.
      destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ].
      specialize (IHa _ _ H0).
      destruct IHa as [ ? [ ? [ ? [ ? ? ] ] ] ].
      consider (exprD' us0 tvs (iterated_base (e_emp SSL) (e_star SSL) (a :: a0)) tySL); intros.
      { do 2 eexists. split; eauto. split; eauto.
        apply exprD'_iterated_base_cons_Some in H5.
        destruct H5 as [ ? [ ? [ ? [ ? ? ] ] ] ].
        intros. Cases.rewrite_all_goal.
        rewrite H in *. rewrite H6 in *.
        inv_all; subst.
        rewrite sepSPA. reflexivity. }
      { exfalso.
        eapply exprD'_iterated_base_cons_None in H5.
        destruct H5; congruence. } }
  Qed.

  Lemma exprD'_iterated_base_app_None
  : forall us tvs a b,
      exprD' us tvs (iterated_base SSL.(e_emp) SSL.(e_star) (a ++ b)) tySL = None <->
      exprD' us tvs (iterated_base SSL.(e_emp) SSL.(e_star) a) tySL = None \/
      exprD' us tvs (iterated_base SSL.(e_emp) SSL.(e_star) b) tySL = None.
  Proof.
    clear Pure_SL PureOp_SL doUnifySepLogOk Pure_ltrue Pure_land.
    induction a; simpl; intros.
    { intuition.
      unfold iterated_base in H0. simpl in *.
      destruct (SSLO.(e_empOk) us0 tvs) as [ ? [ ? ? ] ].
      congruence. }
    { repeat rewrite exprD'_iterated_base_cons_None.
      rewrite IHa. split; tauto. }
  Qed.

  Lemma cancelOk_lem'
  : forall us tvs rhs lhs rem s lhs' rhs' s',
      cancel rhs lhs rem s = (lhs',rhs',s') ->
      match
          exprD' us tvs (conjunctives_to_expr_star SSL lhs) tySL
        , exprD' us tvs (SSL.(e_star) (conjunctives_to_expr_star SSL rem)
                                      (Conjuncts_to_expr rhs)) tySL
      with
        | Some l , Some r =>
          match
              exprD' us tvs (conjunctives_to_expr_star SSL lhs') tySL
            , exprD' us tvs (conjunctives_to_expr_star SSL rhs') tySL
          with
            | Some l' , Some r' =>
              forall vs,
                well_formed _ _ _ lhs us (join_env vs) ->
                well_formed_Conjuncts us (join_env vs) rhs ->
                well_formed _ _ _ rem us (join_env vs) ->
                   well_formed _ _ _ lhs' us (join_env vs)
                /\ well_formed _ _ _ rhs' us (join_env vs)
                /\ (substD us (join_env vs) s' ->
                    (l' vs |-- r' vs) ->
                    (l vs |-- r vs) /\ substD us (join_env vs) s)
            | _ , _ => False
          end
        | _ , _ => True
      end.
  Proof.
    induction rhs; intros; forward.
    { repeat go_crazy SSL SSLO.
      admit. }
    { repeat go_crazy SSL SSLO.
      simpl in H.
      consider (findWithRest
          (fun x : expr func * list (expr func) =>
           doUnifySepLog s (apps f xs) (apps (fst x) (snd x)))
          (spatial lhs) nil); intros.
      { destruct p. destruct p.
        eapply IHrhs in H4; clear IHrhs.
        consider (exprD' us0 tvs
           (conjunctives_to_expr_star SSL
              {|
              spatial := l;
              star_true := star_true lhs;
              pure := pure lhs |}) tySL); intros.
        { consider (exprD' us0 tvs
           (e_star SSL (conjunctives_to_expr_star SSL rem)
              (Conjuncts_to_expr rhs)) tySL); intros.
          { forward. repeat go_crazy SSL SSLO.
            inv_all; subst.
            admit. }
          { exfalso. simpl in H2.
            repeat (go_crazy SSL SSLO; try congruence). } }
        { exfalso.
          simpl in *. admit. } }
      { eapply IHrhs in H4; clear IHrhs. clear H.
        unfold conjunctives_to_expr_star in *; simpl in *.
        progress forward.
        inv_all; subst.
        generalize dependent (e_star SSL
                         (iterated_base (e_emp SSL) 
                            (e_star SSL)
                            (map
                               (fun x : expr func * list (expr func) =>
                                apps (fst x) (snd x)) 
                               (spatial rhs')))
                         (if star_true rhs' then e_true SSL else e_emp SSL)).
        generalize dependent (e_star SSL
             (iterated_base (e_emp SSL) (e_star SSL)
                (map
                   (fun x1 : expr func * list (expr func) =>
                    apps (fst x1) (snd x1)) (spatial lhs')))
             (if star_true lhs' then e_true SSL else e_emp SSL)).
        intros.
        repeat go_crazy SSL SSLO.
        consider (exprD' us0 tvs
           (e_star SSL
              (e_star SSL
                 (iterated_base (e_emp SSL) (e_star SSL)
                    (map (e_and SSL (e_emp SSL)) (pure rem)))
                 (e_star SSL
                    (iterated_base (e_emp SSL) (e_star SSL)
                       (apps f xs
                        :: map
                             (fun x : expr func * list (expr func) =>
                              apps (fst x) (snd x)) 
                             (spatial rem)))
                    (if star_true rem then e_true SSL else e_emp SSL)))
              (Conjuncts_to_expr rhs)) tySL); intros.
        { forward. admit. }
        { exfalso.
          repeat go_crazy SSL SSLO.
          eapply exprD'_iterated_base_cons_None in H4.
          destruct H4; congruence. } } }
    { simpl in H. inv_all; subst.
      simpl in *.
      destruct (SSLO.(e_empOk) us0 tvs) as [ ? [ ? ? ] ].
      repeat go_crazy SSL SSLO.
      inv_all; subst.
      intros.
      split; auto. split; auto. intros. split; auto.
      rewrite H8.
      rewrite H4. rewrite H2.
      rewrite empSPR; eauto. }
    { simpl in H. inv_all; subst.
      simpl in *.
      destruct (SSLO.(e_empOk) us0 tvs) as [ ? [ ? ? ] ].
      repeat go_crazy SSL SSLO.
      unfold conjunctives_to_expr_star. simpl.
      unfold conjunctives_to_expr_star in H1.
      generalize dependent (iterated_base (e_emp SSL) (e_star SSL)
               (map (e_and SSL (e_emp SSL)) (pure rem))).
      generalize dependent (iterated_base (e_emp SSL) (e_star SSL)
                (map
                   (fun x2 : expr func * list (expr func) =>
                    apps (fst x2) (snd x2)) (spatial rem))).
      intros.
      repeat go_crazy SSL SSLO.
      consider (exprD' us0 tvs (e_star SSL e0 (e_star SSL e (e_true SSL))) tySL); intros.
      { split; auto. split; auto.
        intros; split; auto.
        rewrite H14; clear H14.
        repeat go_crazy SSL SSLO.
        inv_all; subst.
        rewrite H4; clear H4.
        rewrite H6; clear H6.
        rewrite H15; clear H15.
        rewrite H17; clear H17.
        rewrite H8; clear H8.
        destruct (SSLO.(e_trueOk) us0 tvs) as [ ? [ ? ? ] ].
        rewrite H3 in *. inv_all; subst.
        rewrite H6.
        destruct (star_true rem); rewrite H7 in *; inv_all; subst.
        { rewrite H6.
          repeat rewrite sepSPA.
          rewrite ltrue_sep; eauto. reflexivity. }
        { rewrite H2. rewrite empSPR; eauto.
          rewrite sepSPA; eauto. reflexivity. } }
      { repeat (go_crazy SSL SSLO; try congruence). } }
  Qed.

(*
  Lemma cancelOk_lem
  : forall rhs lhs rem s lhs' rhs' s',
      cancel rhs lhs rem s = (lhs',rhs',s') ->
      well_formed _ _ _ lhs us vs ->
      well_formed_Conjuncts rhs ->
      well_formed _ _ _ rem us vs ->
      substD us vs s' ->
      match exprD us vs (conjunctives_to_expr_star SSL lhs') tySL
          , exprD us vs (conjunctives_to_expr_star SSL rhs') tySL
      with
        | Some l , Some r =>
          l |-- r
        | _ , _ => True
      end ->
      match exprD us vs (conjunctives_to_expr_star SSL lhs) tySL
          , exprD us vs (SSL.(e_star) (conjunctives_to_expr_star SSL rem)
                                      (Conjuncts_to_expr rhs)) tySL
      with
        | Some l , Some r =>
             l |-- r
          /\ well_formed _ _ _ lhs' us vs
          /\ well_formed _ _ _ rhs' us vs
          /\ substD us vs s
        | _ , _ => True
      end.
  Proof.
  (*
    unfold sentails.
    induction rhs; intros.
    { simpl in H.
      specialize (IHrhs _ _ _ _ _ _ H H0).
      simpl in H1. forward. destruct H5.
      (** TODO: this is about provability and it isn't implemented yet **)
      admit. }
    { simpl in H.
      match goal with
        | _ : match ?X with _ => _ end = _ |- _ =>
          consider X
      end; intros.
      { destruct p. destruct p.
        forward.
        red in H3. unfold Sem_equiv, exprD in *.
        destruct (split_env vs).
        forward. inv_all; subst. simpl in *.
        repeat (go_crazy SSL SSLO).
        assert (well_formed RSym_func tySL PureOp_SL
            {| spatial := l; star_true := star_true lhs; pure := pure lhs |}
            us vs).
        { destruct lhs. simpl in *. auto. }
        assert (well_formed_Conjuncts rhs).
        { simpl in *; auto. }
        assert (well_formed RSym_func tySL PureOp_SL rem us vs) by auto.
        admit. (*
        specialize (IHrhs _ _ _ _ _ _ H5 H12 H13 H14); clear H11 H12 H13 H3 H4.
        repeat go_crazy SSL SSLO.
        inv_all; subst.
        eapply findWithRest_spec in H.
        destruct H. destruct H3 as [ ? [ ? [ ? ? ] ] ].
        simpl in *. subst.
        unfold conjunctives_to_expr_star in *.
        repeat (go_crazy SSL SSLO).
        rewrite H11 in *.
        rewrite map_app in H16.
        apply exprD'_iterated_base_app_Some in H16.
        simpl in *.
        repeat match goal with
                 | H : _ /\ _ |- _ => destruct H
                 | H : exists x, _ |- _ => destruct H
               end.
        eapply exprD'_iterated_base_cons_Some in H20.
        repeat match goal with
                 | H : _ /\ _ |- _ => destruct H
                 | H : exists x, _ |- _ => destruct H
               end.
        consider (exprD' us x
                (e_star SSL
                   (iterated_base (e_emp SSL) (e_star SSL)
                      (map (e_and SSL (e_emp SSL)) (pure lhs)))
                   (e_star SSL
                      (iterated_base (e_emp SSL) (e_star SSL)
                         (map
                            (fun x : expr func * list (expr func) =>
                             apps (fst x) (snd x))
                            (x0 ++ x3)))
                      (if star_true lhs then e_true SSL else e_emp SSL)))
                tySL).
        { intros. clear H11.
          repeat go_crazy SSL SSLO.
          inv_all; subst.
          rewrite map_app in H24.
          eapply exprD'_iterated_base_app_Some in H24.
          destruct H24 as [ ? [ ? [ ? [ ? ? ] ] ] ].
          repeat go_crazy SSL SSLO.
          inv_all; subst.
          Cases.rewrite_all_goal.
          assert (x17 h ** (x19 h ** x11 h ** x14 h ** x22 h) |--
                  x2 h ** (x7 h ** x9 h ** x10 h ** x6 h)).
          { apply scME.
            { eapply doUnifySepLogOk in H.
              { rewrite H7 in *.
                rewrite H20 in *.
                destruct H.
                inv_all; subst.
                rewrite H. reflexivity. }
              { admit. }
              { admit. }
              { admit. }
              { 
 }
            { etransitivity. etransitivity.
              2: eapply IHrhs.
              clear IHrhs. Cases.rewrite_all_goal.
              repeat rewrite sepSPA. reflexivity.
              clear IHrhs. Cases.rewrite_all_goal.
              repeat rewrite sepSPA. reflexivity. } }
          { etransitivity. etransitivity. 2: eapply H11.
            repeat rewrite <- sepSPA.
            { apply scME; try reflexivity.
              apply scME; try reflexivity.
              rewrite sepSPC. rewrite sepSPA. reflexivity. }
            { repeat rewrite <- sepSPA.
              apply scME; try reflexivity.
              rewrite sepSPC with (Q := x2 h).
              repeat rewrite sepSPA.
              reflexivity. } } }
        { intros.
          clear H25.
          repeat go_crazy SSL SSLO.
          rewrite map_app in H24.
          apply exprD'_iterated_base_app_None in H24.
          destruct H24; congruence. } *) }
      { (** findWithRest returns None **)
        unfold Sem_equiv in *.
        forward.
        assert (well_formed RSym_func tySL PureOp_SL lhs us vs) by auto.
        assert (well_formed_Conjuncts rhs) by auto.
        assert (well_formed RSym_func tySL PureOp_SL
                            {|
                              spatial := spatial rem;
                              star_true := star_true rem;
                              pure := pure rem |} us vs) by auto.
        specialize (IHrhs _ _ _ _ _ _ H5 H8 H9 H10); clear H5 H8 H9 H10.
        admit. (*
        rewrite H5 in *. simpl in *. clear H.
        consider (exprD us vs
              (e_star SSL
                 (conjunctives_to_expr_star SSL
                    {|
                    spatial := (f,xs) :: spatial rem;
                    star_true := star_true rem;
                    pure := pure rem |}) (Conjuncts_to_expr rhs)) tySL); intros.
        { rewrite IHrhs; clear IHrhs H5 t.
          unfold conjunctives_to_expr_star in *; simpl in *.
          unfold exprD in *.
          destruct (split_env vs).
          forward.
          inv_all; subst.
          destruct rem; simpl in *.
          repeat go_crazy SSL SSLO.
          inv_all; subst.
          apply exprD'_iterated_base_cons_Some in H14.
          destruct H14 as [ ? [ ? [ ? [ ? ? ] ] ] ].
          rewrite H6 in *. rewrite H3 in *.
          inv_all; subst.
          Cases.rewrite_all_goal.
          repeat rewrite <- sepSPA.
          apply scME; try reflexivity.
          repeat rewrite sepSPA.
          apply scME; try reflexivity.
          rewrite sepSPC. rewrite sepSPA.
          reflexivity. }
        { clear H3.
          unfold conjunctives_to_expr_star in *. simpl in *.
          unfold exprD in *.
          destruct (split_env vs). forward.
          inv_all; subst.
          repeat (go_crazy SSL SSLO; try congruence).
          eapply exprD'_iterated_base_cons_None in H.
          destruct H; congruence. } *) } }
    { simpl in *.
      inv_all; subst.
      forward.
      red in H4.
      unfold exprD in *.
      destruct (split_env vs).
      forward. inv_all; subst.
      destruct (SSLO.(e_empOk) us x) as [ ? [ ? ? ] ].
      repeat go_crazy SSL SSLO.
      inv_all; subst.
      Cases.rewrite_all_goal.
      rewrite empSPR by eauto with typeclass_instances.
      reflexivity. }
    { simpl in *.
      inv_all; subst.
      red in H4. unfold exprD in *. forward.
      inv_all; subst.
      destruct (SSLO.(e_trueOk) us x) as [ ? [ ? ? ] ].
      repeat go_crazy SSL SSLO.
      inv_all; subst.
      rewrite H5; clear H5 H4.
      destruct rem.
      unfold conjunctives_to_expr_star in *. simpl in *.
      repeat go_crazy SSL SSLO.
      inv_all; subst.
      Cases.rewrite_all_goal.
      repeat rewrite sepSPA.
      apply scME; try reflexivity.
      apply scME; try reflexivity.
      destruct star_true.
      { rewrite H9 in *. inv_all; subst.
        Cases.rewrite_all.
        eapply ltrue_sep; eauto with typeclass_instances. }
      { destruct (SSLO.(e_empOk) us x).
        rewrite H9 in *.
        destruct H4.
        inv_all; subst.
        rewrite H5. rewrite empSPL. apply ltrueR. } }
  Qed.
*)
  Admitted.
*)

  Variable order : conjunctives func -> Conjuncts.
  Hypothesis orderOk
  : forall c us tvs,
      match exprD' us tvs (conjunctives_to_expr_star SSL c) tySL
          , exprD' us tvs (Conjuncts_to_expr (order c)) tySL
      with
        | Some l , Some r =>
          forall vs,
            well_formed _ _ _ c us (join_env vs) ->
            ((l vs -|- r vs) /\
             well_formed_Conjuncts us (join_env vs) (order c))
        | None , None => True
        | _ , _ => False
      end.

  Definition ordered_cancel (lhs rhs : conjunctives func) (s : subst)
  : conjunctives func * conjunctives func * subst :=
    let ordered := order rhs in
    let empty := {| spatial := nil ; pure := nil ; star_true := false |} in
    cancel ordered lhs empty s.

  Theorem ordered_cancelOk
  : forall us tvs lhs rhs s lhs' rhs' s',
      ordered_cancel lhs rhs s = (lhs', rhs', s') ->
      match
          exprD' us tvs (conjunctives_to_expr SSL lhs) tySL
        , exprD' us tvs (conjunctives_to_expr SSL rhs) tySL
      with
        | Some l , Some r =>
          match
              exprD' us tvs (conjunctives_to_expr SSL lhs') tySL
            , exprD' us tvs (conjunctives_to_expr SSL rhs') tySL
          with
            | Some l' , Some r' =>
              forall vs', let vs := join_env vs' in
              
              well_formed _ _ _ lhs us vs ->
              well_formed _ _ _ rhs us vs ->
              substD us vs s' ->
                  well_formed _ _ _ lhs' us vs
               /\ well_formed _ _ _ rhs' us vs
               /\ ((l' vs' |-- r' vs') -> l vs' |-- r vs')
            | _ , _ => False
          end
        | _ , _ => True
      end.
  Proof.
    intros.
    unfold ordered_cancel in H.
    eapply cancelOk_lem' with (us := us0) (tvs := tvs) in H.
    forward.
    generalize (@conjunctives_to_expr_conjunctives_to_expr_star_iff _ _ _ _ _ SSL _ tvs us0 lhs).
    generalize (@conjunctives_to_expr_conjunctives_to_expr_star_iff _ _ _ _ _ SSL _ tvs us0 rhs).
    rewrite H0. rewrite H1.
    specialize (orderOk rhs us0 tvs).
    intros; forward.
    match type of H3 with
      | match ?X with _ => _ end =>
        consider X; intros
    end.
    { forward.
      unfold conjunctives_to_expr_star in H3; simpl in H3.
      unfold iterated_base in H3; simpl in H3.
      repeat go_crazy SSL SSLO.
      inv_all; subst.
      generalize (@conjunctives_to_expr_conjunctives_to_expr_star_iff _ _ _ _ _ SSL _ tvs us0 lhs').
      generalize (@conjunctives_to_expr_conjunctives_to_expr_star_iff _ _ _ _ _ SSL _ tvs us0 rhs').
      Cases.rewrite_all_goal.
      intros; forward.
      destruct (orderOk _ H18); clear orderOk.
      assert (well_formed RSym_func tySL PureOp_SL
         {| spatial := nil; star_true := false; pure := nil |} us0
         (join_env vs')) by constructor.
      specialize (H9 _ H17 H21 H22).
      destruct H9 as [ ? [ ? ? ] ].
      split; auto.
      split; auto.
      intro.
      assert (t5 vs' |-- t6 vs').
      { clear H24.
        rewrite <- H14 by auto; clear H14.
        rewrite <- H16 by auto; clear H16.
        assumption. }
      specialize (H24 H19 H26).
      rewrite H5 by auto; clear H5.
      rewrite H4 by auto; clear H4.
      rewrite H20; clear H20.
      destruct H24.
      rewrite H4; clear H4.
      rewrite H11; clear H11.
      rewrite H13; clear H13.
      rewrite H15; clear H15.
      destruct (SSLO.(e_empOk) us0 tvs) as [ ? [ ? ? ] ].
      rewrite H4 in *. inv_all; subst.
      repeat rewrite H11.
      repeat rewrite empSPL. reflexivity. }
    { exfalso.
      unfold conjunctives_to_expr_star in H3; simpl in H3.
      unfold iterated_base in H3; simpl in H3.
      destruct (SSLO.(e_empOk) us0 tvs).
      destruct (SSLO.(e_trueOk) us0 tvs).
      destruct H7; destruct H8.
      repeat (go_crazy SSL SSLO; try congruence). }
  Qed.

End ordered_cancel.

(** The simplest ordering heuristic just uses the order that they occur in the
 ** map without looking at unification variables.
 **)
Section simple_ordering.
  Variable ts : types.
  Variable func : Type.
  Variable RSym_func : RSym (typD ts) func.

  Variable tySL : typ.
  Variable ILogicOps_SL : ILogicOps (typD ts nil tySL).
  Variable BILOperators_SL : BILOperators (typD ts nil tySL).
  Hypothesis ILogic_SL : @ILogic _ ILogicOps_SL.
  Hypothesis BILogic_SL : @BILogic _ ILogicOps_SL BILOperators_SL.



  Definition simple_order (c : conjunctives func) : Conjuncts func :=
    List.fold_right (fun x acc => Impure (fst x) (snd x) acc)
                    (List.fold_right (fun x acc => Pure x acc)
                                     (if c.(star_true) then Tru _ else Emp _)
                                     c.(pure))
                    c.(spatial).

  Variable SSL : SynSepLog func.
  Variable SSLO : SynSepLogOk _ _ _ _ SSL.

  Variable PureOp_SL : @Pure.PureOp (typD ts nil tySL).
  Variable Pure_SL : Pure.Pure PureOp_SL.
  Hypothesis Pure_ltrue : Pure.pure ltrue.
  Hypothesis Pure_land : forall a b, Pure.pure a -> Pure.pure b -> Pure.pure (a //\\ b).


  Theorem simple_orderOk
  : forall c us tvs,
      match exprD' us tvs (conjunctives_to_expr_star SSL c) tySL
          , exprD' us tvs (Conjuncts_to_expr SSL (simple_order c)) tySL
      with
        | Some l , Some r =>
          forall vs,
            well_formed _ _ _ c us (join_env vs) ->
            ((l vs -|- r vs) /\
             well_formed_Conjuncts _ tySL _ us (join_env vs) (simple_order c))
        | None , None => True
        | _ , _ => False
      end.
  Proof.
    intros; destruct c; simpl.
    unfold conjunctives_to_expr_star, simple_order; simpl.
    match goal with
      | |- match ?X with _ => _ end =>
        consider X; intros
    end.
    { admit. }
    { forward.
(*      repeat go_crazy SSL SSLO. *)
      admit. }
  Qed.


End simple_ordering.
