(** This file implements normalization for separation lgoic formulas.
 ** The normal form is:
 **   (a /\ b /\ c) /\ (P * Q * R [* true]?)
 ** The final [* true] is optional and is likely to never occur in
 ** practice but is necessary to make the algorithm total.
 **
 ** In this format, all of [a], [b], and [c] are pure which means that
 ** the above equation is equivalent to:
 **  Inj a * Inj b * Inj c * P * Q * R [* true]?
 ** where [Inj p = p /\ emp]
 **)
Require Import Morphisms.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import BILogic ILogic Pure.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.AppFull.
Require Import Iterated.
Require Import ILogicFunc SepLogFold.
Require Import SynSepLog.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO: These should really be moved to Charge! **)
Section lemmas.
  Variable P : Type.
  Variable ILogicOps_P : ILogicOps P.
  Variable ILogic_P : ILogic P.
  Variable BILOperators_P : BILOperators P.
  Variable BILogic_P : BILogic P.
  Variable PureOp_P : @PureOp P.
  Variable Pure_P : Pure PureOp_P.

  Lemma ltrue_sep : pure ltrue -> ltrue ** ltrue -|- ltrue.
  Proof.
    constructor.
    { apply ltrueR. }
    { rewrite <- pureandsc by eauto with typeclass_instances.
      apply landR; reflexivity. }
  Qed.

  Lemma pure_star_and_true
  : forall a b,
      Pure.pure a ->
      a ** b -|- a //\\ b ** ltrue.
  Proof.
    intros.
    rewrite <- (landtrueR a) at 1.
    rewrite pureandscD by eauto with typeclass_instances.
    rewrite sepSPC. reflexivity.
  Qed.

  Lemma lequiv_sep_cancel : forall a b c,
                              a -|- b -> a ** c -|- b ** c.
  Proof.
    split; apply bilsep; eapply H.
  Qed.

  Lemma land_cancel : forall a b c, b -|- c -> a //\\ b -|- a //\\ c.
  Proof.
    intros. rewrite H. reflexivity.
  Qed.
End lemmas.

Section cancel_state.
  Variable ts : types.
  Variable sym : Type.
  Variable RSym_sym : RSym (typD ts) sym.

  Record conjunctives : Type :=
  { spatial : list (expr sym * list (expr sym))
  ; star_true : bool
  ; pure : list (expr sym)
  }.

  Definition mkEmpty : conjunctives :=
  {| spatial := nil
   ; star_true := false
   ; pure := nil
   |}.

  Definition mkPure e : conjunctives :=
  {| spatial := nil
   ; star_true := true
   ; pure := e :: nil
   |}.

  Definition mkSpatial e es : conjunctives :=
  {| spatial := (e,es) :: nil
   ; star_true := false
   ; pure := nil
   |}.

  Definition mkStar (l r : conjunctives) : conjunctives :=
  {| spatial := l.(spatial) ++ r.(spatial)
   ; star_true := orb l.(star_true) r.(star_true)
   ; pure := l.(pure) ++ r.(pure)
   |}.


  Definition SepLogArgs_normalize : SepLogArgs sym conjunctives :=
  {| do_emp := mkEmpty
   ; do_star := mkStar
   ; do_other := fun f xs => mkSpatial f (List.map fst xs)
   ; do_pure := mkPure
   |}.

  Variable SL : typ.

  Section conjunctivesD.
    Variable ILO : ILogicOps (typD ts nil SL).
    Variable BILO : BILOperators (typD ts nil SL).
    Variable IL : @ILogic _ ILO.
    Variable BIL : @BILogic _ ILO BILO.

    Definition well_formed (PO : PureOp)
               (c : conjunctives) (us vs : env (typD ts)) : Prop :=
      List.Forall (fun e =>
                     exists val, exprD us vs e SL = Some val
                              /\ @Pure.pure _ PO val) c.(pure).


    Variable SSL : SynSepLog sym.
    Variable SSLO : @SynSepLogOk ts sym _ SL _ _ SSL.


    Definition conjunctives_to_expr (c : conjunctives) : expr sym :=
      let spa := iterated_base SSL.(e_emp) SSL.(e_star) (map (fun x => apps (fst x) (snd x)) c.(spatial)) in
      let pur := iterated_base SSL.(e_true) SSL.(e_and) c.(pure) in
      SSL.(e_and) pur (SSL.(e_star) spa (if c.(star_true) then SSL.(e_true) else SSL.(e_emp))).

    Definition conjunctives_to_expr_star (c : conjunctives) : expr sym :=
      let spa := iterated_base SSL.(e_emp) SSL.(e_star) (map (fun x => apps (fst x) (snd x)) c.(spatial)) in
      let pur := iterated_base SSL.(e_emp) SSL.(e_star) (map (SSL.(e_and) SSL.(e_emp)) c.(pure)) in
      SSL.(e_star) pur (SSL.(e_star) spa (if c.(star_true) then SSL.(e_true) else SSL.(e_emp))).

    Require Import MirrorCore.Ext.ExprSem.

    Theorem conjunctives_to_expr_conjunctives_to_expr_star
    : forall (PO : PureOp) (P : Pure PO) vs us c,
        well_formed PO c us vs ->
        Sem_equiv _ SL lequiv us vs
                  (conjunctives_to_expr c)
                  (conjunctives_to_expr_star c).
    Proof.
      unfold well_formed, conjunctives_to_expr, conjunctives_to_expr_star, Sem_equiv.
      destruct c; simpl.
      intros.
      generalize (e_star SSL
           (iterated_base (e_emp SSL) (e_star SSL)
              (map
                 (fun x : expr sym * list (expr sym) => apps (fst x) (snd x))
                 spatial0)) (if star_true0 then e_true SSL else e_emp SSL)).
      intros.
      induction H.
      { simpl. unfold iterated_base. simpl.
        consider (exprD us vs (e_and SSL (e_true SSL) e) SL); intros; forward.
        { intros.
          unfold exprD in *. destruct (split_env vs).
          forward. inv_all; subst.
          consider (exprD' us x (e_star SSL (e_emp SSL) e) SL); intros.
          { repeat go_crazy SSL SSLO.
            inv_all; subst.
            destruct (SSLO.(e_empOk) us x).
            destruct (SSLO.(e_trueOk) us x).
            rewrite H0 in *. destruct H3.
            rewrite H in *. destruct H5.
            inv_all; subst.
            Cases.rewrite_all_goal.
            rewrite empSPL. rewrite landtrueL.
            reflexivity. }
          { repeat go_crazy SSL SSLO.
            destruct (SSLO.(e_empOk) us x). destruct H3. congruence. } }
        { unfold exprD in *. destruct (split_env vs).
          forward; inv_all; subst.
          repeat go_crazy SSL SSLO.
          destruct (SSLO.(e_trueOk) us x).
          destruct H4.
          congruence. } }
      { simpl.
    Admitted.

(*
    Definition conjunctives_to_expr (c : conjunctives) : expr sym :=
      let ps := iterated e_and c.(pure) in
      let sp := iterated e_star (map (fun x => apps (fst x) (snd x)) c.(spatial)) in
      match ps , sp with
        | None , None => if c.(star_true) then e_true else e_emp
        | None , Some sp => if c.(star_true) then e_star sp e_true else sp
        | Some p , None => if c.(star_true) then p else e_and p e_emp
        | Some p , Some sp =>
          e_and p (if c.(star_true) then
                     e_star sp e_true
                   else
                     sp)
      end.
*)

    Variable SLS : SepLogSpec sym.
    Variable slsok : SepLogSpecOk RSym_sym SL SLS ILO BILO.

    Local Instance PureOp_it : @PureOp _  := slsok.(_PureOp).
    Local Instance Pure_it : @Pure _ _ _ slsok.(_PureOp) := _Pure slsok.
    Hypothesis pure_ltrue : Pure.pure ltrue.
    Hypothesis pure_land : forall p q, Pure.pure p -> Pure.pure q -> Pure.pure (land p q).

    Definition R_conjunctives
               (e : expr sym) (c : conjunctives) (tus tvs : tenv typ) : Prop :=
      forall us : hlist _ tus,
      forall val,
        exprD' (ts := ts) (join_env us) tvs e SL = Some val ->
        exists val',
             exprD' (join_env us) tvs (conjunctives_to_expr c) SL = Some val'
          /\ (forall vs,
                (val vs -|- val' vs) /\ well_formed _ c (join_env us) (join_env vs)).

    Ltac forward_ex_and :=
      repeat match goal with
               | H : exists x, _ |- _ => destruct H
               | H : _ /\ _ |- _ => destruct H
             end.

    Local Instance Reflexive_lentails : Reflexive lentails.
    Proof.
      destruct IL. destruct lentailsPre. auto.
    Qed.

    Require Import MirrorCore.Ext.ExprSem.

    Lemma something_smart
    : forall a b c d,
        Pure.pure a -> Pure.pure b ->
        (a //\\ b) //\\ c ** d -|- (a //\\ c) ** b //\\ d.
    Proof.
      clear - BIL IL. intros.
      symmetry.
      rewrite pureandscD by eauto with typeclass_instances.
      rewrite sepSPC.
      rewrite pureandscD by eauto with typeclass_instances.
      rewrite <- landA.
      rewrite sepSPC. reflexivity.
    Qed.

    Lemma well_formed_pure
    : forall x us tvs (vs : hlist _ tvs),
        well_formed _ x us (join_env vs) ->
        forall x7,
          exprD' us tvs (iterated_base SSL.(e_true) SSL.(e_and) (pure x)) SL = Some x7 ->
          Pure.pure (x7 vs).
    Proof.
      unfold well_formed. destruct x; simpl.
      induction 1; simpl; intros.
      { unfold iterated_base in H. simpl in *.
        destruct (SSLO.(e_trueOk) us tvs).
        rewrite H in *. destruct H0.
        inv_all; subst. eapply Pure.pure_proper. eapply H1.
        eapply pure_ltrue; eauto with typeclass_instances. }
      { unfold iterated_base in *. simpl in *.
        destruct (iterated SSL.(e_and) l); intros.
        { go_crazy SSL SSLO.
          eapply Pure.pure_proper. eapply H3.
          destruct H. destruct H.
          eapply pure_land; eauto with typeclass_instances.
          unfold exprD in *. rewrite split_env_join_env in *.
          rewrite H1 in *. inv_all. rewrite H. auto. }
        { destruct H. destruct H.
          unfold exprD in H. rewrite split_env_join_env in *.
          rewrite H1 in *. inv_all; subst.
          auto. } }
    Qed.

    Lemma Forall_app
    : forall T (P : T -> Prop) xs ys,
        List.Forall P (xs ++ ys) <-> (List.Forall P xs /\ List.Forall P ys).
    Proof.
      clear. induction xs; simpl; intros.
      { intuition. }
      { split; intros.
        { inversion H; subst. rewrite IHxs in H3. intuition. }
        { intuition. inversion H0; subst. constructor; eauto. eapply IHxs. auto. } }
    Qed.

    Lemma something_smart'
    : forall a b c d e f g,
        Pure.pure a -> Pure.pure b ->
        e -|- f ** g ->
        (a //\\ b) //\\ (c ** d) ** e -|-
                   (a //\\ c ** f) ** b //\\ d ** g.
    Proof.
      clear - BIL pure_land pure_ltrue. intros. rewrite H1. clear H1.
      transitivity ((a //\\ b) //\\ (c ** f) ** d ** g).
      { apply land_cancel; eauto with typeclass_instances.
        repeat rewrite sepSPA.
        rewrite (sepSPC c).
        rewrite (sepSPC c).
        apply lequiv_sep_cancel; eauto with typeclass_instances.
        repeat rewrite <- sepSPA.
        rewrite (sepSPC d f). reflexivity. }
      { rewrite something_smart by eauto. reflexivity. }
    Qed.

    Lemma cte_mkStar
    : forall us tvs r_res l_res rval lval,
        exprD' us tvs (conjunctives_to_expr r_res) SL = Some rval ->
        exprD' us tvs (conjunctives_to_expr l_res) SL = Some lval ->
        exists val,
          exprD' us tvs (conjunctives_to_expr (mkStar l_res r_res)) SL = Some val /\
          forall vs,
            well_formed _ l_res us (join_env vs) ->
            well_formed _ r_res us (join_env vs) ->
            (val vs -|- lval vs ** rval vs) /\
            well_formed _ (mkStar l_res r_res) us (join_env vs).
    Proof.
(*
      intros.
      consider (exprD' us tvs (conjunctives_to_expr (mkStar l_res r_res)) SL);
        intros; unfold conjunctives_to_expr, mkStar in *; simpl in *.
      { eexists; split; eauto. intros.
        split.
        { destruct (SSLO.(e_empOk) us tvs).
          destruct (SSLO.(e_trueOk) us tvs).
          rewrite map_app in *.
          forward_ex_and.
          generalize (@iterated_base_app _ SSL.(e_true) SSL.(e_and)
                        (Sem_equiv _ SL lequiv us (join_env vs))
                 (@Reflexive_Sem_equiv _ _ _ SL lequiv _ us (join_env vs))
                 (@Transitive_Sem_equiv _ _ _ SL lequiv _ us (join_env vs))
                 (Sem_equiv_e_and_assoc _ SSLO) Sem_equiv_Proper_e_and
                 Sem_equiv_e_true_e_and_unitLL
                 Sem_equiv_e_true_e_and_unitLR
                 Sem_equiv_e_true_e_and_unitRL
                 Sem_equiv_e_true_e_and_unitRR r_res.(pure) l_res.(pure) us tvs).
          generalize (@iterated_base_app _ e_emp e_star (Sem_equiv _ SL lequiv)
                (@Reflexive_Sem_equiv _ _ _ SL lequiv _)
                (@Transitive_Sem_equiv _ _ _ SL lequiv _)
                Sem_equiv_e_star_assoc Sem_equiv_Proper_e_star
                Sem_equiv_e_emp_e_star_unitLL
                Sem_equiv_e_emp_e_star_unitLR
                Sem_equiv_e_emp_e_star_unitRL
                Sem_equiv_e_emp_e_star_unitRR
                (map (fun x : expr sym * list (expr sym) => apps (fst x) (snd x)) r_res.(spatial))
                (map (fun x : expr sym * list (expr sym) => apps (fst x) (snd x)) l_res.(spatial))
                us tvs).
          repeat go_crazy.
          intros; forward.
          inv_all; subst.
          repeat match goal with
                   | H : forall x, _ -|- _ |- _ => rewrite H
                 end.
          assert (Pure.pure (x8 vs)).
          { eapply well_formed_pure; [ | eauto ]; eauto. }
          assert (Pure.pure (x9 vs)).
          { eapply well_formed_pure; [ | eauto ]; eauto. }
          destruct l_res.(star_true); destruct r_res.(star_true);
          intros; simpl in *; repeat go_crazy; inv_all; subst;
          repeat match goal with
                   | H : forall x, _ -|- _ |- _ => rewrite H
                 end; eapply something_smart'; auto.
          { rewrite ltrue_sep. reflexivity. }
          { rewrite empSPR. reflexivity. }
          { rewrite empSPL. reflexivity. }
          { rewrite empSPL. reflexivity. } }
        { red. simpl.
          apply Forall_app. split; assumption. } }
      { exfalso.
        generalize (@iterated_base_app _ e_true e_and (Sem_equiv _ SL lequiv)
                                     (@Reflexive_Sem_equiv _ _ _ SL lequiv _)
                                     (@Transitive_Sem_equiv _ _ _ SL lequiv _)
                                     Sem_equiv_e_and_assoc Sem_equiv_Proper_e_and
                 Sem_equiv_e_true_e_and_unitLL
                 Sem_equiv_e_true_e_and_unitLR
                 Sem_equiv_e_true_e_and_unitRL
                 Sem_equiv_e_true_e_and_unitRR r_res.(pure) l_res.(pure) us tvs).
        generalize (@iterated_base_app _ e_emp e_star (Sem_equiv _ SL lequiv)
           (@Reflexive_Sem_equiv _ _ _ SL lequiv _)
           (@Transitive_Sem_equiv _ _ _ SL lequiv _)
           Sem_equiv_e_star_assoc Sem_equiv_Proper_e_star
           Sem_equiv_e_emp_e_star_unitLL
           Sem_equiv_e_emp_e_star_unitLR
           Sem_equiv_e_emp_e_star_unitRL
           Sem_equiv_e_emp_e_star_unitRR
           (map (fun x : expr sym * list (expr sym) => apps (fst x) (snd x)) r_res.(spatial))
           (map (fun x : expr sym * list (expr sym) => apps (fst x) (snd x)) l_res.(spatial))
           us tvs).
        rewrite map_app in *.
        repeat go_crazy.
        inv_all; subst. intros; forward.
        destruct l_res.(star_true); destruct r_res.(star_true); simpl in *;
        repeat go_crazy; congruence. }
    Qed.
*) Admitted.

    Theorem SepLogArgsOk_conjunctives
    : SepLogArgsOk RSym_sym SL SepLogArgs_normalize SLS R_conjunctives.
    Proof.
      constructor; unfold R_conjunctives; simpl; intros.
      { unfold mkSpatial, conjunctives_to_expr. simpl.
        unfold iterated_base. simpl.
        consider (exprD' (join_env us) tvs (SSL.(e_and) SSL.(e_true) (SSL.(e_star) (apps e (map fst es)) SSL.(e_emp))) SL); intros;
        repeat (go_crazy SSL SSLO); inv_all; subst.
        { eexists; split; eauto.
          intros.
          destruct (SSLO.(e_empOk) (join_env us) tvs).
          destruct (SSLO.(e_trueOk) (join_env us) tvs).
          forward_ex_and.
          repeat (go_crazy SSL SSLO).
          inv_all; subst.
          repeat match goal with
                   | H : forall x, _ -|- _ |- _ =>
                     rewrite H
                 end.
          rewrite empSPR; eauto with typeclass_instances.
          rewrite landtrueL. split.
          reflexivity. constructor. }
        { destruct (SSLO.(e_trueOk) (join_env us) tvs) as [ ? [ ? ? ] ]. congruence. }
        { destruct (SSLO.(e_empOk) (join_env us) tvs) as [ ? [ ? ? ] ]. congruence. } }
      { unfold conjunctives_to_expr, mkPure; simpl.
        unfold iterated_base. simpl.
        destruct (SSLO.(e_empOk) (join_env us) tvs).
        destruct (SSLO.(e_trueOk) (join_env us) tvs).
        forward_ex_and.
        consider (exprD' (join_env us) tvs (SSL.(e_and) e (SSL.(e_star) SSL.(e_emp) SSL.(e_true))) SL);
          intros; do 5 (go_crazy SSL SSLO); try congruence.
        { eexists; split; eauto.
          intros. inv_all; subst.
          rewrite H8. rewrite H10. rewrite H4. rewrite H5.
          rewrite empSPL. rewrite landtrueR. split.
          { reflexivity. }
          { red. constructor. 2: constructor.
            unfold exprD. rewrite split_env_join_env. rewrite H1.
            eexists; split; eauto.
            eapply His_pure. eassumption.
            instantiate (1 := join_env vs).
            instantiate (1 := join_env us).
            unfold exprD. rewrite split_env_join_env. rewrite H1. reflexivity. } } }
      { unfold conjunctives_to_expr, mkEmpty; simpl.
        destruct (SSLO.(e_empOk) (join_env us) tvs).
        destruct (SSLO.(e_trueOk) (join_env us) tvs).
        forward_ex_and. unfold iterated_base. simpl.
        consider (exprD' (join_env us) tvs (SSL.(e_and) SSL.(e_true) (SSL.(e_star) SSL.(e_emp) SSL.(e_emp))) SL); 
          intros; repeat (go_crazy SSL SSLO); try congruence.
        { eexists; split; eauto.
          inv_all; subst. intros.
          split; try solve [ constructor ].
          eapply His_emp  with (us := join_env us) (vs := join_env vs) in H0; eauto.
          unfold exprD in *. rewrite split_env_join_env in *.
          rewrite H1 in *. inv_all; subst. rewrite H0.
          rewrite H8. rewrite H10. rewrite H4. rewrite H5.
          rewrite empSPL. rewrite landtrueL. reflexivity. } }
      { red_exprD.
        generalize (slsok.(His_star) _ H2 (join_env us)).
        rewrite H in *.
        unfold type_of_apply in *.
        forward.
        inv_all. subst t. subst t4. subst p. subst val.
        red_exprD. rewrite H in H8.
        forward. inv_all.
        subst p t2.
        specialize (H3 _ _ H8).
        subst t0 t1.
        specialize (H4 _ _ H9).
        forward_ex_and.
        specialize (@cte_mkStar (join_env us) tvs _ _ _ _ H4 H3); intros.
        forward_ex_and.
        eexists; split; eauto.
        intros.
        uip_all'.
        specialize (H7 (join_env vs)).
        unfold exprD in *.
        rewrite split_env_join_env in *.
        rewrite H5 in *. inv_all; subst.
        rewrite H7.
        specialize (H10 vs). specialize (H11 vs).
        forward_ex_and.
        specialize (H13 _ H16 H14).
        forward_ex_and. split; auto.
        symmetry. rewrite H11. rewrite H10. auto. }
    Qed.

  End conjunctivesD.

(*
  Section demo.
  Definition is_emp (i : sym) : bool :=
    match i with
      | ilf_true _ => true
      | _ => false
    end.
  Definition is_star (e : expr sym) : bool :=
    match e with
      | Inj (fref 1%positive) => true
      | _ => false
    end.


    Definition inj_emp := Inj (ilf_true (tyType 0)).
    Definition inj_star a b :=
      Eval compute in apps (Inj (fref 1%positive)) (a :: b :: nil).

    Definition test := fun x => app_fold_args normalizeArgs x nil nil.
    Eval compute in  test inj_emp.
    Eval compute in  test (inj_star inj_emp inj_emp).
    Eval compute in  test (inj_star (Var 0) (inj_star inj_emp (inj_and (Var 1) (Var 3)))).
  End demo.
*)

End cancel_state.
