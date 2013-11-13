Require Import Bool.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Tactics.Cases.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.
Require Import ExtLib.Tactics.Consider.
Require Import Setoid Morphisms RelationClasses.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.Ext.ExprD.
Require Import MirrorCore.Ext.ExprTactics.
Require Import ILogicFunc ILogic.

Set Implicit Arguments.
Set Strict Implicit.

Section Tauto.
  Context (ts : types) (funcs : fun_map ts) (gs : logic_ops ts).
  Context (H : forall g, match gs g return Type with
                             | Some T => @ILogic _ T
                             | None => unit
                           end).

  Local Instance RSym_ilfunc : SymI.RSym (typD ts) ilfunc := RSym_ilfunc ts funcs gs.

  Inductive Facts : Type :=
  | Inconsistent
  | Knows : list (expr ilfunc) -> Facts.

  Local Notation "P //\\ Q" := (App (App (Inj (ilf_and _)) P) Q).

  Fixpoint known_learn (e : expr ilfunc) (f : list (expr ilfunc)) : Facts :=
    match e with
      | Inj (ilf_true _) => Knows f
      | Inj (ilf_false _) => Inconsistent
      | P //\\ Q =>
        match known_learn Q f with
          | Inconsistent => Inconsistent
          | Knows f => known_learn P f
        end
      | _ => Knows (e :: f)
    end.

  Definition learn e f : Facts :=
    match f with
      | Inconsistent => Inconsistent
      | Knows fs => known_learn e fs
    end.

  Fixpoint known_assumption (env : list (expr ilfunc)) (p : expr ilfunc) :=
    match env with
      | nil => false
      | q :: env' =>
        if p ?[eq] q then
  	  true
  	else
  	  known_assumption env' p
    end.

  Definition assumption (f : Facts) (p : expr ilfunc) : bool :=
    match f with
      | Inconsistent => true
      | Knows fs => known_assumption fs p
    end.

  Fixpoint tauto (env : Facts) (p : expr ilfunc) : bool :=
    match p with
      | Inj (ilf_true _) => true
      | App (App (Inj (ilf_and _)) p) q => andb (tauto env p) (tauto (learn p env) q)
      | App (App (Inj (ilf_or _)) p) q => orb (tauto env p) (tauto env q)
      | App (App (Inj (ilf_impl _)) p) q => tauto (learn p env) q
      | _ => assumption env p
    end.

  Local Existing Instance lentailsPre.
  Local Hint Extern 1 (ILogic _) => eassumption : typeclass_instances.

  Section factsD.
    Variables (us vs : env (typD ts)).
    Variables (t : typ) (ILO : ILogicOps (typD ts nil t)).
    Hypothesis (Hgs : gs t = Some ILO).

    Fixpoint eval_env (env : list (expr ilfunc))
    : option (typD ts nil t) :=
      match env with
        | nil => Some (@ltrue _ ILO)
        | p :: env => match exprD us vs p t, eval_env env with
  		        | Some p, Some q => Some (@land _ ILO q p)
  		        | _, _ => None
  		      end
      end.

    Lemma known_assumption_sound
    : forall (env : _) (p : expr ilfunc) x v
	     (_ : exprD us vs p t = Some v)
	     (_ : eval_env env = Some x),
        known_assumption env p = true ->
        @lentails (typD ts nil t) ILO x v.
    Proof.
      induction env; simpl; intros; try congruence.
      forward; inv_all; subst.
      specialize (H t). rewrite Hgs in *.
      consider (p ?[ eq ] a); intros; subst.
      { rewrite H0 in *. inv_all; subst.
        eapply landL2. reflexivity. }
      { specialize (IHenv _ _ _ H0 eq_refl H4).
        eapply landL1. assumption. }
    Qed.

    Definition FactsD (f : Facts) : option (typD ts nil t) :=
      match f with
        | Inconsistent => Some (@lfalse _ ILO)
        | Knows fs => eval_env fs
      end.

    Lemma assumption_sound : forall (env : Facts) (p : expr ilfunc) x v
	                            (_ : exprD us vs p t = Some v)
	                            (_ : FactsD env = Some x)
                                    (_ : gs t = Some ILO),
                               assumption env p = true ->
                               @lentails (typD ts nil t) ILO x v.
    Proof.
      destruct env; simpl; intros; inv_all; subst.
      { specialize (H t). rewrite H2 in *.
        eapply lfalseL. }
      { eapply known_assumption_sound; eauto. }
    Qed.

    Lemma FactsD_known_cons
    : forall (f : list (expr ilfunc))
             (v : typD ts nil t)
             (P : typD ts nil t)
             (e : expr ilfunc),
        eval_env f = Some P ->
        exprD us vs e t = Some v ->
        exists Q : typD ts nil t,
          FactsD (Knows (e :: f)) = Some Q /\ land P v |-- Q.
    Proof.
      admit.
    Qed.

    Lemma FactsD_known_learn : forall e f f' v P,
      exprD us vs e t = Some v ->
      eval_env f = Some P ->
      known_learn e f = f' ->
      exists Q,
        FactsD f' = Some Q /\
        land P v |-- Q.
    Proof.
      refine (@expr_strong_ind _ _ _); intros.
      destruct e; subst; eauto using FactsD_known_cons.
      { simpl. destruct i; eauto using FactsD_known_cons.
        { red_exprD. simpl in *.
          forward; inv_all; subst.
          rewrite H2. eexists; split; eauto.
          specialize (H t). 
          rewrite H1 in *. inv_all; subst.
          apply landL1. reflexivity. }
        { red_exprD; simpl in *.
          forward; inv_all; subst.
          eexists; split; eauto.
          specialize (H t). rewrite H1 in *. inv_all; subst.
          eapply landL2. reflexivity. } }
      { simpl.
        destruct e1; eauto using FactsD_known_cons.
        destruct e1_1; eauto using FactsD_known_cons.
        destruct i; eauto using FactsD_known_cons.
        repeat (red_exprD; Cases.rewrite_all; forward; simpl in *; inv_all; try subst).
        revert H11. repeat subst.
        rewrite typ_cast_typ_refl in *. inv_all; subst.
        intros; subst. specialize (H t). rewrite H3 in *. inv_all; subst.
        consider (known_learn e2 f); intros.
        { eexists; split. reflexivity.
          eapply H0 in H1; eauto with typeclass_instances.
          destruct H1. destruct H1.
          simpl in H1. inv_all. subst.
          etransitivity. 2: eassumption.
          eapply landR.
          { eapply landL1. reflexivity. }
          { eapply landL2. eapply landL2. reflexivity. } }
        { eapply H0 in H1; eauto with typeclass_instances.
          destruct H1. destruct H1. simpl in H1.
          consider (known_learn e1_2 l); simpl; intros.
          { eexists; split; eauto.
            eapply H0 in H6; try eassumption; eauto with typeclass_instances.
            destruct H6. destruct H6.
            simpl in *. inv_all; subst.
            etransitivity; [ | eassumption ].
            eapply landR.
            { etransitivity; [ | eassumption ].
              eapply landR.
              { eapply landL1. reflexivity. }
              { eapply landL2; eapply landL2; reflexivity. } }
            { eapply landL2. eapply landL1. reflexivity. } }
          { eapply H0 in H6. 4: eassumption. 2: eauto with typeclass_instances.
            2: eauto.
            destruct H6. destruct H6.
            eexists; split; eauto.
            etransitivity; [ | eassumption ].
            eapply landR.
            { etransitivity; [ | eassumption ].
              eapply landR.
              { eapply landL1. reflexivity. }
              { eapply landL2. eapply landL2. reflexivity. } }
            { eapply landL2. eapply landL1. reflexivity. } } } }
    Qed.

    Lemma FactsD_learn : forall f f' e v P,
      exprD us vs e t = Some v ->
      FactsD f = Some P ->
      learn e f = f' ->
      exists Q,
        FactsD f' = Some Q /\
        land P v |-- Q.
    Proof.
      destruct f; simpl; intros; inv_all; subst.
      { exists lfalse. intuition.
        specialize (H t). rewrite Hgs in *.
        eapply landL1. reflexivity. }
      { eapply FactsD_known_learn; eauto. }
    Qed.

  End factsD.

  Lemma tauto_sound : forall (p : expr ilfunc) (t : typ) env us vs x v
    (_ : exprD us vs p t = Some v)
    (ILO : ILogicOps (typD ts nil t))
    (_ : gs t = Some ILO)
    (_ : FactsD us vs t ILO env = Some x),
    tauto env p = true ->
    @lentails (typD ts nil t) ILO x v.
  Proof.
    refine (@expr_strong_ind _ _ _); intros.
    destruct e; simpl in *; eauto using assumption_sound.
    { destruct i; eauto using assumption_sound.
      red_exprD. simpl in *.
      forward; inv_all; subst.
      specialize (H t).
      rewrite H1 in *. inv_all; subst.
      eapply ltrueR. }
    { destruct e1; eauto using assumption_sound.
      destruct e1_1; eauto using assumption_sound.
      destruct i; eauto using assumption_sound.
      { eapply andb_true_iff in H4. destruct H4.
        repeat (red_exprD; forward; inv_all; subst).
        red_exprD. rewrite H6 in *.
        red_exprD. rewrite H6 in *.
        rewrite typ_cast_typ_refl in *.
        simpl in *. forward; subst. inv_all; subst.
        inversion x0; subst. clear H9.
        uip_all'.
        rewrite H6 in H2. inv_all; subst.
        specialize (H t). rewrite H6 in *.
        eapply landR.
        { eapply H0; eauto.
          eauto with typeclass_instances. }
        { destruct (@FactsD_learn us vs _ _ H6 env (learn e1_2 env) e1_2 t1 x H7 H3 eq_refl).
          destruct H1.
          eapply H0 in H5. 5: eassumption. 4: eauto. 3: eauto. 2: eauto with typeclass_instances.
          etransitivity; [ | eassumption ].
          etransitivity; [ | eassumption ].
          eapply landR; eauto.
          { eapply H0; eauto. eauto with typeclass_instances. } } }
      { eapply orb_true_iff in H4.
        repeat (red_exprD; forward; inv_all; simpl in *; try subst).
        revert H13. repeat subst.
        specialize (H t).
        rewrite H5 in *. inv_all; subst.
        uip_all'; intros. subst.
        destruct H4.
        { eapply lorR1. eapply H0; eauto. eauto with typeclass_instances. }
        { eapply lorR2. eapply H0; eauto. eauto with typeclass_instances. } }
      { repeat (red_exprD; forward; inv_all; simpl in *; try subst).
        revert H13; repeat subst.
        uip_all'. intros; subst.
        specialize (H t).
        rewrite H5 in *; inv_all; subst.
        eapply limplAdj.
        destruct (@FactsD_learn us vs _ _ H5 env _ _ _ _ H9 H3 eq_refl).
        destruct H2.
        etransitivity.
        2: eapply H0. 6: eassumption. 5: eassumption. 4: eauto. 3: eauto. 2: eauto with typeclass_instances.
        eauto. } }
  Qed.

End Tauto.