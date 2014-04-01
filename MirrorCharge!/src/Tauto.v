Require Import Coq.Bool.Bool.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import ILogic ILEmbed.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Recur.Relation.
Require Import ExtLib.Tactics.Cases.
Require Import ExtLib.Tactics.Injection.
Require Import ExtLib.Tactics.EqDep.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorCore.Ext.ExprCore.
Require Import MirrorCore.Ext.Types.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.Ext.ExprD.
Require Import MirrorCore.Ext.ExprTactics.
Require Import ILogicFunc.

Set Implicit Arguments.
Set Strict Implicit.

Section Tauto.
  Context (ts : types) (funcs : fun_map ts) (gs : logic_ops ts) (es : embed_ops ts).
  Context (H : logic_opsOk gs).
  Context (Hembed : embed_opsOk gs es).

  Local Notation "P //\\ Q" := (App (App (Inj (ilf_and _)) P) Q).

  Theorem ILogic_from t z (pf : gs t = Some z) : @ILogic _ z.
    specialize (H t). rewrite pf in *.
    assumption.
  Qed.

  Ltac get_logic t :=
    match goal with
      | Hgs : gs ?X = Some t
      |- _ =>
        exact (@ILogic_from _ _ Hgs)
    end.

  Local Instance RSym_ilfunc : SymI.RSym (typD ts) ilfunc := @RSym_ilfunc ts funcs gs es.
  Local Hint Extern 0 (@ILogic _ ?X) => get_logic X : typeclass_instances.
  Local Existing Instance lentailsPre.
  Local Hint Extern 1 (ILogic _) => eassumption : typeclass_instances.
  Local Hint Extern 1 (@Embed _ _ _ _ _) => eassumption : typeclass_instances.

  Inductive Facts : Type :=
  | Inconsistent
  | Knows : list (expr ilfunc) -> Facts.

  (** Facts Denotation **)
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

    Definition FactsD (f : Facts) : option (typD ts nil t) :=
      match f with
        | Inconsistent => Some (@lfalse _ ILO)
        | Knows fs => eval_env fs
      end.
  End factsD.

  (** Learning **)
  Section learning.
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

    Variables (us vs : env (typD ts)).
    Variables (t : typ) (ILO : ILogicOps (typD ts nil t)).
    Hypothesis (Hgs : gs t = Some ILO).

    Lemma FactsD_known_cons
    : forall (f : list (expr ilfunc))
             (v : typD ts nil t)
             (P : typD ts nil t)
             (e : expr ilfunc),
        eval_env us vs t _ f = Some P ->
        exprD us vs e t = Some v ->
        exists Q : typD ts nil t,
          FactsD us vs t _ (Knows (e :: f)) = Some Q /\ land P v |-- Q.
    Proof.
      simpl; intuition.
      rewrite H1. rewrite H0.
      eexists; split; eauto.
      reflexivity.
    Qed.

    Lemma FactsD_known_learn : forall e f f' v P,
      exprD us vs e t = Some v ->
      eval_env us vs t _ f = Some P ->
      known_learn e f = f' ->
      exists Q,
        FactsD us vs t _ f' = Some Q /\
        land P v |-- Q.
    Proof.
      refine (@expr_strong_ind _ _ _); intros.
      destruct e; subst; eauto using FactsD_known_cons.
      { simpl. destruct i; eauto using FactsD_known_cons.
        { red_exprD. simpl in *.
          forward; inv_all; subst.
          rewrite H2. eexists; split; eauto.
          apply landL1. reflexivity. }
        { red_exprD; simpl in *.
          forward; inv_all; subst.
          eexists; split; eauto.
          rewrite H1 in *. inv_all; subst.
          eapply landL2. reflexivity. } }
      { simpl.
        destruct e1; eauto using FactsD_known_cons.
        destruct e1_1; eauto using FactsD_known_cons.
        destruct i; eauto using FactsD_known_cons.
        repeat (red_exprD; Cases.rewrite_all_goal; forward;
                simpl in *; inv_all; try subst).
        destruct (H0 e2 _ f _ _ _ H5 H2 eq_refl) as [ ? [ ? ? ] ].
        consider (known_learn e2 f); intros.
        { simpl in *.
          inv_all; subst.
          eexists; split; try reflexivity.
          rewrite <- H4.
          apply landR.
          - apply landL1. reflexivity.
          - apply landL2.
            rewrite H1 in *. inv_all; subst.
            apply landL2. reflexivity. }
        { destruct (H0 e1_2 _ l _ _ _ H7 H6 eq_refl) as [ ? [ ? ? ] ].
          eexists; split. eassumption.
          rewrite H1 in *. inv_all; subst.
          rewrite <- H9.
          apply landR.
          - etransitivity; [ | eapply H4 ].
            apply landR.
            + apply landL1. reflexivity.
            + apply landL2. apply landL2. reflexivity.
          - apply landL2. apply landL1. reflexivity. } }
    Qed.

    Lemma FactsD_learn : forall f f' e v P,
      exprD us vs e t = Some v ->
      FactsD us vs t _ f = Some P ->
      learn e f = f' ->
      exists Q,
        FactsD us vs t _ f' = Some Q /\
        land P v |-- Q.
    Proof.
      destruct f; simpl; intros; inv_all; subst.
      { exists lfalse. intuition.
        specialize (H t). rewrite Hgs in *.
        eapply landL1. reflexivity. }
      { eapply FactsD_known_learn; eauto. }
    Qed.

  End learning.

  Variable floor : expr ilfunc -> typ -> typ -> option (expr ilfunc).

  Definition floor_spec e e' from to : Prop :=
    forall us vs P ILT ILU eTU,
      gs from = Some ILT ->
      gs to = Some ILU ->
      es from to = Some eTU ->
      exprD us vs e to = Some P ->
      exists Q,
        exprD us vs e' from = Some Q /\
        @lentails _ _ P (embed Q).

  Hypothesis Hfloor : forall e e' from to,
                        floor e from to = Some e' ->
                        floor_spec e e' from to.

  (** Lowering **)
  Section lowering.
    Variables from to : typ.

    Fixpoint known_lower_to (ls : list (expr ilfunc)) : list (expr ilfunc) :=
      match ls with
        | nil => nil
        | l :: ls =>
          match floor l from to with
            | None => known_lower_to ls
            | Some x => x :: known_lower_to ls
          end
      end.

    Definition lower_to (f : Facts) : Facts :=
      match f with
        | Inconsistent => Inconsistent
        | Knows fs => Knows (known_lower_to fs)
      end.

    Variables (us vs : env (typD ts)).
    Context {ILF} `{Hgs_from : gs from = Some ILF}.
    Context {ILT} `{Hgs_to : gs to = Some ILT}.
    Context {eFT} `{Hes_from_to : es from to = Some eFT}.


    Lemma known_lower_to_sound : forall ls P ls',
      known_lower_to ls = ls' ->
      eval_env us vs to _ ls = Some P ->
      exists Q,
        eval_env us vs from _ ls' = Some Q /\
        lentails P (embed Q).
    Proof.
      induction ls; simpl; intros; subst; inv_all; subst.
      { simpl in *. eexists; split; eauto.
        assert (Embed (typD ts nil from) (typD ts nil to)).
        { specialize (Hembed from to).
          rewrite Hgs_to in *. rewrite Hgs_from in *.
          rewrite Hes_from_to in *. assumption. }
        eapply embedltrue. }
      { forward; inv_all; subst.
        specialize (IHls _ _ eq_refl eq_refl).
        destruct IHls; intuition.
        consider (floor a from to); intros.
        { simpl. rewrite H3.
          specialize (Hfloor H2). red in Hfloor.
          specialize (@Hfloor us vs _ _ _ _ Hgs_from Hgs_to Hes_from_to H0).
          destruct Hfloor; clear Hfloor. intuition.
          rewrite H6. eexists; split; eauto.
          specialize (Hembed from to).
          generalize (H from).
          generalize (H to).
          rewrite Hgs_from in *. rewrite Hgs_to in *.
          rewrite Hes_from_to in *.
          rewrite H4. rewrite H7.
          intros. eapply embedland.  }
        { eexists; split; eauto.
          rewrite H4. apply landL1. reflexivity. } }
    Qed.

    Theorem lower_to_sound : forall ls P ls',
      lower_to ls = ls' ->
      FactsD us vs to _ ls = Some P ->
      exists Q,
        FactsD us vs from _ ls' = Some Q /\
        lentails P (embed Q).
    Proof.
      destruct ls; simpl; intros; subst; inv_all; subst; simpl.
      { eexists; split; eauto. }
      { eapply known_lower_to_sound in H1; eauto. }
    Qed.

  End lowering.

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

  Section assumption.
    Variables (us vs : env (typD ts)).
    Variables (t : typ) (ILO : ILogicOps (typD ts nil t)).
    Hypothesis (Hgs : gs t = Some ILO).

    Lemma known_assumption_sound
    : forall (env : _) (p : expr ilfunc) x v
	     (_ : exprD us vs p t = Some v)
	     (_ : eval_env us vs t _ env = Some x),
        known_assumption env p = true ->
        @lentails (typD ts nil t) ILO x v.
    Proof.
      induction env; simpl; intros; try congruence.
      forward; inv_all; subst.
      consider (p ?[ eq ] a); intros; subst.
      { rewrite H0 in *. inv_all; subst.
        eapply landL2. reflexivity. }
      { specialize (IHenv _ _ _ H0 eq_refl H4).
        eapply landL1. assumption. }
    Qed.

    Lemma assumption_sound : forall (env : Facts) (p : expr ilfunc) x v
	                            (_ : exprD us vs p t = Some v)
	                            (_ : FactsD us vs t _ env = Some x)
                                    (_ : gs t = Some ILO),
                               assumption env p = true ->
                               @lentails (typD ts nil t) ILO x v.
    Proof.
      destruct env; simpl; intros; inv_all; subst.
      { specialize (H t). rewrite H2 in *.
        eapply lfalseL. }
      { eapply known_assumption_sound; eauto. }
    Qed.
  End assumption.

  Fixpoint tauto (env : Facts) (p : expr ilfunc) : bool :=
    match p with
      | Inj (ilf_true _) => true
      | App (App (Inj (ilf_and _)) p) q => andb (tauto env p) (tauto (learn p env) q)
      | App (App (Inj (ilf_or _)) p) q => orb (tauto env p) (tauto env q)
      | App (App (Inj (ilf_impl _)) p) q => tauto (learn p env) q
      | App (Inj (ilf_embed from to)) p' =>
        match gs from with
          | None => assumption env p
          | Some _ => tauto (lower_to from to env) p'
        end
      | _ =>
        (** TODO: This is the source of incompleteness **)
        assumption env p
    end.

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
      { destruct i; eauto using assumption_sound.
        consider (gs from); eauto using assumption_sound; intros.
        repeat (red_exprD; forward; inv_all; simpl in *; try subst).
        uip_all'.
        eapply lower_to_sound in H3. 4: eassumption.
        3: eauto. 2: eauto. 2: reflexivity.
        destruct H3. intuition.
        eapply H0 in H6.
        5: eassumption. 4: eauto. 3: eauto. 2: eauto with typeclass_instances.
        rewrite H7.
        specialize (Hembed t1 t).
        rewrite H2 in *. rewrite H4 in *. rewrite H1 in *.
        eapply embed_sound. eassumption. }
      { destruct e1_1; eauto using assumption_sound.
        destruct i; eauto using assumption_sound.
        { eapply andb_true_iff in H4. destruct H4.
          repeat (red_exprD; forward; inv_all; subst).
          simpl in *. forward; inv_all; subst.
          subst. subst.
          simpl in *. forward. inv_all; subst. clear H11 H12.
          uip_all'.
          rewrite H2 in *; inv_all; subst.
          eapply landR.
          { eapply H0; eauto.
            eauto with typeclass_instances. }
          { destruct (@FactsD_learn us vs _ _ H2 env (learn e1_2 env) e1_2 _ x H10 H3 eq_refl).
            destruct H1.
            eapply H0 in H5. 5: eassumption. 4: eauto. 3: eauto. 2: eauto with typeclass_instances.
            etransitivity; [ | eassumption ].
            etransitivity; [ | eassumption ].
            eapply landR; eauto.
            { eapply H0; eauto. eauto with typeclass_instances. } } }
        { eapply orb_true_iff in H4.
          repeat (red_exprD; forward; inv_all; simpl in *; try subst).
          revert x0. uip_all'.
          rewrite H1 in *. inv_all; subst.
          destruct H4.
          { eapply lorR1. eapply H0; eauto. eauto with typeclass_instances. }
          { eapply lorR2. eapply H0; eauto. eauto with typeclass_instances. } }
        { repeat (red_exprD; forward; inv_all; simpl in *; try subst).
          uip_all'.
          rewrite H1 in *; inv_all; subst.
          eapply limplAdj.
          destruct (@FactsD_learn us vs _ _ H1 env _ _ _ _ H9 H3 eq_refl).
          destruct H2.
          etransitivity.
          2: eapply H0. 6: eassumption. 5: eassumption. 4: eauto. 3: eauto. 2: eauto with typeclass_instances.
          eauto. } } }
  Qed.

End Tauto.


(**
  Definition test_floor (e : expr ilfunc) (from to : typ) : option (expr ilfunc) :=
    match e with
      | App (Inj (ilf_embed from' to')) e' =>
        if from ?[ eq ] from'
        then Some e'
        else None
      | _ => None
    end.

  Theorem test_floor_sound : forall e t t' e',
                               test_floor e t t' = Some e' ->
                               floor_sound e e' t t'.
  Proof.
    red.
    destruct e; simpl; intuition; try congruence.
    forward. subst.
    inv_all; subst.
    red_exprD.
    forward. inv_all; subst.
    red_exprD. simpl in *.
    Cases.rewrite_all.
    rewrite H4 in *.
    rewrite typ_cast_typ_refl in *.
    inv_all; subst.
    eexists; split; eauto.
    reflexivity.
  Qed.
**)