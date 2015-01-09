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
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCharge.ILogicFunc.
Require Import MirrorCore.Lambda.Expr.

Set Implicit Arguments.
Set Strict Implicit.

Section Tauto.
  Variable typ : Type.
  Variable sym : Type.

  Inductive LogicCtor :=
  | LTrue | LFalse | LAnd | LOr | LImpl | LEntails.

  Record ILogicSpec : Type :=
  { as_logic : expr typ sym -> option LogicCtor
  }.

  Record EmbedSpec : Type :=
  { is_embed : expr typ sym -> option typ
  }.

  Variable tyProp : typ.
  Variable ilspec : ILogicSpec.
  Variable emspec : EmbedSpec.

  Definition Facts : Type := list (expr typ sym).

(*
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
*)

  (** Learning **)
  Section learning.
    Fixpoint known_learn (e : expr typ sym) (f : Facts) : option Facts :=
      match ilspec.(as_logic) e with
        | Some LTrue => Some f
        | Some LFalse => None
        | _ =>
          match e with
            | App (App bop l) r =>
              match ilspec.(as_logic) bop with
                | Some LAnd =>
                  match known_learn l f with
                    | None => None
                    | Some f' => known_learn r f'
                  end
                | _ => Some (e :: f)
              end
            | _ => Some (e :: f)
          end
      end.

    Definition learn e f : option Facts := known_learn e f.

    Variables (t : typ).

(*
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
*)
  End learning.

  Variable floor : expr typ sym -> typ -> typ -> option (expr typ sym).

(*
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
*)


  (** Lowering **)
  Section lowering.
    Variables from to : typ.

    Fixpoint known_lower_to (ls : list (expr typ sym)) : list (expr typ sym) :=
      match ls with
        | nil => nil
        | l :: ls =>
          match floor l from to with
            | None => known_lower_to ls
            | Some x => x :: known_lower_to ls
          end
      end.

    Definition lower_to (f : Facts) : Facts :=
      known_lower_to f.
  End lowering.

  Variable RelDec_expr : RelDec (@eq (expr typ sym)).

  Fixpoint known_assumption (env : list (expr typ sym)) (p : expr typ sym) :=
    match env with
      | nil => false
      | q :: env' =>
        if p ?[eq] q then
  	  true
  	else
  	  known_assumption env' p
    end.

  Definition assumption (f : Facts) (p : expr typ sym) : bool :=
    known_assumption f p.

(*
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
*)

  Fixpoint tauto (env : Facts) (goal : expr typ sym) (tyLogic : typ) : bool :=
    match ilspec.(as_logic) goal with
      | Some LTrue => true
      | _ =>
        match goal with
        | App z q =>
          match emspec.(is_embed) z with
            | Some t' =>
              tauto (lower_to tyLogic t' env) q t'
            | None =>
              match z with
                | App bop p =>
                  match ilspec.(as_logic) bop with
                    | Some LAnd =>
                      if tauto env p tyLogic then
                        match learn p env with
                          | None => true
                          | Some env' => tauto env' q tyLogic
                        end
                      else
                        false
                    | Some LOr => orb (tauto env p tyLogic) (tauto env q tyLogic)
                    | Some LImpl =>
                      match learn p env with
                        | None => true
                        | Some p' => tauto p' q tyLogic
                      end
                    | _ => assumption env goal
                  end
                | _ => assumption env goal
              end
          end
        | _ => assumption env goal
        end
    end.

  Fixpoint tauto_simplify (env : Facts) (goal : expr typ sym) (tyLogic : typ)
  : option (expr typ sym) :=
    match ilspec.(as_logic) goal with
      | Some LTrue => None
      | _ =>
        match goal with
        | App z q =>
          match emspec.(is_embed) z with
            | Some t' =>
              match tauto_simplify (lower_to tyLogic t' env) q t' with
                | None => None
                | Some q' => Some (App z q')
              end
            | None =>
              match z with
                | App bop p =>
                  match ilspec.(as_logic) bop with
                    | Some LAnd =>
                      match tauto_simplify env p tyLogic with
                        | None =>
                          match learn p env with
                            | None => None
                            | Some env' => tauto_simplify env' q tyLogic
                          end
                        | Some p =>
                          match learn p env with
                            | None => Some p
                            | Some env' =>
                              match tauto_simplify env' q tyLogic with
                                | None => Some p
                                | Some q => Some (App (App bop p) q)
                              end
                          end
                      end
                    | Some LOr =>
                      match tauto_simplify env p tyLogic
                          , tauto_simplify env q tyLogic
                      with
                        | None , _ => None
                        | _ , None => None
                        | Some P , Some Q => Some (App (App bop P) Q)
                      end
                    | Some LImpl =>
                      match learn p env with
                        | None => None
                        | Some p' => tauto_simplify p' q tyLogic
                      end
                    | Some LEntails =>
                      match learn p nil with
                        | None => None
                        | Some ps => tauto_simplify ps q tyProp
                      end
                    | _ => if assumption env goal then None else Some goal
                  end
                | _ => if assumption env goal then None else Some goal
              end
          end
        | _ => if assumption env goal then None else Some goal
        end
    end.


(*
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
*)


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
