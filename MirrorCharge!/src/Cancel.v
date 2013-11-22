(** This file implements cancellation for separation logic.
 **)
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import BILogic ILogic Pure.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Ext.Expr.
Require Import MirrorCore.Ext.AppFull.
Require Import ILogicFunc SepLogFold.

Set Implicit Arguments.
Set Strict Implicit.

Section iterated.
  Variable T : Type.
  Variable base : T.
  Variable join : T -> T -> T.

  Fixpoint iterated (ls : list T) : option T :=
    match ls with
      | nil => None
      | l :: ls => match iterated ls with
                     | None => Some l
                     | Some ls => Some (join l ls)
                   end
    end.

  Definition iterated_base (ls : list T) : T :=
    match iterated ls with
      | None => base
      | Some l => l
    end.

  Lemma iterated_None : forall ls, iterated ls = None -> ls = nil.
  Proof.
    destruct ls; simpl; intros; try congruence.
    destruct (iterated ls); congruence.
  Qed.

  Require Import Relations Morphisms.
  Require Import RelationClasses.

  Hypothesis R : relation T.
  Hypothesis Reflexive_R : Reflexive R.
  Hypothesis Transitive_R : Transitive R.
  Hypothesis join_assoc : forall a b c, R (join a (join b c)) (join (join a b) c).
  Hypothesis join_respects : Proper (R ==> R ==> R)%signature join.

  Definition option_R (a b : option T) : Prop :=
    match a , b with
      | None , None => True
      | Some a , Some b => R a b
      | _ , _ => False
    end.

  Local Instance Reflexive_optionR : Reflexive option_R.
  Proof.
    red. destruct x; simpl; reflexivity.
  Qed.
  Local Instance Transitive_optionR : Transitive option_R.
  Proof.
    red. destruct x; destruct y; destruct z; simpl; intros; auto.
    etransitivity; eauto. intuition.
  Qed.

  Theorem iterated_app
  : forall ls' ls,
      option_R (iterated (ls ++ ls'))
               (match iterated ls' with
                  | None => iterated ls
                  | Some ls' => match iterated ls with
                                  | None => Some ls'
                                  | Some ls => Some (join ls ls')
                                end
                end).
  Proof.
    induction ls; simpl.
    { intros. destruct (iterated ls'); reflexivity. }
    { intros. unfold option_R in *.
      repeat match goal with
               | |- context [ match ?X with _ => _ end ] =>
                 consider X; intros; try congruence
               | H : context [ match ?X with _ => _ end ] |- _ =>
                 consider X; intros; try congruence
               | H : R _ _ |- _ => rewrite H
             end; inv_all; subst; try solve [ congruence | intuition ].
      { rewrite IHls. etransitivity. 2: eapply join_assoc. reflexivity. }
      { rewrite H5. reflexivity. }
      { rewrite H4; reflexivity. }
      { subst. reflexivity. } }
  Qed.


  Hypothesis Rbase_LL : forall a, R (join base a) a.
  Hypothesis Rbase_LR : forall a, R (join a base) a.
  Hypothesis Rbase_RL : forall a, R a (join base a).
  Hypothesis Rbase_RR : forall a, R a (join a base).

  Theorem iterated_base_app
  : forall ls' ls,
      R (iterated_base (ls ++ ls'))
        (join (iterated_base ls) (iterated_base ls')).
  Proof.
    induction ls; simpl.
    { intros. unfold iterated_base. simpl.
      eapply Rbase_RL. }
    { unfold iterated_base in *; simpl in *.
      destruct (iterated (ls ++ ls')).
      { rewrite IHls.
        rewrite join_assoc.
        destruct (iterated ls); try reflexivity.
        rewrite Rbase_LR. reflexivity. }
      { destruct (iterated ls); destruct (iterated ls'); simpl.
        { rewrite <- join_assoc. rewrite <- IHls. eapply Rbase_RR. }
        { rewrite <- join_assoc. rewrite <- IHls. apply Rbase_RR. }
        { rewrite Rbase_LL in IHls.
          rewrite <- IHls. apply Rbase_RR. }
        { eapply Rbase_RR. } } }
  Qed.

  Variable P : T -> Prop.
  Hypothesis Pjoin : forall a b, P a -> P b -> P (join a b).

  Theorem iterated_inv
  : forall ls,
      List.Forall P ls ->
      match iterated ls with
        | None => ls = nil
        | Some e => P e
      end.
  Proof.
    clear - Pjoin. induction 1; simpl; intros; auto.
    destruct (iterated l); auto.
  Qed.

  Hypothesis Pbase : P base.

  Theorem iterated_base_inv
  : forall ls,
      List.Forall P ls ->
      P (iterated_base ls).
  Proof.
    clear - Pjoin Pbase.
    unfold iterated_base; intros.
    eapply iterated_inv in H. destruct (iterated ls); eauto.
  Qed.

End iterated.

Section cancel_state.
  Variable ts : types.
  Variable sym : Type.
  Variable RSym_sym : RSym (typD ts) sym.

  Record conjunctives : Type :=
  { spatial : option (list (expr sym * list (expr sym)))
  ; pure : list (expr sym)
  }.

  Definition mkEmpty : conjunctives :=
  {| spatial := Some (nil)
   ; pure := nil
   |}.

  Definition mkPure e : conjunctives :=
  {| spatial := None
   ; pure := e :: nil
   |}.

  Definition mkSpatial e es : conjunctives :=
  {| spatial := Some ((e,es) :: nil)
   ; pure := nil
   |}.

  Definition mkStar (l r : conjunctives) : conjunctives :=
  {| spatial := match l.(spatial)  with
                  | None => r.(spatial)
                  | Some a => match r.(spatial) with
                                | None => Some a
                                | Some b => Some (a ++ b)
                              end
                end
   ; pure := l.(pure) ++ r.(pure)
   |}.

  Definition SepLogArgs_normalize : SepLogArgs sym conjunctives :=
  {| do_emp := mkEmpty
   ; do_star := mkStar
   ; do_atomic_app := mkSpatial
   ; do_pure := mkPure
   |}.

  Variable SL : typ.

  Section conjunctivesD.
    Variable SLS : SepLogSpec sym.
    Variable ILO : ILogicOps (typD ts nil SL).
    Variable BILO : BILOperators (typD ts nil SL).
    Variable IL : @ILogic _ ILO.
    Variable BIL : @BILogic _ ILO BILO.

    Variable slsok : SepLogSpecOk RSym_sym SL SLS ILO BILO.

    Variable e_star : expr sym -> expr sym -> expr sym.
    Variable e_and : expr sym -> expr sym -> expr sym.
    Variable e_emp : expr sym.
    Variable e_true : expr sym.

    Definition well_formed (c : conjunctives) (us vs : env (typD ts)) : Prop :=
      List.Forall (fun e =>
                     exists val, exprD us vs e SL = Some val
                              /\ @Pure.pure _ slsok.(_PureOp) val) c.(pure).

    Definition conjunctives_to_expr (c : conjunctives) : expr sym :=
      match c.(spatial) with
        | None => iterated_base e_true e_and c.(pure)
        | Some s =>
          let s := iterated_base e_emp e_star (map (fun x => apps (fst x) (snd x)) s) in
          match iterated e_and c.(pure) with
            | None => s
            | Some p => e_and p s
          end
      end.

    Definition conjunctives_to_expr' (c : conjunctives) : expr sym :=
      let spa :=
          match c.(spatial) with
            | None => e_true
            | Some s => iterated_base e_emp e_star (map (fun x => apps (fst x) (snd x)) s)
          end
      in
      let pur := iterated_base e_true e_and c.(pure) in
      e_and pur spa.

    Definition R_conjunctives
               (e : expr sym) (c : conjunctives) (tus tvs : tenv typ) : Prop :=
      forall us : hlist _ tus,
      forall val,
        exprD' (ts := ts) (join_env us) tvs e SL = Some val ->
        exists val',
             exprD' (join_env us) tvs (conjunctives_to_expr c) SL = Some val'
          /\ (forall vs, 
                (val vs -|- val' vs) /\ well_formed c (join_env us) (join_env vs)).

    Hypothesis e_empOk : forall us tvs,
                         exists val,
                           exprD' us tvs e_emp SL = Some val /\
                           forall vs, val vs -|- empSP.
    Hypothesis e_trueOk : forall us tvs,
                          exists val,
                            exprD' us tvs e_true SL = Some val /\
                            forall vs, val vs -|- ltrue.
    Hypothesis e_starOk : forall us tvs x y valx valy,
                            exprD' us tvs x SL = Some valx ->
                            exprD' us tvs y SL = Some valy ->
                            exists val,
                              exprD' us tvs (e_star x y) SL = Some val /\
                              forall vs, val vs -|- valx vs ** valy vs.
    Hypothesis e_starValid : forall us tvs x y val,
                               exprD' us tvs (e_star x y) SL = Some val ->
                               exists valx valy,
                                 exprD' us tvs x SL = Some valx /\
                                 exprD' us tvs y SL = Some valy /\
                                 forall vs, val vs -|- valx vs ** valy vs.
    Hypothesis e_andOk : forall us tvs x y valx valy,
                            exprD' us tvs x SL = Some valx ->
                            exprD' us tvs y SL = Some valy ->
                            exists val,
                              exprD' us tvs (e_and x y) SL = Some val /\
                              forall vs, val vs -|- valx vs //\\ valy vs.
    Hypothesis e_andValid : forall us tvs x y val,
                              exprD' us tvs (e_and x y) SL = Some val ->
                              exists valx valy,
                                exprD' us tvs x SL = Some valx /\
                                exprD' us tvs y SL = Some valy /\
                                forall vs, val vs -|- valx vs //\\ valy vs.

    Ltac forward_ex_and :=
      repeat match goal with
               | H : exists x, _ |- _ => destruct H
               | H : _ /\ _ |- _ => destruct H
             end.

    Lemma e_andOk_None1
    : forall us tvs x y,
        exprD' us tvs x SL = None ->
        exprD' us tvs (e_and x y) SL = None.
    Proof.
      intros.
      consider (exprD' us tvs (e_and x y) SL); auto; intros.
      exfalso.
      eapply e_andValid in H0. forward_ex_and. congruence.
    Qed.

    Lemma e_andOk_None2
    : forall us tvs x y,
        exprD' us tvs y SL = None ->
        exprD' us tvs (e_and x y) SL = None.
    Proof.
      intros.
      consider (exprD' us tvs (e_and x y) SL); auto; intros.
      exfalso.
      eapply e_andValid in H0. forward_ex_and. congruence.
    Qed.

    Lemma e_starOk_None1
    : forall us tvs x y,
        exprD' us tvs x SL = None ->
        exprD' us tvs (e_star x y) SL = None.
    Proof.
      intros.
      consider (exprD' us tvs (e_star x y) SL); auto; intros.
      exfalso.
      eapply e_starValid in H0. forward_ex_and. congruence.
    Qed.

    Lemma e_starOk_None2
    : forall us tvs x y,
        exprD' us tvs y SL = None ->
        exprD' us tvs (e_star x y) SL = None.
    Proof.
      intros.
      consider (exprD' us tvs (e_star x y) SL); auto; intros.
      exfalso.
      eapply e_starValid in H0. forward_ex_and. congruence.
    Qed.

    Definition Sem_ext (t : typ) (P : typD ts nil t -> Prop) (Q : Prop)
    : expr sym -> Prop :=
      fun e =>
        forall us tvs,
          match exprD' us tvs e t with
            | Some val =>
              forall vs, P (val vs)
            | None => Q
          end.

    Ltac go_crazy :=
      match goal with
        | H : exprD' _ _ _ _ = _ , H' : _ |- _ =>
          rewrite H in H'
        | H : exprD' _ _ _ _ = _ |- _ =>
          rewrite H
        | H : exprD' _ _ (e_and _ _) _ = _ |- _ =>
          eapply e_andValid in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
        | H : exprD' _ _ (e_star _ _) _ = _ |- _ =>
          eapply e_starValid in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
        | H : exprD' _ _ ?C _ = _
        , H' : exprD' _ _ ?D _ = _
        |- context [ exprD' ?A ?B (e_and ?C ?D) ?T ] =>
          destruct (@e_andOk _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
        | H : exprD' _ _ ?C _ = _
        , H' : exprD' _ _ ?D _ = _
        |- context [ exprD' ?A ?B (e_star ?C ?D) ?T ] =>
          destruct (@e_starOk _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
        | H : exprD' _ _ ?C _ = _
        , H' : exprD' _ _ ?D _ = _
        , H'' : context [ exprD' ?A ?B (e_star ?C ?D) ?T ]
        |- _ =>
          destruct (@e_starOk _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
        | H : exprD' _ _ ?C _ = _
        , H' : exprD' _ _ ?D _ = _
        , H'' : context [ exprD' ?A ?B (e_and ?C ?D) ?T ]
        |- _ =>
          destruct (@e_andOk _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
        | H : exprD' _ _ _ _ = None |- _ =>
          first [ erewrite (@e_starOk_None1 _ _ _ _ H) in *
                | erewrite (@e_starOk_None2 _ _ _ _ H) in *
                | erewrite (@e_andOk_None1 _ _ _ _ H) in *
                | erewrite (@e_andOk_None2 _ _ _ _ H) in * ]
      end.

    Local Instance Reflexive_lentails : Reflexive lentails.
    Proof.
      destruct IL. destruct lentailsPre. auto.
    Qed.

    Require Import MirrorCore.Ext.ExprSem.

    Theorem conjunctives_to_expr_conjunctives_to_expr'
    : forall e,
        Sem_equiv _ SL lequiv (conjunctives_to_expr e) (conjunctives_to_expr' e).
    Proof.
      destruct e.
      unfold conjunctives_to_expr, conjunctives_to_expr', iterated_base; simpl.
      generalize (iterated e_and pure0); intros.
      destruct spatial0.
      { generalize (iterated e_star
                             (map
                                (fun x : expr sym * list (expr sym) =>
                                   apps (fst x) (snd x)) l)).
        intro.
        generalize (match o0 with
                      | Some l0 => l0
                      | None => e_emp
                    end); intro.
        red. intros.
        destruct o.
        { forward. reflexivity. }
        { destruct (e_trueOk us tvs). destruct H.
          consider (exprD' us tvs e SL); intros; repeat go_crazy; auto.
          inv_all; subst. intros. rewrite H3. rewrite H0.
          rewrite landtrueL. reflexivity. } }
      { red. intros.
        generalize (match o with
                      | Some l => l
                      | None => e_true
                    end); intros.
        destruct (e_trueOk us tvs). destruct H.
        consider (exprD' us tvs e SL); intros; repeat go_crazy; auto.
        inv_all; subst. intros.
        rewrite H5. rewrite H0. rewrite landtrueR. reflexivity. }
    Qed.

    Lemma Sem_equiv_e_and_assoc
    : forall a b c : expr sym,
        Sem_equiv _ SL lequiv (e_and a (e_and b c)) (e_and (e_and a b) c).
    Proof.
      clear - IL e_andOk e_andValid. intros.
      red. intros.
      consider (exprD' us tvs (e_and a (e_and b c)) SL);
        consider (exprD' us tvs (e_and (e_and a b) c) SL); intros; auto.
      { eapply e_andValid in H. eapply e_andValid in H0.
        do 2 destruct H; do 2 destruct H0.
        destruct H0. destruct H1. destruct H. destruct H3.
        eapply e_andValid in H. do 3 destruct H. destruct H5.
        eapply e_andValid in H1. do 3 destruct H1. destruct H7.
        rewrite H4. rewrite H2. rewrite H6. rewrite H8.
        rewrite H0 in *. rewrite H5 in *. rewrite H7 in *.
        inv_all; subst.
        symmetry. eapply landA. }
      { eapply e_andValid in H0.
        do 3 destruct H0. destruct H1.
        eapply e_andValid in H1.
        do 3 destruct H1. destruct H3.
        destruct (@e_andOk _ _ _ _ _ _ H0 H1). destruct H5.
        destruct (@e_andOk _ _ _ _ _ _ H5 H3). destruct H7.
        congruence. }
      { eapply e_andValid in H.
        do 3 destruct H. destruct H1.
        eapply e_andValid in H.
        do 3 destruct H. destruct H3.
        destruct (@e_andOk _ _ _ _ _ _ H3 H1). destruct H5.
        destruct (@e_andOk _ _ _ _ _ _ H H5). destruct H7.
        congruence. }
    Qed.

    Lemma Sem_equiv_e_star_assoc
    : forall a b c : expr sym,
        Sem_equiv _ SL lequiv (e_star a (e_star b c)) (e_star (e_star a b) c).
    Proof.
      clear - IL BIL e_starOk e_starValid. intros.
      red. intros.
      consider (exprD' us tvs (e_star a (e_star b c)) SL);
        consider (exprD' us tvs (e_star (e_star a b) c) SL); intros; auto.
      { eapply e_starValid in H. eapply e_starValid in H0.
        do 2 destruct H; do 2 destruct H0.
        destruct H0. destruct H1. destruct H. destruct H3.
        eapply e_starValid in H. do 3 destruct H. destruct H5.
        eapply e_starValid in H1. do 3 destruct H1. destruct H7.
        rewrite H4. rewrite H2. rewrite H6. rewrite H8.
        rewrite H0 in *. rewrite H5 in *. rewrite H7 in *.
        inv_all; subst.
        symmetry. eapply sepSPA. }
      { eapply e_starValid in H0.
        do 3 destruct H0. destruct H1.
        eapply e_starValid in H1.
        do 3 destruct H1. destruct H3.
        destruct (@e_starOk _ _ _ _ _ _ H0 H1). destruct H5.
        destruct (@e_starOk _ _ _ _ _ _ H5 H3). destruct H7.
        congruence. }
      { eapply e_starValid in H.
        do 3 destruct H. destruct H1.
        eapply e_starValid in H.
        do 3 destruct H. destruct H3.
        destruct (@e_starOk _ _ _ _ _ _ H3 H1). destruct H5.
        destruct (@e_starOk _ _ _ _ _ _ H H5). destruct H7.
        congruence. }
    Qed.

    Lemma Sem_equiv_Proper_e_and
    : Proper (Sem_equiv _ SL lequiv ==> Sem_equiv _ SL lequiv ==> Sem_equiv _ SL lequiv) e_and.
    Proof.
      unfold Sem_equiv; repeat red; simpl; intros.
      specialize (H us tvs). specialize (H0 us tvs).
      match goal with
        | |- match ?X with _ => _ end =>
          consider X; intros
      end; repeat go_crazy; forward; repeat go_crazy.
      { inv_all; subst.
        intros. rewrite H3. rewrite H4. rewrite H9.
        rewrite H5. reflexivity. }
      { forward.
        go_crazy. congruence. }
    Qed.

    Lemma Sem_equiv_Proper_e_star
    : Proper (Sem_equiv _ SL lequiv ==> Sem_equiv _ SL lequiv ==> Sem_equiv _ SL lequiv) e_star.
    Proof.
      unfold Sem_equiv; repeat red; simpl; intros.
      specialize (H us tvs). specialize (H0 us tvs).
      match goal with
        | |- match ?X with _ => _ end =>
          consider X; intros
      end; repeat go_crazy; forward; repeat go_crazy.
      { inv_all; subst.
        intros. rewrite H3. rewrite H4. rewrite H9.
        rewrite H5. reflexivity. }
      { forward.
        go_crazy. congruence. }
    Qed.

    Lemma ltrue_unitL : forall a, land ltrue a -|- a.
    Proof.
      clear - IL; intros.
      split.
      { eapply landL2. reflexivity. }
      { eapply landR; try reflexivity. eapply ltrueR. }
    Qed.

    Lemma ltrue_unitR : forall a, land a ltrue -|- a.
    Proof.
      clear - IL; intros.
      split.
      { eapply landL1. reflexivity. }
      { eapply landR; try reflexivity. eapply ltrueR. }
    Qed.

    Lemma empSPR : forall a, a ** empSP -|- a.
    Proof.
      clear - BIL IL; intros.
      rewrite sepSPC. rewrite empSPL. reflexivity.
    Qed.

    Lemma Sem_equiv_e_true_e_and_unitLL
    : forall a : expr sym,
        Sem_equiv _ SL lequiv (e_and e_true a) a.
    Proof.
      red; intros.
      destruct (e_trueOk us tvs) as [ ? [ ? ? ] ].
      consider (exprD' us tvs a SL); intros; repeat go_crazy; auto.
      inv_all; subst; intros.
      Cases.rewrite_all. clear - IL.
      rewrite ltrue_unitL. reflexivity.
    Qed.

    Lemma Sem_equiv_e_true_e_and_unitLR
    : forall a : expr sym,
        Sem_equiv _ SL lequiv (e_and a e_true) a.
    Proof.
      red; intros.
      destruct (e_trueOk us tvs) as [ ? [ ? ? ] ].
      consider (exprD' us tvs a SL); intros; repeat go_crazy; auto.
      inv_all; subst; intros.
      Cases.rewrite_all. clear - IL.
      rewrite ltrue_unitR. reflexivity.
    Qed.
    Lemma Sem_equiv_e_true_e_and_unitRL
    : forall a : expr sym,
        Sem_equiv _ SL lequiv a (e_and e_true a).
    Proof.
      red; intros.
      destruct (e_trueOk us tvs) as [ ? [ ? ? ] ].
      consider (exprD' us tvs a SL); intros; repeat go_crazy; auto.
      inv_all; subst; intros.
      Cases.rewrite_all. clear - IL.
      rewrite ltrue_unitL. reflexivity.
    Qed.
    Lemma Sem_equiv_e_true_e_and_unitRR
    : forall a : expr sym,
        Sem_equiv _ SL lequiv a (e_and a e_true).
    Proof.
      red; intros.
      destruct (e_trueOk us tvs) as [ ? [ ? ? ] ].
      consider (exprD' us tvs a SL); intros; repeat go_crazy; auto.
      inv_all; subst; intros.
      Cases.rewrite_all. clear - IL.
      rewrite ltrue_unitR. reflexivity.
    Qed.

    Lemma Sem_equiv_e_emp_e_star_unitLL
    : forall a : expr sym,
        Sem_equiv _ SL lequiv (e_star e_emp a) a.
    Proof.
      red; intros.
      destruct (e_empOk us tvs) as [ ? [ ? ? ] ].
      consider (exprD' us tvs a SL); intros; repeat go_crazy; auto.
      inv_all; subst; intros.
      Cases.rewrite_all. clear - BIL IL.
      rewrite empSPL. reflexivity.
    Qed.
    Lemma Sem_equiv_e_emp_e_star_unitLR
    : forall a : expr sym,
        Sem_equiv _ SL lequiv (e_star a e_emp) a.
    Proof.
      red; intros.
      destruct (e_empOk us tvs) as [ ? [ ? ? ] ].
      consider (exprD' us tvs a SL); intros; repeat go_crazy; auto.
      inv_all; subst; intros.
      Cases.rewrite_all. clear - BIL.
      rewrite empSPR. reflexivity.
    Qed.
    Lemma Sem_equiv_e_emp_e_star_unitRL
    : forall a : expr sym,
        Sem_equiv _ SL lequiv a (e_star e_emp a).
    Proof.
      red; intros.
      destruct (e_empOk us tvs) as [ ? [ ? ? ] ].
      consider (exprD' us tvs a SL); intros; repeat go_crazy; auto.
      inv_all; subst; intros.
      Cases.rewrite_all. clear - BIL.
      rewrite empSPL. reflexivity.
    Qed.
    Lemma Sem_equiv_e_emp_e_star_unitRR
    : forall a : expr sym,
        Sem_equiv _ SL lequiv a (e_star a e_emp).
    Proof.
      red; intros.
      destruct (e_empOk us tvs) as [ ? [ ? ? ] ].
      consider (exprD' us tvs a SL); intros; repeat go_crazy; auto.
      inv_all; subst; intros.
      Cases.rewrite_all. clear - BIL.
      rewrite empSPR. reflexivity.
    Qed.

    Local Instance PureOp_it : @PureOp _  := slsok.(_PureOp).
    Local Instance Pure_it : @Pure _ _ _ slsok.(_PureOp) := _Pure slsok.

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
        well_formed x us (join_env vs) ->
        forall x7,
          exprD' us tvs (iterated_base e_true e_and (pure x)) SL = Some x7 ->
          Pure.pure (x7 vs).
    Proof.
      unfold well_formed. destruct x; simpl.
      induction 1; simpl; intros.
      { unfold iterated_base in H. simpl in *.
        destruct (e_trueOk us tvs).
        rewrite H in *. destruct H0.
        inv_all; subst. rewrite H1.
        eapply pure_ltrue; eauto with typeclass_instances. }
      { unfold iterated_base in *. simpl in *.
        destruct (iterated e_and l); intros.
        { go_crazy.
          rewrite H3.
          destruct H. destruct H.
          eapply pure_land; eauto with typeclass_instances.
          unfold exprD in *. rewrite split_env_join_env in *.
          rewrite H1 in *. inv_all. rewrite H. auto. }
        { destruct H. destruct H.
          unfold exprD in H. rewrite split_env_join_env in *.
          rewrite H1 in *. inv_all; subst.
          auto. } }
    Qed.

    Lemma Forall_app : forall T (P : T -> Prop) xs ys,
                         List.Forall P (xs ++ ys) <-> (List.Forall P xs /\ List.Forall P ys).
    Proof.
      clear. induction xs; simpl; intros.
      { intuition. }
      { split; intros.
        { inversion H; subst. rewrite IHxs in H3. intuition. }
        { intuition. inversion H0; subst. constructor; eauto. eapply IHxs. auto. } }
    Qed.

    Lemma cte_mkStar
    : forall us tvs r_res l_res rval lval,
        exprD' us tvs (conjunctives_to_expr r_res) SL = Some rval ->
        exprD' us tvs (conjunctives_to_expr l_res) SL = Some lval ->
        exists val,
          exprD' us tvs (conjunctives_to_expr (mkStar l_res r_res)) SL = Some val /\
          forall vs,
            well_formed l_res us (join_env vs) ->
            well_formed r_res us (join_env vs) ->
            (val vs -|- lval vs ** rval vs) /\
            well_formed (mkStar l_res r_res) us (join_env vs).
    Proof.
      intros.
      specialize (conjunctives_to_expr_conjunctives_to_expr' r_res us tvs).
      specialize (conjunctives_to_expr_conjunctives_to_expr' l_res us tvs).
      specialize (conjunctives_to_expr_conjunctives_to_expr' (mkStar l_res r_res) us tvs).
      About Reflexive_Sem_equiv.
      generalize (@iterated_base_app _ e_true e_and (Sem_equiv _ SL lequiv)
                                     (@Reflexive_Sem_equiv _ _ _ SL lequiv _)
                                     (@Transitive_Sem_equiv _ _ _ SL lequiv _)
                                     Sem_equiv_e_and_assoc Sem_equiv_Proper_e_and
                 Sem_equiv_e_true_e_and_unitLL
                 Sem_equiv_e_true_e_and_unitLR
                 Sem_equiv_e_true_e_and_unitRL
                 Sem_equiv_e_true_e_and_unitRR r_res.(pure) l_res.(pure) us tvs).
(*
      generalize (@iterated_base_app _ e_emp e_star (Sem_equiv _ SL lequiv) _ _
                                     Sem_equiv_e_star_assoc Sem_equiv_Proper_e_star
                 Sem_equiv_e_emp_e_star_unitLL
                 Sem_equiv_e_emp_e_star_unitLR
                 Sem_equiv_e_emp_e_star_unitRL
                 Sem_equiv_e_emp_e_star_unitRR (map
                (fun x : expr sym * list (expr sym) => apps (fst x) (snd x))
                (spatial r_res)) (map
                (fun x : expr sym * list (expr sym) => apps (fst x) (snd x))
                (spatial l_res)) us tvs).
 *)
      Cases.rewrite_all_goal.
      unfold Sem_equiv, mkStar, conjunctives_to_expr', conjunctives_to_expr; simpl.
      clear H H0; intros; forward.
      repeat go_crazy.
      inv_all; subst.
      forward. 
      repeat go_crazy.
      admit.
(*
      destruct (spatial l_res).
      { destruct (spatial r_res).

      match goal with
        | |- exists x, exprD' _ _ ?X _ = _ /\ _ =>
          generalize dependent X
      end.
      intros.
      consider (exprD' us tvs e SL); intros; forward.
      { eexists; split; eauto.
        intros. split.
        rewrite H4 , 
                 
      generalize dependent (match
                               match spatial l_res with
                                 | Some a =>
                                   match spatial r_res with
                                     | Some b => Some (a ++ b)
                                     | None => Some a
                                   end
                                 | None => spatial r_res
                               end
                             with
                               | Some s =>
                                 match iterated e_and (pure l_res ++ pure r_res) with
                                   | Some p =>
                                     e_and p
                                           (iterated_base e_emp e_star
                                                          (map
                                                             (fun x : expr sym * list (expr sym) =>
                                                                apps (fst x) (snd x)) s))
                                   | None =>
                                     iterated_base e_emp e_star
                                                   (map
                                                      (fun x : expr sym * list (expr sym) =>
                                                         apps (fst x) (snd x)) s)
                                 end
                               | None => iterated_base e_true e_and (pure l_res ++ pure r_res)
                             end); 
      


      destruct (l_res.(spatial)); destruct (r_res.(spatial)).
      { generalize (
      inv_all; subst.
      consider (iterated e_and (pure l_res ++ pure r_res)); intros.
      { forward. repeat go_crazy.
        inv_all; subst.
        eexists; split; eauto.
        intros.
        unfold iterated_base in H0. rewrite H1 in H0.
        rewrite H0 in H14. inv_all; subst.
        split.
        { rewrite H4 , H5. rewrite H9 , H7 , H21.
          rewrite H12. rewrite H11.
          rewrite H10. rewrite H15.
          eapply something_smart.
          red in H20.
          eapply well_formed_pure. 2: eauto. eauto.
          eapply well_formed_pure. 2: eauto. eauto. }
        { unfold well_formed; simpl.
          rewrite Forall_app. split.
          eapply H20. eapply H22. } }
      { eapply iterated_None in H1. rewrite H1 in *.
        unfold iterated_base in H0. simpl in H0.
        repeat go_crazy.
        eexists; split; eauto.
        intros. unfold well_formed; simpl; split; auto.
        rewrite H4 , H5 , H7. rewrite H14. rewrite H16. rewrite H9.
        rewrite H10. rewrite H17. rewrite H12 , H11.
        eapply something_smart.
        clear - H1 H2 e_trueOk BIL IL.
        unfold iterated_base in *.
        destruct (pure l_res); simpl in *; try congruence.
        specialize (e_trueOk us tvs). destruct e_trueOk. rewrite H2 in *.
        destruct H. inv_all; subst.
        rewrite H0. eapply pure_ltrue; eauto with typeclass_instances.
        clear - H1 H3 e_trueOk BIL IL.
        unfold iterated_base in *.
        destruct (pure l_res); simpl in *; try congruence.
        specialize (e_trueOk us tvs). rewrite H1 in *. simpl in *.
        destruct e_trueOk. rewrite H3 in *.
        destruct H. inv_all; subst.
        rewrite H0. eapply pure_ltrue; eauto with typeclass_instances. }
*)
    Qed.

(*
    Lemma cte_mkStar
    : forall us tvs r_res l_res rval lval val,
        exprD' us tvs (conjunctives_to_expr r_res) SL = Some rval ->
        exprD' us tvs (conjunctives_to_expr l_res) SL = Some lval ->
        exprD' us tvs (conjunctives_to_expr (mkStar l_res r_res)) SL = Some val ->
        forall vs, val vs -|- lval vs ** rval vs.
    Proof.
      intros.
      specialize (conjunctives_to_expr_conjunctives_to_expr' r_res us tvs).
      specialize (conjunctives_to_expr_conjunctives_to_expr' l_res us tvs).
      specialize (conjunctives_to_expr_conjunctives_to_expr' (mkStar l_res r_res) us tvs).
      Cases.rewrite_all_goal.
      unfold mkStar, conjunctives_to_expr'; simpl.
      clear H H0 H1; intros; forward.
      rewrite map_app in *.
      generalize dependent (map
                (fun x : expr sym * list (expr sym) => apps (fst x) (snd x))
                (spatial l_res)).
      generalize dependent (map (fun x : expr sym * list (expr sym) => apps (fst x) (snd x))
               (spatial r_res)); intros.
      assert (forall a b c : expr sym,
                Sem_equiv SL lequiv (e_and a (e_and b c)) (e_and (e_and a b) c)).
      { clear - IL e_andOk e_andValid. intros.
        red. intros.
        consider (exprD' us tvs (e_and a (e_and b c)) SL);
          consider (exprD' us tvs (e_and (e_and a b) c) SL); intros; auto.
        { eapply e_andValid in H. eapply e_andValid in H0.
          do 2 destruct H; do 2 destruct H0.
          destruct H0. destruct H1. destruct H. destruct H3.
          eapply e_andValid in H. do 3 destruct H. destruct H5.
          eapply e_andValid in H1. do 3 destruct H1. destruct H7.
          rewrite H4. rewrite H2. rewrite H6. rewrite H8.
          rewrite H0 in *. rewrite H5 in *. rewrite H7 in *.
          inv_all; subst.
          symmetry. eapply landA. }
        { eapply e_andValid in H0.
          do 3 destruct H0. destruct H1.
          eapply e_andValid in H1.
          do 3 destruct H1. destruct H3.
          destruct (@e_andOk _ _ _ _ _ _ H0 H1). destruct H5.
          destruct (@e_andOk _ _ _ _ _ _ H5 H3). destruct H7.
          congruence. }
        { eapply e_andValid in H.
          do 3 destruct H. destruct H1.
          eapply e_andValid in H.
          do 3 destruct H. destruct H3.
          destruct (@e_andOk _ _ _ _ _ _ H3 H1). destruct H5.
          destruct (@e_andOk _ _ _ _ _ _ H H5). destruct H7.
          congruence. } }
      assert (Proper
                (Sem_equiv SL lequiv ==> Sem_equiv SL lequiv ==> Sem_equiv SL lequiv)
                e_and).
      { clear - IL e_andOk e_andValid. intros.
        repeat red; unfold Sem_equiv; intros.
        specialize (H us tvs). specialize (H0 us tvs).
        admit. }
      assert (forall a : expr sym, Sem_equiv SL lequiv (e_and e_emp a) a) by admit.
      assert (forall a : expr sym, Sem_equiv SL lequiv (e_and a e_emp) a) by admit.
      assert (forall a : expr sym, Sem_equiv SL lequiv a (e_and e_emp a)) by admit.
      assert (forall a : expr sym, Sem_equiv SL lequiv a (e_and a e_emp)) by admit.
      eapply e_starValid in H1. eapply e_starValid in H0. eapply e_starValid in H.
      repeat match goal with
               | H : exists x, _ |- _ => destruct H
               | H : _ /\ _ |- _ => destruct H
             end.
      specialize (@iterated_base_app (expr sym) e_emp e_and (@Sem_equiv SL lequiv) _ _ H5 H6 H7 H8 H9 H10 
                                     (pure r_res) (pure l_res) us tvs).
      rewrite H.
      destruct (@e_andOk us tvs _ _ _ _ H0 H1). destruct H17. rewrite H17; intros.
      assert (forall a : expr sym, Sem_equiv SL lequiv (e_star e_emp a) a) by admit.
      assert (forall a : expr sym, Sem_equiv SL lequiv (e_star a e_emp) a) by admit.
      assert (forall a : expr sym, Sem_equiv SL lequiv a (e_star e_emp a)) by admit.
      assert (forall a : expr sym, Sem_equiv SL lequiv a (e_star a e_emp)) by admit.
      assert (forall a b c : expr sym,
                Sem_equiv SL lequiv (e_star a (e_star b c)) (e_star (e_star a b) c)).
      { clear - IL BIL e_starOk e_starValid. intros.
        red. intros.
        consider (exprD' us tvs (e_star a (e_star b c)) SL);
          consider (exprD' us tvs (e_star (e_star a b) c) SL); intros; auto.
        { eapply e_starValid in H. eapply e_starValid in H0.
          do 2 destruct H; do 2 destruct H0.
          destruct H0. destruct H1. destruct H. destruct H3.
          eapply e_starValid in H. do 3 destruct H. destruct H5.
          eapply e_starValid in H1. do 3 destruct H1. destruct H7.
          rewrite H4. rewrite H2. rewrite H6. rewrite H8.
          rewrite H in *. rewrite H1 in *. rewrite H7 in *.
          inv_all; subst. rewrite sepSPA. reflexivity. }
        { eapply e_starValid in H0.
          do 3 destruct H0. destruct H1.
          eapply e_starValid in H1.
          do 3 destruct H1. destruct H3.
          destruct (@e_starOk _ _ _ _ _ _ H0 H1). destruct H5.
          destruct (@e_starOk _ _ _ _ _ _ H5 H3). destruct H7.
          congruence. }
        { eapply e_starValid in H.
          do 3 destruct H. destruct H1.
          eapply e_starValid in H.
          do 3 destruct H. destruct H3.
          destruct (@e_starOk _ _ _ _ _ _ H3 H1). destruct H5.
          destruct (@e_starOk _ _ _ _ _ _ H H5). destruct H7.
          congruence. } }
      assert (Proper
                (Sem_equiv SL lequiv ==> Sem_equiv SL lequiv ==> Sem_equiv SL lequiv)
                e_star) by admit.
      specialize (@iterated_base_app (expr sym) e_emp e_star (@Sem_equiv SL lequiv) _ _ H24 H25 H20 H21 H22 H23
                                     l l0 us tvs).
      rewrite H11.
      destruct (@e_starOk us tvs _ _ _ _ H13 H15). destruct H26. rewrite H26; intros.
      rewrite H4 , H3 , H2 , H12 , H14 , H16.
      rewrite H28 , H19 , H18. rewrite H27.
      admit.
    Qed.
*)


    Theorem SepLogArgsOk_conjunctives : SepLogArgsOk RSym_sym SL SepLogArgs_normalize SLS R_conjunctives.
    Proof.
      constructor; unfold R_conjunctives; simpl; intros.
      { unfold mkSpatial, conjunctives_to_expr. simpl.
        eexists; split; eauto.
        split. reflexivity; intros.
        intuition. red. simpl. constructor. }
      { unfold conjunctives_to_expr, mkPure; simpl.
        unfold iterated_base. simpl.
        eexists; split; eauto; intros.
        split; auto.
        red. simpl. constructor; auto.
        unfold exprD. rewrite split_env_join_env. rewrite H1.
        eexists; split; eauto.
        eapply His_pure in H0.
        eapply H0.
        instantiate (1 := join_env vs).
        instantiate (1 := join_env us).
        unfold exprD. rewrite split_env_join_env. rewrite H1. reflexivity. }
      { unfold conjunctives_to_expr, mkEmpty; simpl.
        specialize (e_empOk (join_env us) tvs). destruct e_empOk; clear e_empOk.
        destruct H2. eexists; split; eauto.
        split; intros.
        rewrite H3. generalize (slsok.(His_emp) _ H0 (join_env us) (join_env vs)).
        unfold exprD. rewrite split_env_join_env. rewrite H1. intros.
        inv_all. rewrite H4. reflexivity.
        red; simpl. constructor. }
      { red_exprD.
        generalize (slsok.(His_star) _ H2 (join_env us)).
        unfold type_of_apply in *.
        forward. inv_all; subst. inv_all. subst t0 t5. clear H5.
        unfold mkStar, conjunctives_to_expr. simpl.
        red_exprD. forward. inv_all; subst.
        specialize (H3 _ _ H10).
        specialize (H4 _ _ H9).
        destruct H3. destruct H4.
        destruct H , H3.
        destruct (@cte_mkStar (join_env us) tvs _ _ _ _ H3 H).
        destruct H11. unfold mkStar in H11. unfold conjunctives_to_expr in H11.
        simpl in H11.
        eexists; split; eauto.
        uip_all'. simpl in *.
        specialize (H4 vs); specialize (H6 vs).
        destruct H4 , H6.
        destruct (H13 vs H14 H15).
        split.
        { eapply His_star in H2; eauto with typeclass_instances.
          revert H2.
          instantiate (1 := join_env vs).
          instantiate (1 := join_env us).
          intros. unfold exprD in H2. rewrite split_env_join_env in H2.
          rewrite H8 in *. inv_all. rewrite H2.
          rewrite H16. rewrite H4 , H6. reflexivity. }
        { eapply H17. } }
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

  Require Import ExtLib.Structures.Monads.
  Require Import ExtLib.Data.Monads.StateMonad.

  Section with_monad.
    Local Open Scope monad_scope.
    Import MonadNotation.

    Definition conjunctives_remove (c : conjunctives) (e : expr ilfunc)
    : option conjunctives:= None.

(*
  Definition cancel_atomic (e : expr ilfunc) : state conjunctives conjunctives :=
    (lhs <- get ;;
     match conjunctives_remove lhs e with
       | None => (** it wasn't found **)
         ret (atomic e)
       | Some r =>
         put r ;;
         ret empty
     end)%monad.

  Definition cancelArgs : AppFullFoldArgs ilfunc (state conjunctives conjunctives) :=
  {| do_var := fun v _ _ => cancel_atomic (Var v)
   ; do_uvar := fun u _ _ => cancel_atomic (UVar u)
   ; do_inj := fun i _ _ => cancel_atomic (Inj i)
   ;


  Definition cancel (rhs : expr ilfunc) : conjunctives -> (conjunctives * conjunctives).
*)
  End with_monad.

End cancel_state.