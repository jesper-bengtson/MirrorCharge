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

(** TODO: This should be moved elsewhere, really it is based on folding **)
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
      let spa := iterated_base e_emp e_star (map (fun x => apps (fst x) (snd x)) c.(spatial)) in
      let pur := iterated_base e_true e_and c.(pure) in
      e_and pur (e_star spa (if c.(star_true) then e_true else e_emp)).

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

    Lemma exprD'_e_and_None
    : forall us tvs a b,
        exprD' us tvs (e_and a b) SL = None ->
        exprD' us tvs a SL = None \/ exprD' us tvs b SL = None.
    Proof.
      intros.
      consider (exprD' us tvs a SL); intros; auto.
      consider (exprD' us tvs b SL); intros; auto.
      exfalso.
      specialize (@e_andOk _ _ _ _ _ _ H0 H1).
      destruct e_andOk. intuition; congruence.
    Qed.

    Lemma exprD'_e_star_None
    : forall us tvs a b,
        exprD' us tvs (e_star a b) SL = None ->
        exprD' us tvs a SL = None \/ exprD' us tvs b SL = None.
    Proof.
      intros.
      consider (exprD' us tvs a SL); intros; auto.
      consider (exprD' us tvs b SL); intros; auto.
      exfalso.
      specialize (@e_starOk _ _ _ _ _ _ H0 H1).
      destruct e_starOk. intuition; congruence.
    Qed.

    Ltac go_crazy :=
      match goal with
        | H : exprD' _ _ _ _ = _ , H' : _ |- _ =>
          rewrite H in H'
        | H : exprD' _ _ _ _ = _ |- _ =>
          rewrite H
        | H : exprD' _ _ ?C _ = _
        , H' : exprD' _ _ ?D _ = _
        |- context [ exprD' ?A ?B (e_and ?C ?D) ?T ] =>
          destruct (@e_andOk _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
        | H : exprD' _ _ ?C _ = _
        , H' : exprD' _ _ ?D _ = _
        |- context [ exprD' ?A ?B (e_star ?C ?D) ?T ] =>
          destruct (@e_starOk _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
        | H : exprD' _ _ (e_and _ _) _ = _ |- _ =>
          eapply e_andValid in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
        | H : exprD' _ _ (e_star _ _) _ = _ |- _ =>
          eapply e_starValid in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
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

        | H : exprD' _ _ _ _ = None |- _ =>
          first [ congruence
                | apply exprD'_e_star_None in H; destruct H; try congruence
                | apply exprD'_e_and_None in H; destruct H; try congruence ]
      end.

(*
    Ltac go_crazy' :=
      match goal with
        | H : exprD' _ _ _ _ = _ , H' : _ |- _ =>
          rewrite H in H'
        | H : exprD' _ _ _ _ = _ |- _ =>
          rewrite H
        | H : exprD' _ _ ?C _ = _
        , H' : exprD' _ _ ?D _ = _
        |- context [ exprD' ?A ?B (e_and ?C ?D) ?T ] =>
          destruct (@e_andOk _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
        | H : exprD' _ _ ?C _ = _
        , H' : exprD' _ _ ?D _ = _
        |- context [ exprD' ?A ?B (e_star ?C ?D) ?T ] =>
          destruct (@e_starOk _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
        | H : exprD' _ _ (e_and _ _) _ = _ |- _ =>
          eapply e_andValid in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
        | H : exprD' _ _ (e_star _ _) _ = _ |- _ =>
          eapply e_starValid in H ; destruct H as [ ? [ ? [ ? [ ? ? ] ] ] ]
        | H : exprD' _ _ ?C _ = _
        , H' : exprD' _ _ ?D _ = _
        , H'' : context [ match exprD' ?A ?B (e_star ?C ?D) ?T with _ => _ end ]
        |- _ =>
          destruct (@e_starOk _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
        | H : exprD' _ _ ?C _ = _
        , H' : exprD' _ _ ?D _ = _
        , H'' : context [ match exprD' ?A ?B (e_and ?C ?D) ?T with _ => _ end ]
        |- _ =>
          destruct (@e_andOk _ _ _ _ _ _ H H') as [ ? [ ? ? ] ]
        | H : exprD' _ _ _ _ = None |- _ =>
          first [ congruence
                | apply exprD'_e_star_None in H; destruct H; try congruence
                | apply exprD'_e_and_None in H; destruct H; try congruence ]
      end.
*)

    Local Instance Reflexive_lentails : Reflexive lentails.
    Proof.
      destruct IL. destruct lentailsPre. auto.
    Qed.

    Require Import MirrorCore.Ext.ExprSem.

    Local Instance PureOp_it : @PureOp _  := slsok.(_PureOp).
    Local Instance Pure_it : @Pure _ _ _ slsok.(_PureOp) := _Pure slsok.
    Hypothesis pure_ltrue : Pure.pure ltrue.
    Hypothesis pure_land : forall p q, Pure.pure p -> Pure.pure q -> Pure.pure (land p q).

    Lemma ltrue_sep : ltrue ** ltrue -|- ltrue.
    Proof.
      constructor.
      { apply ltrueR. }
      { rewrite <- pureandsc by eauto with typeclass_instances.
        apply landR; reflexivity. }
    Qed.

    Lemma pure_star_and_true : forall a b,
                                 Pure.pure a ->
                                 a ** b -|- a //\\ b ** ltrue.
    Proof.
      clear - BIL.
      intros.
      rewrite <- (landtrueR a) at 1.
      rewrite pureandscD by eauto with typeclass_instances.
      rewrite sepSPC. reflexivity.
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
      inv_all; subst; intros. clear pure_land pure_ltrue.
      Cases.rewrite_all_goal. clear - IL.
      rewrite ltrue_unitL. reflexivity.
    Qed.

    Lemma Sem_equiv_e_true_e_and_unitLR
    : forall a : expr sym,
        Sem_equiv _ SL lequiv (e_and a e_true) a.
    Proof.
      red; intros.
      destruct (e_trueOk us tvs) as [ ? [ ? ? ] ].
      consider (exprD' us tvs a SL); intros; repeat go_crazy; auto.
      inv_all; subst; intros. clear pure_land pure_ltrue.
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
      inv_all; subst; intros. clear pure_land pure_ltrue.
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
      inv_all; subst; intros. clear pure_land pure_ltrue.
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
      inv_all; subst; intros. clear pure_land pure_ltrue.
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
      inv_all; subst; intros. clear pure_land pure_ltrue.
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
      inv_all; subst; intros. clear pure_land pure_ltrue.
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
      inv_all; subst; intros. clear pure_land pure_ltrue.
      Cases.rewrite_all. clear - BIL.
      rewrite empSPR. reflexivity.
    Qed.

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

    Lemma lequiv_sep_cancel : forall a b c,
                                a -|- b -> a ** c -|- b ** c.
    Proof.
      split; apply bilsep; eapply H.
    Qed.
    Lemma land_cancel : forall a b c, b -|- c -> a //\\ b -|- a //\\ c.
    Proof.
      intros. rewrite H. reflexivity.
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
      { apply land_cancel.
        repeat rewrite sepSPA.
        rewrite (sepSPC c).
        rewrite (sepSPC c).
        apply lequiv_sep_cancel.
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
            well_formed l_res us (join_env vs) ->
            well_formed r_res us (join_env vs) ->
            (val vs -|- lval vs ** rval vs) /\
            well_formed (mkStar l_res r_res) us (join_env vs).
    Proof.
      intros.
      consider (exprD' us tvs (conjunctives_to_expr (mkStar l_res r_res)) SL);
        intros; unfold conjunctives_to_expr, mkStar in *; simpl in *.
      { eexists; split; eauto. intros.
        split.
        { destruct (e_empOk us tvs); clear e_empOk.
          destruct (e_trueOk us tvs); clear e_trueOk.
          rewrite map_app in *.
          forward_ex_and.
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

    Theorem SepLogArgsOk_conjunctives : SepLogArgsOk RSym_sym SL SepLogArgs_normalize SLS R_conjunctives.
    Proof.
      constructor; unfold R_conjunctives; simpl; intros.
      { unfold mkSpatial, conjunctives_to_expr. simpl.
        unfold iterated_base. simpl.
        consider (exprD' (join_env us) tvs (e_and e_true (e_star (apps e es) e_emp)) SL); intros;
        repeat go_crazy; inv_all; subst.
        { eexists; split; eauto.
          intros.
          destruct (e_empOk (join_env us) tvs); clear e_empOk.
          destruct (e_trueOk (join_env us) tvs); clear e_trueOk.
          forward_ex_and.
          go_crazy. inv_all; subst.
          rewrite H3 , H5. rewrite H7.
          rewrite H4 in *. inv_all; subst. rewrite H8.
          rewrite empSPR. rewrite landtrueL. split.
          reflexivity. constructor. }
        { destruct (e_trueOk (join_env us) tvs).
          destruct H2; congruence. } 
        { destruct (e_empOk (join_env us) tvs).
          destruct H2; congruence. } }
      { unfold conjunctives_to_expr, mkPure; simpl.
        unfold iterated_base. simpl.
        destruct (e_empOk (join_env us) tvs); clear e_empOk.
        destruct (e_trueOk (join_env us) tvs); clear e_trueOk.
        forward_ex_and.
        consider (exprD' (join_env us) tvs (e_and e (e_star e_emp e_true)) SL);
          intros; do 3 go_crazy; try congruence.
        { eexists; split; eauto.
          intros.
          repeat go_crazy. inv_all; subst.
          rewrite H8. rewrite H10. rewrite H4. rewrite H5.
          rewrite empSPL. rewrite landtrueR. split.
          reflexivity.
          red. constructor. 2: constructor.
          unfold exprD. rewrite split_env_join_env. rewrite H1.
          eexists; split; eauto.
          eapply His_pure. eassumption.
          instantiate (1 := join_env vs).
          instantiate (1 := join_env us).
          unfold exprD. rewrite split_env_join_env. rewrite H1. reflexivity. } }
      { unfold conjunctives_to_expr, mkEmpty; simpl.
        destruct (e_empOk (join_env us) tvs); clear e_empOk.
        destruct (e_trueOk (join_env us) tvs); clear e_trueOk.
        forward_ex_and. unfold iterated_base. simpl.
        consider (exprD' (join_env us) tvs (e_and e_true (e_star e_emp e_emp)) SL); 
          intros; repeat go_crazy; try congruence.
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


(**
    Theorem conjunctives_to_expr_conjunctives_to_expr'
    : forall e us tvs,
        match exprD' us tvs (conjunctives_to_expr e) SL
            , exprD' us tvs (conjunctives_to_expr' e) SL
        with
          | Some l , Some r =>
            forall vs,
              well_formed e us (join_env vs) ->
              l vs -|- r vs
          | None , None => True
          | _ , _ => False
        end.
    Proof.
      destruct e.
      unfold conjunctives_to_expr, conjunctives_to_expr', iterated_base; simpl.
      unfold well_formed; simpl; intros.
      specialize (e_trueOk us tvs); destruct e_trueOk as [ ? [ ? ? ] ]; clear e_trueOk.
      specialize (e_empOk us tvs); destruct e_empOk as [ ? [ ? ? ] ]; clear e_empOk.
      



      assert (
          List.Forall
            (fun e : expr sym =>
               exists val : _ -> typD ts nil SL,
                 exprD' us tvs e SL = Some val) pure0 -> 
            match iterated e_and pure0 with
              | None => pure0 = nil
              | Some z =>
                exists p, exprD' us tvs z SL = Some p /\ 
                          forall vs : hlist (typD ts nil) tvs,
                            List.Forall
                              (fun e : expr sym =>
                                 exists val : _ -> typD ts nil SL,
                                   exprD' us tvs e SL = Some val /\ Pure.pure (val vs)) pure0 ->
                            Pure.pure (p vs)
            end).
      { induction 1; simpl; intros; auto.
        destruct (iterated e_and l); forward_ex_and.
        { repeat go_crazy. eexists; split; eauto. inv_all; subst.
          intros. inversion H7; clear H7; subst.
          eapply H6 in H13. forward_ex_and. rewrite H10.
          rewrite H3 in *. inv_all; subst.
          eapply pure_land; eauto. }
        { subst. clear H4. eexists; split; eauto. intros.
          inversion H4; clear H4; subst. forward_ex_and.
          rewrite H3 in *. inv_all; subst; auto. } }
      generalize dependent (iterated e_and pure0); intros.
      destruct spatial0.
      { destruct (iterated e_star
                           (map
                              (fun x1 : expr sym * list (expr sym) =>
                                 apps (fst x1) (snd x1)) l));
        destruct o; destruct star_true0; intros.
        { consider (exprD' us tvs (e_star e0 e) SL); intros; forward.
          { consider (exprD' us tvs (e_and e0 (e_star e e_true)) SL); intros; repeat go_crazy.
            { inv_all; subst. rewrite H12. rewrite H8. rewrite H10.
              rewrite H0.
              assert (List.Forall
                        (fun e : expr sym =>
                           exists val : hlist (typD ts nil) tvs -> typD ts nil SL,
                             exprD' us tvs e SL = Some val) pure0).
              { admit. }
              apply H3 in H5; clear H3. forward_ex_and. inv_all; subst.
              assert (Pure.pure (x vs)) by admit.
              eapply pure_star_and_true; auto. }
            { apply exprD'_e_and_None in H5; destruct H5; try congruence.
              apply exprD'_e_star_None in H5; destruct H5; congruence. } }
          { do 4 go_crazy.
            apply exprD'_e_star_None in H4; destruct H4; congruence. } }
        { consider (exprD' us tvs (e_and e0 (e_star e e_emp)) SL); intros; forward; repeat go_crazy.
          { inv_all; subst. intros.
            rewrite H12. rewrite H6. rewrite H8. rewrite H2.
            rewrite empSPR. reflexivity. }
          { go_crazy'. go_crazy'. go_crazy'. congruence. } }
        { generalize (e_star e e_true); intros.
          consider (exprD' us tvs e0 SL); intros; forward; repeat go_crazy'; inv_all; subst.
          intros. rewrite H6. rewrite H0. rewrite landtrueL. reflexivity. }
        { consider (exprD' us tvs (e_and e_true (e_star e e_emp)) SL); intros;
          forward; repeat go_crazy; inv_all; subst.
          { intros.
            rewrite H6. rewrite H0. rewrite H8. rewrite H2.
            rewrite empSPR. rewrite landtrueL. reflexivity. }
          { go_crazy'. go_crazy'. congruence. } }
        { consider (exprD' us tvs e SL); intros; intros; forward;
          repeat go_crazy'; inv_all; subst.
          consider (exprD' us tvs (e_and e (e_star e_emp e_true)) SL);
            intros.
          { do 5 go_crazy'. inv_all; subst.
            rewrite H8. rewrite H10. rewrite H0. rewrite H2.
            rewrite empSPL. rewrite landtrueR. reflexivity. }
          { go_crazy'. go_crazy'. congruence. } }
        { consider (exprD' us tvs (e_and e (e_star e_emp e_emp)) SL); intros;
          forward; repeat go_crazy; inv_all; subst; intros.
          { rewrite H6; clear H6. rewrite H8. rewrite H12.
            rewrite H2. rewrite empSPL. reflexivity. }
          { go_crazy'. go_crazy'. } }
        { consider (exprD' us tvs (e_and e_true (e_star e_emp e_true)) SL);
          intros; forward; repeat go_crazy; inv_all; subst.
          { subst. rewrite H8. rewrite H10. rewrite H2.
            rewrite empSPL.
            { split. apply landR; reflexivity. apply landL1. reflexivity. } }
          { go_crazy'. go_crazy'. congruence. } }
        { consider (exprD' us tvs (e_and e_true (e_star e_emp e_emp)) SL);
          intros; forward; repeat go_crazy; inv_all; subst; intros.
          { rewrite H8. rewrite H10. rewrite H2.
            rewrite H0. rewrite empSPL. rewrite landtrueL. reflexivity. }
          { go_crazy'. go_crazy'. } } }
      { destruct o; destruct star_true0; simpl;
        match goal with
          | |- match _ with None => match ?X with _ => _ end | _ => _ end =>
            consider X; intros; forward;
            repeat go_crazy; inv_all; subst; intros
        end; try solve [ do 2 go_crazy'; congruence ].
        { rewrite H6. rewrite H8. rewrite H0.
          rewrite ltrue_sep. rewrite landtrueR. reflexivity. }
        { rewrite H6. rewrite H8. rewrite H2. rewrite H0.
          rewrite empSPR. rewrite landtrueR. reflexivity. }
        { subst. rewrite H8. rewrite H10. rewrite H0.
          rewrite ltrue_sep. rewrite landtrueR. reflexivity. }
        { subst. rewrite H8. rewrite H10. rewrite H0. rewrite H2.
          rewrite empSPR. rewrite landtrueR. reflexivity. } }
    Qed.
**)