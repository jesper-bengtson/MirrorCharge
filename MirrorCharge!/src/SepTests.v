Require Import MirrorCore.Ext.Expr.
(** Charge **)
Require Import ILogic BILogic ILEmbed.
(** MirrorCharge **)
Require Import ILogicFunc.
Require Import OrderedCanceller.
Require Import CancellerTac.

Add ML Path "../plugins".
Add ML Path "plugins".
Declare ML Module "reify_ILogicFunc_plugin".

Require Import Checkless.Checkless.
Require Import Reify. (** Note: this is from MirrorCharge **)

Set Implicit Arguments.
Set Strict Implicit.

(** Test cases for the core of separation logic **)
Section SepTests.
  Variable SL : Type.
  Context {ILOps} {ILogic_SL : @ILogic SL ILOps}.
  Context {BILO} {BILogic_SL : @BILogic SL ILOps BILO}.
  Context `{Embed_SL : EmbedOp Prop SL}.
  Context {PureOp : @Pure.PureOp SL}.
  Context {Pure : Pure.Pure PureOp}.
  Context {Pure_true : Pure.pure ltrue}.

  Definition sepSP' := @sepSP _ BILO.
  Definition empSP' := @empSP _ BILO.

  Ltac prep := intros;
    repeat match goal with
             | |- exists x , _ => eexists
           end;
    change (@sepSP _ BILO) with sepSP';
    change (@empSP _ BILO) with empSP'.

  Ltac prove_tcs :=
    repeat (first [ solve [ constructor ]
                  | (constructor; [ solve [ simpl; eauto with typeclass_instances ] | ]) ]).

  Definition seed_types : list (option Type) :=
    Some SL :: nil.
  Definition seed_funcs : list (option (@sigT Type (fun x => x))) :=
    Some (@existT _ _ _ sepSP) :: Some (@existT _ _ SL empSP) :: nil.
  Definition seed_logics : list (@sigT Type ILogicOps) :=
    (@existT _ _ SL ILOps) :: nil.

  Fixpoint types_repr (overlay onto : types) : types :=
    match overlay with
      | TEemp => onto
      | TEbranch l e r =>
        TEbranch (types_repr l match onto with
                                 | TEemp => TEemp
                                 | TEbranch l _ _ => l
                               end)
                 (match e with
                    | Some e => Some e
                    | None => match l with
                                | TEemp => None
                                | TEbranch _ x _ => x
                              end
                  end)
                 (types_repr r match onto with
                                 | TEemp => TEemp
                                 | TEbranch _ _ r => r
                               end)
    end.

  Fixpoint list_to_pmap' {T} (ls : list (option T)) (n : positive) (acc : MapPositive.PositiveMap.t T)
  : MapPositive.PositiveMap.t T :=
    match ls with
      | nil => acc
      | x :: ls =>
        list_to_pmap' ls (Pos.succ n)
                      match x with
                        | None => acc
                        | Some x => MapPositive.PositiveMap.add n x acc
                      end
    end.
  Definition list_to_pmap {T} (ls : list (option T)) : MapPositive.PositiveMap.t T :=
    list_to_pmap' ls 1%positive (MapPositive.PositiveMap.empty _).

  Definition seed_types' : types :=
    Eval compute in list_to_types seed_types.
  Definition seed_funcs' ts : fun_map (types_repr seed_types' ts) :=
    Eval cbv beta iota zeta delta
         [ Pos.succ list_to_pmap list_to_pmap' MapPositive.PositiveMap.add ]
    in
    let tySL := tyType 1%positive in
    list_to_pmap
      ((Some {| ftype := tyArr tySL (tyArr tySL tySL)
              ; fdenote := sepSP |}) ::
       (Some {| ftype := tySL
              ; fdenote := empSP |}) :: nil).
  Definition seed_logics' ts : list (tc_logic_opt (types_repr seed_types' ts)) :=
    let tySL := tyType 1%positive in
    (@Build_tc_logic_opt (types_repr seed_types' ts) tySL ILOps :: nil).

  Definition CSL :=
    Build_ConcreteSepLog (fref 1%positive) (fref 2%positive).

  Ltac cancel :=
    match goal with
      | |- ?X |-- ?Y =>
        let k t f l us lhs rhs :=
            idtac us ;
            let tySLV := constr:(tyType 1%positive) in
            let tsV := t in
            let fsV := f in
            let lV := fresh in
            pose (lV := @tc_map_to_logic_ops tsV l) ;
            let emV := fresh "embed" in
            pose (emV := @embed_map_to_embed_ops tsV nil) ;
            let lhsV := fresh "lhs" in
            pose (lhsV := lhs) ;
            let rhsV := fresh "rhs" in
            pose (rhsV := rhs) ;
            let tcOk := fresh in
            assert (tcOk : @tc_mapOk tsV l) by prove_tcs ;
            let embedOk := fresh in
            assert (embedOk : embed_mapOk l nil) by prove_tcs ;
            let usV := us in
            let vsV := fresh in
            pose (vsV := @nil _ : EnvI.env (typD tsV)) ;
            let x := fresh in
            change (@canceller_post t f lV emV tySLV ILOps usV vsV lhsV rhsV) ;
            let solver :=
                constr:(the_canceller (@RSym_func tsV fsV lV emV) tySLV
                                      (SynSepLog_ConcreteSepLog_smart tySLV CSL)
                                      (SepLogSpec_ConcreteSepLog CSL)
                                      (EnvI.typeof_env usV) (EnvI.typeof_env vsV) lhs rhs
                                      (FMapSubst.SUBST.subst_empty ilfunc))
            in
            let solver_red :=
                eval cbv beta iota zeta delta
                     [ EnvI.typeof_env List.map projT1 usV vsV ] in solver in
            let solved := eval vm_compute in solver_red in
            match solved with
              | (?lhs', ?rhs', ?sub') =>
                let lhs'V := fresh in
                pose (lhs'V := lhs') ;
                let rhs'V := fresh in
                pose (rhs'V := rhs') ;
                let sub'V := fresh in
                pose (sub'V := sub') ;
                cut (@canceller_pre t f lV emV tySLV ILOps usV vsV lhs'V rhs'V sub'V) ;
                [ exact_no_check (@apply_the_canceller
                                    tsV fsV lV emV
                                    (@tc_mapOk_to_logic_opsOk tsV l tcOk)
                                    (@embed_mapOk_to_embed_opsOk tsV l nil embedOk)
                                    tySLV ILOps (@eq_refl _ _) BILO BILogic_SL
                                    PureOp Pure Pure_true
                                    CSL
                                    (@Build_ConcreteSepLogOk
                                       tsV fsV lV emV tySLV
                                       BILO CSL
                                       (fun us tvs => @eq_refl _ _)
                                       (fun us tvs => @eq_refl _ _))
                                    usV vsV lhsV rhsV lhs'V rhs'V sub'V
                                    (@eq_refl _ (lhs'V,rhs'V,sub'V) <: (solver = (lhs'V,rhs'V,sub'V)))
                                 )
                | cbv beta iota zeta delta
                      [ canceller_pre exprD EnvI.split_env lhs'V rhs'V sub'V tsV fsV lV emV usV  vsV exprD'
                        SymI.typeof_sym typ_cast_typ RSym_ilfunc
                        typeof_func embed tc_map_to_logic_ops logics typ_eq_odec
                        positive_eq_odec SymI.symAs TypesI.type_cast RType_typ
                        nat_eq_odec MapPositive.PositiveMap.find
                        ftype fdenote SymI.symD
                        funcD
                        Subst.substD FMapSubst.SUBST.SubstOk_subst
                        FMapSubst.SUBST.subst_substD
                        FMapSubst.SUBST.env FMapSubst.SUBST.raw_substD
                        FMapSubst.MAP.fold
                        FMapSubst.MAP.this FMapSubst.MAP.Raw.fold
                        nth_error value error EnvI.lookupAs ExprI.exprD' Expr_expr
                        ExprDI.nth_error_get_hlist_nth projT1 projT2
                        HList.hlist_hd HList.hlist_tl
                        (** For Raw **)
                        Subst2.substD RawSubst2.SubstOk_list_subst RawSubst2.substD_for_domain
                        Subst2.lookup Subst2.domain List.map
                        RawSubst2.Subst_list_subst RawSubst2.list_subst_domain
                        RawSubst2.list_subst_domain' fold_left
                        RawSubst2.list_subst_lookup
                      ] ;
                  try clear lhs'V rhs'V lhsV rhsV sub'V tsV fsV l lV emV vsV usV embedOk tcOk
                ]
            end
        in
        let stypes := eval cbv delta [ seed_types ] in seed_types in
        let sfuncs := eval cbv delta [ seed_funcs ] in seed_funcs in
        let slogics := eval cbv delta [ seed_logics ] in seed_logics in
        reify_expr ~types:stypes ~funcs:sfuncs ~logics:slogics [ X Y ] k
        (** TODO: It is important that I can pass pre-reified environments
         ** to [reify_expr].
         **)
    end.

  (** Propositional **)
  Variables P Q R S T : SL.

  Goal P |-- P.
  Proof.
    prep.
    cancel.
    reflexivity.
  Qed.

  Goal P ** Q |-- Q ** P.
  Proof.
    prep.
    cancel.
    reflexivity.
  Qed.

  Goal P ** Q ** R ** S ** T |-- T ** S ** R ** Q ** P.
  Proof.
    prep.
    cancel.
    reflexivity.
  Qed.

  (** Predicate **)
  Variable PT : nat -> nat -> SL.

  Goal PT 1 1 |-- PT 1 1.
  Proof.
    prep.
    cancel.
    reflexivity.
  Qed.

  Goal forall w x y z,
         PT w x ** PT x y ** PT y z |-- PT y z ** PT x y ** PT w x.
  Proof.
    prep.
    cancel.
    reflexivity.
  Qed.

  (** With Meta-variables **)
  Goal forall w x, exists x',
         PT w x |-- PT w x'.
  Proof.
    prep.
    cancel.
    split; reflexivity.
    Set Printing Implicit.
    Show Proof.
  Time Qed.

  Goal forall w x y z, exists x' y' z',
         PT w x ** PT x y ** PT y z |-- PT y' z' ** PT x' y' ** PT w x'.
  Proof.
    prep.
    cancel. (** This is because the ordering heuristic is really bad **)
  Abort.

  (** With premises **)
  Goal forall w x y, x = y ->
                     PT w x |-- PT w y.
  Proof.
    prep.
  Abort.

  (** With pure predicates **)
  Goal forall w x y,
         PT w x //\\ embed (x = y) |-- PT w y.
  Proof.
    prep.
  Abort.

  Goal forall w x y,
         PT w x //\\ embed (x = y) |-- PT w y //\\ embed (x = y).
  Proof.
    prep.
  Abort.

  Goal forall w x y z, exists z',
         (PT w x ** PT x z) //\\ embed (x = y) |-- (PT y z' ** PT w y) //\\ embed (x = y).
  Proof.
    prep.
  Abort.

  (** With existentials **)
  Goal forall w x,
         PT w x |-- lexists (fun y : nat => PT w y).
  Proof.
    prep.
  Abort.

  Goal forall w x y,
         PT w x ** PT x y |-- Exists x : nat, PT w x ** Exists y : nat, PT x y.
  Proof.
    prep.
  Abort.

  Goal forall w x y,
         PT w x ** PT x y |-- Exists x, Exists y, PT x y ** PT w x.
  Proof.
    prep.
  Abort.

  Goal forall w x y,
         PT w x ** PT x y |-- Exists x, x.
  Proof.
    prep.
  Abort.

  Goal forall w x y,
         PT w x ** PT x y |-- (Exists x, x) ** PT x y.
  Proof.
    prep.
  Abort.

  Goal forall w x y,
         PT w x ** PT x y |-- (Exists x, x) ** PT w x.
  Proof.
    prep.
  Abort.

  (** With existentials & pure premises **)
  Goal forall w x y,
         PT w x ** PT x y |--
         Exists w', Exists x', Exists y', Exists z',
           PT w' x' ** PT y' z' //\\ embed (w = w') //\\ embed (y' = x).
  Proof.
    (** This is potentially very difficult because you have to propagate information
     ** from the right-hand-side pure facts before solving the unification problem.
     **)
    prep.
  Abort.

End SepTests.