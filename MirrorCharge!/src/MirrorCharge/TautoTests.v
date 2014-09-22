Require Import MirrorCore.Ext.Expr.
Require Import ExtLib.Tactics.
Require Import MirrorCharge.ILogicFunc.
Require Import MirrorCharge.Tauto.

Add ML Path "../plugins".
Add ML Path "plugins".
Declare ML Module "reify_ILogicFunc_plugin".

Require Import MirrorCharge.Reify.

Set Implicit Arguments.
Set Strict Implicit.

(** Over Prop **)
Module PropTests.

  Definition null_floor : expr ilfunc -> typ -> typ -> option (expr ilfunc) :=
    fun _ _ _ => None.

  Fixpoint learn_all (ls : list (expr ilfunc)) (f : Facts) : Facts :=
    match ls with
      | nil => f
      | l :: ls => learn_all ls (learn l f)
    end.

  Definition tauto_call (ts : types) (gs : tc_map ts)
             (ls : list (expr ilfunc)) (goal : expr ilfunc) : bool :=
    @tauto ts (tc_map_to_logic_ops gs) null_floor (learn_all ls (Knows nil)) goal.

  Fixpoint implyEach (F : expr ilfunc -> Prop) (ls : list (expr ilfunc))
           (res : expr ilfunc) : Prop :=
    match ls with
      | nil => F res
      | l :: ls => F l -> implyEach F ls res
    end.

  Definition Provable_True :=
    fun (a : types) (b : Type) (c : SymI.RSym (typD a) b)
        (d e : EnvI.env (typD a)) (f : expr b) =>
      match exprD d e f tyProp with
        | Some x => x
        | None => True
      end.

  Theorem Apply_tauto_Prop
  : forall ts (fs : fun_map ts) (gs : tc_map ts) (es : embed_map ts),
      tc_mapOk gs -> embed_mapOk gs es ->
      forall us vs goal,
        @tauto_call ts gs nil goal = true ->
        @Provable_True ts ilfunc (@RSym_ilfunc_ctor ts fs gs es) us vs goal.
  Proof.
    intros.
    red.
    forward.
    generalize I.
    apply (fun floorOk Z =>
                  @tauto_sound ts fs _ _ (@tc_mapOk_to_logic_opsOk ts gs H)
                               (@embed_mapOk_to_embed_opsOk ts gs es H0)
                               null_floor floorOk
               goal tyProp (learn_all nil (Knows nil)) us vs
               True
               t H2 _ Z eq_refl H1).
    { red. inversion 1. }
    { (** TODO: this might not actually be true because it isn't working with
       ** the environments **)
      admit. }
  Qed.

  Ltac rtauto :=
    repeat match goal with
             | H : ?T |- _ =>
               match type of T with
                 | Prop => revert H
               end
           end;
    let prove_tcs :=
        repeat (first [ solve [ constructor ]
                      | (constructor; [ solve [ simpl; eauto with typeclass_instances ] | ]) ])
    in
    match goal with
      | |- ?X =>
        let k t f l us e :=
            let eV := fresh in
            pose (eV := e) ;
            let tcOk := fresh in
            assert (tcOk : @tc_mapOk t l) by  prove_tcs ;
            let embedOk := fresh in
            assert (embedOk : embed_mapOk l nil) by prove_tcs ;
            change (@Provable t (@RSym_ilfunc_ctor t f l nil) us nil eV) ;
            cut (@tauto_call t l nil eV = true) ;
            [ exact (@Apply_tauto_Prop t f l nil tcOk embedOk us nil eV)
            | try (vm_compute; reflexivity) ]
        in
        reify_expr [ X ] k
    end.

  Goal True.
  rtauto.
  Qed.

  Goal False -> False.
  rtauto.
  Qed.

  Goal forall P : Prop, False -> P.
  intro. rtauto.
  Qed.

  Goal forall P Q R S : Prop,
         P -> Q -> R -> S -> P /\ Q /\ R /\ S.
  intros P Q R S. Time rtauto.
  Qed.

  (** Can't solve this one yet b/c we don't have good handling for -> **)
  Goal forall P Q R S : Prop,
         (P -> Q) -> (Q -> R) -> (R -> S) -> P -> S.
  Abort.
End PropTests.