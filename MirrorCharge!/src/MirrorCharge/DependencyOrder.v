Require Import ExtLib.Data.Fun.
Require Import ExtLib.Tactics.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.SubstI.
Require Import MirrorCore.EnvI.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.ExprSem.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.AppN.
Require Import ILogic BILogic Pure.
Require Import MirrorCharge.BILNormalize.
Require Import MirrorCharge.SynSepLog.
Require Import MirrorCharge.OrderedCanceller.

Set Implicit Arguments.
Set Strict Implicit.

Section better_ordering.
  Variable typ : Type.
  Variable RType_typ : RType typ.
  Variable Typ2_Fun : Typ2 _ Fun.
  Variable func : Type.
  Variable RSym_func : RSym func.

  Variable tySL : typ.
  Variable ILogicOps_SL : ILogicOps (typD tySL).
  Variable BILOperators_SL : BILOperators (typD tySL).
  Hypothesis ILogic_SL : @ILogic _ ILogicOps_SL.
  Hypothesis BILogic_SL : @BILogic _ ILogicOps_SL BILOperators_SL.

  (** dependencies are like [a -> b] **)
  (** put things in as soon as they are solvable **)

  (** NOTE: These are like a functor **)
  Variable dependency : Type.
  Variable dep_satisfied : dependency -> dependency -> option dependency.
  Variable dep_for : expr typ func -> dependency.

  Inductive Decorated :=
  | DPure (_ : dependency) (_ : expr typ func) (_ : Decorated)
  | DImpure (_ : dependency) (f : expr typ func) (xs : list (expr typ func)) (_ : Decorated)
  | DFrame (_ : dependency) (_ : expr typ func) (xs : list (expr typ func)) (_ : Decorated)
  | DEmp
  | DTru.

  Fixpoint forget_Decorated (d : Decorated) : Conjuncts typ func :=
    match d with
      | DPure _ p d => Pure p (forget_Decorated d)
      | DImpure _ f xs d => Impure f xs (forget_Decorated d)
      | DFrame _ f xs d => Frame f xs (forget_Decorated d)
      | DEmp => Emp _ _
      | DTru => Tru _ _
    end.

  Fixpoint insert_into (d : dependency) (dec : Decorated)
           (here : Decorated -> Decorated)
  : Decorated :=
    match dec with
      | DEmp => here DEmp
      | DTru => here DTru
      | DFrame d' xs ys rst => here (DFrame d' xs ys rst)
      | DPure d' P rst =>
        match dep_satisfied d' d with
          | None => here (DPure d' P rst)
          | Some d => DPure d' P (insert_into d rst here)
        end
      | DImpure d' f xs rst =>
        match dep_satisfied d' d with
          | None => here (DImpure d' f xs rst)
          | Some d => DImpure d' f xs (insert_into d rst here)
        end
    end.

  Definition better_order_decorated (c : conjunctives typ func)
  : Decorated :=
    List.fold_right (fun x acc =>
                       match fst x with
                         | UVar _ =>
                           let d := dep_for (apps (fst x) (snd x)) in
                           insert_into d acc (DFrame d (fst x) (snd x))
                         | _ =>
                           let d := dep_for (apps (fst x) (snd x)) in
                           insert_into d acc (DImpure d (fst x) (snd x))
                       end)
                    (List.fold_right (fun x acc =>
                                        let d := dep_for x in
                                        insert_into d acc (DPure d x))
                                     (if c.(star_true) then DTru else DEmp)
                                     c.(pure))
                    c.(spatial).


  Definition better_order (c : conjunctives typ func) : Conjuncts typ func :=
    forget_Decorated (better_order_decorated c).

  Variable SSL : SynSepLog typ func.
  Variable SSLO : SynSepLogOk _ _ _ _ _ SSL.

  Variable PureOp_SL : @Pure.PureOp (typD tySL).
  Variable Pure_SL : Pure.Pure PureOp_SL.
  Hypothesis Pure_ltrue : Pure.pure ltrue.
  Hypothesis Pure_land : forall a b,
                           Pure.pure a -> Pure.pure b -> Pure.pure (a //\\ b).

(*
  Theorem simple_orderOk
  : @order_spec ts func _ tySL ILogicOps_SL SSL _ simple_order.
  Proof.
    red.
    intros; destruct c; simpl.
    unfold conjunctives_to_expr_star, simple_order; simpl.
    match goal with
      | |- match ?X with _ => _ end =>
        consider X; intros
    end.
    { repeat go_crazy SSL SSLO.
      revert H0. generalize dependent x1.
      induction spatial.
     { simpl. admit. }
      { simpl. intros.
        eapply exprD'_iterated_base_cons_Some in H0; eauto.
        destruct H0 as [ ? [ ? [ ? [ ? ? ] ] ] ].
        assert (forall us vs,
                  x0 us vs -|- x4 us vs ** x2 us vs).
        { intros. rewrite H3. rewrite H5.
          specialize (fun z => IHspatial _ z H4).
          admit. }
        { admit. } } }
    { forward.
(*      repeat go_crazy SSL SSLO. *)
      admit. }
  Qed.
*)
End better_ordering.
