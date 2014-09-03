Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.STac.STac.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCharge.ILogicFunc.
Require Import MirrorCharge.OrderedCanceller.
Require Import MirrorCharge.BILNormalize.
Require Import MirrorCharge.SynSepLog.
Require Import MirrorCharge.SepLogFold.
Require Import MirrorCharge.Imp.Syntax.

Set Implicit Arguments.
Set Strict Implicit.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance Expr_expr.

Local Notation "a @ b" := (@App typ _ a b) (at level 30).
Local Notation "a 'p@' b" := (App a b) (at level 30).
Local Notation "\ t -> e" := (@Abs typ _ t e) (at level 40).
Local Notation "'Ap' '[' x , y ']'" := (Inj (inl (inr (pAp x y)))) (at level 0).
Local Notation "'Pure' '[' x ']'" := (Inj (inl (inr (pPure x)))) (at level 0).
Local Notation "x '|-' y" :=
  (App (App (Inj (inr (ilf_entails tySProp))) x) y) (at level 10).
(** function_spec **)
Local Notation "'{{'  P  '}}'  c  '{{'  Q  '}}'" :=
  (Inj (inl (inl 8%positive)) @ P @ c @ Q) (at level 20).
Local Notation "c1 ;; c2" := (Inj (inl (inl 2%positive)) @ c1 @ c2) (at level 30).
Local Notation "a >> b" := (tyArr a b) (at level 31,right associativity).

Fixpoint lentails_conjunct T (P : expr typ func -> option T) (e : expr typ func)
: option T.
  (** This function will look through e to find a conjunct that matches P.
   ** This is essentiall [assumption] for ILogic
   **)
Admitted.

Definition match_spec (f : expr typ func) (P : expr typ func)
: option (expr typ func * expr typ func) :=
  match P with
    | Inj (inl (inl idx)) p@ P' p@ n p@ Q' =>
      if idx ?[ eq ] 8%positive then
        if n ?[ eq ] f then
          Some (P', Q')
        else
          None
      else
        None
    | _ => None
  end.

(** TODO: replace this with the actual unification algorithm.
 ** - This is where packaging is likely to make a big difference in usability.
 **)
Axiom exprUnify : tenv typ ->
       tenv typ ->
       nat -> subst -> expr typ func -> expr typ func -> typ -> option subst.

Definition solve_spec (tus tvs : tenv typ) (s : subst)
           (G name P Q : expr typ func)
: Result typ (expr typ func) subst :=
  match lentails_conjunct (match_spec name) G with
    | None => @Fail _ _ _
    | Some (P',Q') =>
      match exprUnify tus tvs 0 s P P' (tyNat >> tyLProp) with
        | None => @Fail _ _ _
        | Some s' =>
          match exprUnify tus tvs 0 s Q Q' (tyNat >> tyLProp) with
            | None => @Fail _ _ _
            | Some s'' =>
              @Solved _ _ _ nil nil s''
          end
      end
  end.

Definition stac_solve_get_spec : stac typ (expr typ func) subst :=
(** NOTE: Doing this pattern match modularly might be important **)
  fun tus tvs s hyps goal =>
    match goal with
      | G |- Inj (inl (inl idx)) p@ P p@ f p@ Q =>
        if idx ?[ eq ] 8%positive then
          solve_spec tus tvs s G f P Q
        else
          @Fail _ _ _
      | _ => @Fail _ _ _
    end.