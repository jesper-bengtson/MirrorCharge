Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Nat.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.provers.DefaultProver.
Require Import MirrorCore.Subst.FMapSubst.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCharge.SynSepLog.
Require Import MirrorCharge.SepLogFold.
Require Import MirrorCharge.Imp.Reify.
Require MirrorCharge.Imp.Imp.
Require Import MirrorCharge.Imp.Syntax.
Require Import MirrorCharge.Imp.ImpTac.
Require Import MirrorCharge.Imp.STacCancel.

Set Implicit Arguments.
Set Strict Implicit.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance Expr_expr.

Fixpoint get_alls (e : expr typ func) : list typ * expr typ func :=
  match e with
    | ExprCore.App (@ExprCore.Inj (inr (ILogicFunc.ilf_forall t tyProp)))
                   (ExprCore.Abs _ e) =>
      let (alls,e) := get_alls e in
      (t :: alls, e)
    | _ => (nil, e)
  end.

Fixpoint get_impls (e : expr typ func) : list (expr typ func) * expr typ func :=
  match e with
    | ExprCore.App (ExprCore.App (Inj (inr (ILogicFunc.ilf_impl tyProp))) P) Q =>
      let (impls,e) := get_impls Q in
      (P :: impls,e)
    | _ => (nil, e)
  end.

Definition convert_to_lemma (e : expr typ func)
: lemma typ (expr typ func) (expr typ func) :=
  let (alls, e) := get_alls e in
  let (impls, e) := get_impls e in
  {| vars := rev alls
   ; premises := impls
   ; concl := e |}.

Ltac reify_lemma e :=
  match type of e with
    | ?T =>
      (let k e :=
           let e := constr:(convert_to_lemma e) in
           let e := eval unfold convert_to_lemma in e in
           let e := eval simpl in e in
           refine e
       in
       reify_expr Reify.reify_imp k [ True ] [ T ])
  end.

(*
Definition to_skip : lemma typ (expr typ func) (expr typ func) :=
{| vars     := tyLProp :: tyCmd :: tyLProp :: tyLProp :: tySProp :: nil
 ; premises := (Var 4 |- {{ Var 0 }} (Var 1) {{ Var 3 }}) ::
               (Var 4 |- embed ((Var 2 : texp tyLProp) |- (Var 3))) :: nil
 ; concl    := (Var 4 |- {{ Var 0 }} (Var 1) {{ Var 2 }}) : expr _ _
 |}.

Eval hnf in test_lemma to_skip.
*)

(** Skip **)
Definition Assign_seq_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Imp.Assign_seq_rule.
Defined.
Definition Assign_tail_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Imp.Assign_tail_rule.
Defined.

Definition Read_seq_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Imp.Read_seq_rule.
Defined.
Definition Read_tail_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Imp.Read_tail_rule.
Defined.

Definition Write_seq_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Imp.Write_seq_rule.
Defined.
Definition Write_tail_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Imp.Write_tail_rule.
Defined.

Definition Skip_seq_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Imp.Skip_seq_rule.
Defined.
Definition Skip_tail_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Imp.Skip_tail_rule.
Defined.

Definition Assert_seq_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Imp.Assert_seq_rule.
Defined.
Definition Assert_tail_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Imp.Assert_tail_rule.
Defined.

Definition SeqA_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Imp.SeqA_rule.
Defined.

Definition triple_exL_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Imp.triple_exL.
Defined.

Definition triple_pureL_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Imp.triple_pureL.
Defined.
