Require Import MirrorCore.Lemma.
Require Import MirrorCharge.Imp.Reify.
Require MirrorCharge.Imp.Imp.
Require Import MirrorCharge.Imp.Syntax.
Require Import MirrorCore.Util.Nat.
Require Import MirrorCore.ExprDAs.

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

Section rn.
  Variable mx : nat.

  Fixpoint renumber (skip : nat) (e : expr typ func) : expr typ func :=
    match e with
      | ExprCore.Var n =>
        match Nat.lt_rem n skip with
          | None => e
          | Some n' => Var (mx - 1 - n' + skip)
        end
      | App a b => App (renumber skip a) (renumber skip b)
      | Abs t x => Abs t (renumber (S skip) x)
      | Inj _
      | ExprCore.UVar _ => e
    end.
End rn.

Definition convert_to_lemma (e : expr typ func)
: lemma typ (expr typ func) (expr typ func) :=
  let (alls, e) := get_alls e in
  let (impls, e) := get_impls e in
  let lalls := length alls in
  {| vars := alls
   ; premises := map (renumber lalls 0) impls
   ; concl := renumber lalls 0 e |}.

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

(** Skip **)
Definition Assign_seq_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Imp.Assign_seq_rule.
Defined.
Goal Lemma.lemmaD (exprD'_typ0 (T:=Prop)) nil nil Assign_seq_lemma.
exact Imp.Assign_seq_rule.
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

Definition go_lower_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Imp.go_lower.
Defined.
Definition embed_ltrue_lemma : lemma typ (expr typ func) (expr typ func).
reify_lemma Imp.embed_ltrue.
Defined.
