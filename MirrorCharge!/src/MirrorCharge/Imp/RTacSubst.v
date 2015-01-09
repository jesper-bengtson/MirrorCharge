Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.RTac.RTac.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCharge.ILogicFunc.
Require Import MirrorCharge.OrderedCanceller.
Require Import MirrorCharge.BILNormalize.
Require Import MirrorCharge.SynSepLog.
Require Import MirrorCharge.SepLogFold.
Require Import MirrorCharge.Imp.Syntax.
Require Import MirrorCharge.Tauto.
Require Import MirrorCharge.Imp.ImpTac.

Set Implicit Arguments.
Set Strict Implicit.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance Expr_expr.

Record Eq_spec : Type :=
{ as_eq : expr typ func -> option (typ * expr typ func * expr typ func) }.

Section subst.
  Variable eq_spec : Eq_spec.
  Variable ilspec : ILogicSpec typ func.

  Require Import ExtLib.Core.RelDec.

  Fixpoint find_in_list (n : nat) (ls : list (nat * expr typ func))
  : option (expr typ func) :=
    match ls with
      | nil => None
      | cons (n',e) ls =>
        if n ?[eq] n' then Some e else find_in_list n ls
    end.

  Section the_subst.
    Variable ss : list (nat * expr typ func).

    Fixpoint subst  (u : nat) (e : expr typ func)
    : expr typ func :=
      match e with
        | ExprCore.Var v =>
          match Nat.lt_rem v u with
            | None => Var v
            | Some k =>
              match find_in_list k ss with
                | None => e
                | Some e' => lift 0 u e'
              end
          end
        | ExprCore.UVar _
        | ExprCore.Inj _ => e
        | ExprCore.App l r => ExprCore.App (subst u l) (subst u r)
        | ExprCore.Abs t l => ExprCore.Abs t (subst (S u) l)
      end.
  End the_subst.

  Fixpoint gather (e : expr typ func)
  : expr typ func * list (nat * expr typ func) :=
    match eq_spec.(as_eq) e with
      | Some (t,l,r) =>
        match l with
          | ExprCore.Var v => (Syntax.ltrue tyProp, (v,r) :: nil)
          | _ =>
            match r with
              | ExprCore.Var v => (Syntax.ltrue tyProp, (v,l) :: nil)
              | _ => (e,nil)
            end
        end
      | None =>
        match e with
          | App (App bop l) r =>
            match ilspec.(as_logic) bop with
              | Some LAnd =>
                let (l',eqsl) := gather l in
                let (r',eqsr) := gather r in
                (App (App bop l') r', eqsl ++ eqsr)
              | Some LImpl =>
                let (l',eqsl) := gather l in
                (App (App bop l) (subst eqsl 0 r), nil)
              | Some LEntails =>
                let (l',eqsl) := gather l in
                (App (App bop l) (subst eqsl 0 r), nil)
              | _ => (e,nil)
            end
          | _ => (e,nil)
        end
    end.

  Definition subst_tac : imp_tac :=
    fun tus tvs _ _ ctx sub g =>
      let (g',_) := gather g in
      More_ sub (GGoal g').

End subst.
