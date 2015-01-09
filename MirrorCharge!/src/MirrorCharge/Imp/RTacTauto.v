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

Definition ILogicSpec_sym : ILogicSpec typ func :=
{| as_logic := fun e =>
                match e with
                  | Inj (inr (ILogicFunc.ilf_true _)) => Some LTrue
                  | Inj (inr (ILogicFunc.ilf_false _)) => Some LFalse
                  | Inj (inr (ILogicFunc.ilf_and _)) => Some LAnd
                  | Inj (inr (ILogicFunc.ilf_or _)) => Some LOr
                  | Inj (inr (ILogicFunc.ilf_impl _)) => Some LImpl
                  | Inj (inr (ILogicFunc.ilf_entails _)) => Some LEntails
                  | _ => None
                end
 |}.

Definition EmbedSpec_sym : EmbedSpec typ func :=
{| is_embed := fun e =>
                match e with
                  | Inj (inr (ILogicFunc.ilf_embed _ t)) => Some t
                  | _ => None
                end
 |}.

Definition floor (e : expr typ func) (from to : typ) : option (expr typ func) :=
  None.

Axiom todo : forall {T : Type}, T.

Definition tauto_tac : imp_tac :=
  fun tus tvs _ _ ctx sub e =>
    match e with
      | App (App (Inj (inr (ILogicFunc.ilf_entails t))) P) Q =>
        match learn ILogicSpec_sym P nil with
          | None => Solved sub
          | Some ps =>
            match Tauto.tauto_simplify tyProp ILogicSpec_sym EmbedSpec_sym floor _ ps Q t with
              | None => Solved sub
              | Some Q' =>
                More_ sub (GGoal (App (App (Inj (inr (ILogicFunc.ilf_entails t))) P) Q'))
            end
        end
      | _ => Fail
    end.

Theorem tauto_tac_sound : rtac_sound tauto_tac.
Admitted.