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
Require Import ExtLib.Core.RelDec.

Set Implicit Arguments.
Set Strict Implicit.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance Expr_expr.


Definition sls (ty : typ)  : SepLogSpec typ func :=
{| is_pure := fun (e : expr typ func) =>
                match e with
                  | Inj (inr (ilf_true _))
                  | Inj (inr (ilf_false _)) => true
                  | _ => false
                end
 ; is_emp := fun e => false
 ; is_star := fun (e : expr typ func) =>
                match e with
                  | Inj (inl (inr (pStar ty'))) =>
                    ty ?[eq] ty'
                  | _ => false
                end
 |}.

Let ssl (ty : typ) : SynSepLog typ func :=
{| e_star := fun l r =>
               match l with
                 | Inj (inl (inr (pEmp _))) => r
                 | _ => match r with
                          | Inj (inl (inr (pEmp _))) => l
                          | _ => lstar ty l r
                        end
               end
 ; e_emp := lemp ty
 ; e_and := fun l r =>
              match l with
                | Inj (inr (ilf_true _)) => r
                | _ => match r with
                         | Inj (inr (ilf_true _)) => l
                         | _ => land ty l r
                       end
              end
 ; e_true := ltrue ty
 |}.

Definition is_solved (e1 e2 : conjunctives typ func) : bool :=
  match e1 , e2 with
    | {| spatial := e1s ; star_true := t ; pure := _ |}
    , {| spatial := nil ; star_true := t' ; pure := nil |} =>
      if t' then
        (** ... |- true **)
        true
      else
        (** ... |- emp **)
        if t then false else match e1s with
                               | nil => true
                               | _ => false
                             end
    | _ , _ => false
  end.

Section the_canceller.
  Variable subst : Type.
  Variable Subst_subst : Subst subst (expr typ func).
  Variable SubstUpdate_subst : SubstUpdate subst (expr typ func).

  Variable ty : typ.

  Let doUnifySepLog (tus tvs : EnvI.tenv typ) (s : subst) (e1 e2 : expr typ func)
  : option subst :=
    @exprUnify subst typ func _ _ _ _ _ 10 tus tvs 0 e1 e2 ty s.

  Definition eproveTrue (s : subst) (e : expr typ func) : option subst :=
    match e with
      | Inj (inr (ilf_true _)) => Some s
      | _ => None
    end.

  Definition the_canceller tus tvs (lhs rhs : expr typ func)
             (s : subst)
  : (expr typ func * expr typ func * subst) + subst:=
    let full := sls ty in
    match @normalize typ _ _ func _ full tus tvs ty lhs
        , @normalize typ _ _ func _ full tus tvs ty rhs
    with
      | Some lhs_norm , Some rhs_norm =>
        match lhs_norm tt , rhs_norm tt with
          | Some lhs_norm , Some rhs_norm =>
            let ssl := ssl ty in
            let '(lhs',rhs',s') :=
                OrderedCanceller.ordered_cancel
                  (doUnifySepLog tus tvs) eproveTrue
                  ssl
                  (simple_order (func:=func)) lhs_norm rhs_norm s
            in
            if is_solved lhs' rhs' then
              inr s'
            else
              inl (conjunctives_to_expr ssl lhs',
                   conjunctives_to_expr ssl rhs',
                   s')
          | _ , _ => inl (lhs, rhs, s)
        end
      | _ , _ => inl (lhs, rhs, s)
    end.
End the_canceller.


Definition stac_cancel : rtac typ (expr typ func) :=
  fun tus tvs _ _ ctx sub e =>
    match e with
      | App (App (Inj (inr (ilf_entails z))) L) R =>
        match the_canceller _ _ z tus tvs L R sub with
          | inl (l,r,s') =>
            let e' :=
                App (App (Inj (inr (ilf_entails z))) l) r
            in
            More_ s' (GGoal e')
          | inr s' => @Solved _ _ _ s'
        end
      | _ => More_ sub (GGoal e)
    end.
