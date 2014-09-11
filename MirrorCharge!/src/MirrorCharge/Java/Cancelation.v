Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.STac.STac.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Subst.CascadeSubst.
Require Import MirrorCharge.ILogicFunc.
Require Import MirrorCharge.OrderedCanceller.
Require Import MirrorCharge.BILNormalizeEx.
Require Import MirrorCharge.SynSepLog.
Require Import MirrorCharge.SepLogFold.
Require Import MirrorCharge.Java.Syntax.

Set Implicit Arguments.
Set Strict Implicit.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance Expr_expr.

(** NOTE: this is for [locals -> HProp] **)
Definition sls : SepLogFoldEx.SepLogSpec typ func :=
{| SepLogFoldEx.is_pure := fun (e : expr typ func) =>
                match e with
          (*        | mkTrue [_]
                  | mkFalse [_] => true
                  | App (App (Inj (inl (inr (pAp _ _)))) (App (Inj (inl (inr (pConst _)))) (Inj (inr (ilf_embed tyProp _))))) _ => true*)
                  | _ => false
                end
 ; SepLogFoldEx.is_emp := fun e => false
 ; SepLogFoldEx.is_star := fun (e : expr typ func) =>
                match e with
                  | fStar [_] => true
                  | _ => false
                end
 ; SepLogFoldEx.is_and := fun (e : expr typ func) =>
                match e with
                  | fAnd [_] => true
                  | _ => false
                end
 ; SepLogFoldEx.is_ex := fun (e : expr typ func) =>
                match e with
                  | fExists [t, _] => Some t
                  | _ => None
                end
 |}.

About normalize.

Section inst_2.
  Variable lookup : uvar -> nat -> option (expr typ func).

  Fixpoint instantiate (u : nat) (e : expr typ func)
  : expr typ func :=
    match e with
      | Var _ => e
      | Inj _ => e
      | App l r => App (instantiate u l) (instantiate u r)
      | Abs t e =>
        Abs t (instantiate (S u) e)
      | UVar uv =>
        match lookup uv u with
          | None => UVar uv
          | Some e => e
        end
    end.

  Variable check : uvar -> bool.
  Fixpoint mentions_any (e : expr typ func) : bool :=
    match e with
      | Var _ => false
      | Inj _ => false
      | App l r => if mentions_any l then true else mentions_any r
      | Abs t e => mentions_any e
      | UVar uv => check uv
    end.
End inst_2.

Let Subst_CS : SubstI.Subst (CascadeSubst subst subst) (expr typ func) :=
  @Subst_CascadeSubst (expr typ func) subst _ subst _ (@lift typ func 0).
Let SubstU_CS : SubstI.SubstUpdate (CascadeSubst subst subst) (expr typ func) :=
  @SubstUpdate_CascadeSubst (expr typ func) subst _ _ subst _
                            (@lift typ func 0)
                            (@lower typ func 0)
                            mentions_any
                            instantiate.
Local Existing Instance Subst_CS.
Local Existing Instance SubstU_CS.

Let doUnifySepLog (tus tvs : EnvI.tenv typ) (s : CascadeSubst subst subst) (e1 e2 : expr typ func)
: option (CascadeSubst subst subst) :=
  @exprUnify _ typ func _ _ _ _ _ 10 tus tvs 0 s e1 e2 tySasn.

Let ssl : SynSepLog typ func :=
{| e_star := fun l r =>
               let result := mkStar [tySasn, l, r] in
               let nested_match := match r with
		                           | mkEmp [_] => l
		                           | _ => result
		                           end in
               match l with
                 | mkEmp [_] => r
                 | _ => nested_match
               end
 ; e_emp := mkEmp [tySasn]
 ; e_and := fun l r =>
 			  let result := mkAnd [tySasn, l, r] in
 			  let nested_match := match r with
		                          | mkTrue [_] => l
		                          | _ => result
		                          end in
              match l with
                | mkEmp [_] => r
                | _ => nested_match
              end
 ; e_true := mkTrue [tySasn]
 |}.

Definition eproveTrue (s : CascadeSubst subst subst) (e : expr typ func)
: option (CascadeSubst subst subst) :=
  match e with
    | mkTrue [_] => Some s
    | _ => None
  end.

Definition is_solved (e1 e2 : BILNormalize.conjunctives typ func) : bool :=
  match e2 with
    | {| BILNormalize.spatial := nil
       ; BILNormalize.star_true := _
       ; BILNormalize.pure := nil |} => true
    | _ => false
  end.

Require Import ExtLib.Core.RelDec.

Fixpoint vars_to_uvars (skip count over : nat) (e : expr typ func)
: expr typ func :=
  match e with
    | Var v =>
      if v ?[ lt ] skip then Var v
      else if (v - skip) ?[ lt ] count then
             UVar (v - skip + over)
           else
             Var (v - count)
    | UVar u => UVar u
    | Inj i => Inj i
    | App l r => App (vars_to_uvars skip count over l)
                     (vars_to_uvars skip count over r)
    | Abs t e => Abs t (vars_to_uvars skip count over e)
  end.
Check instantiate.
Definition the_canceller tus tvs (lhs rhs : expr typ func)
           (s : subst)
: (expr typ func * expr typ func * subst) + subst:=
  match @normalize typ _ sls lhs
      , @normalize typ _ sls rhs
  with
    | Some lhs_norm , Some rhs_norm =>
      (** TODO: I need to build a new substitution **)
      let s' :=
          @over subst subst s (@SubstI.empty _ _ _)
                (length tus) (length lhs_norm.(exs))
      in
      let rhs_ucount := length rhs_norm.(exs) in
      let lhs_count := length lhs_norm.(exs) in
      let lifter e :=
          lift 0 lhs_count (vars_to_uvars 0 rhs_ucount (length tus) e)
      in
      let '(lhs',rhs',s') :=
          @OrderedCanceller.ordered_cancel
            typ func (CascadeSubst subst subst)
            (doUnifySepLog (tus ++ rhs_norm.(exs))
                           (lhs_norm.(exs) ++ tvs))
            eproveTrue
            ssl
            (simple_order (func:=func))
            {| BILNormalize.spatial := lhs_norm.(spatial)
             ; BILNormalize.pure := lhs_norm.(pure)
             ; BILNormalize.star_true := lhs_norm.(star_true) |}
            {| BILNormalize.spatial :=
                 map (fun e_es =>
                        let '(e,es) := e_es in
                        (lifter e, map lifter es)) rhs_norm.(spatial)
             ; BILNormalize.pure :=
                 map lifter rhs_norm.(pure)
             ; BILNormalize.star_true := rhs_norm.(star_true) |}
            s'
      in
      match SubstI.pull (length tus) (length rhs_norm.(exs)) s' with
        | None => inl (lhs, rhs, s)
        | Some s' =>
          if is_solved lhs' rhs' then
            inr (s'.(lowerSubst))
          else
            (*inl (conjunctives_to_expr ssl lhs',
                 conjunctives_to_expr ssl rhs',
                 s') *)
            inl (lhs, rhs, s)
      end
    | _ , _ => inl (lhs, rhs, s)
  end.

Definition stac_cancel : stac typ (expr typ func) subst :=
  fun tus tvs s hyps e =>
    match e with
      | mkEntails [tySasn, L, R] =>
        match the_canceller tus tvs L R s with
          | inl (l,r,s') =>
            let e' :=
                mkEntails [tySasn, l, r]
            in
            More tus tvs s hyps e'
          | inr s' => @Solved _ _ _ nil nil s'
        end
      | _ => More nil nil s hyps e
    end.