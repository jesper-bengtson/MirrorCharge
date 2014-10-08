Require Import MirrorCore.Lambda.ExprCore.
Require Import MirrorCore.Lambda.ExprD.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.ExprI.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Tactics.
Require Import MirrorCore.syms.SymSum.

Require Import MirrorCharge.AutoSetoidRewrite.

Set Implicit Arguments.
Set Strict Implicit.

Section SetoidRewrite.
  Context {typ func : Type}.

  Context {RType_typ : RType typ} {RelDec_typ_eq : RelDec (@eq typ)}
          {RelDecCorrect_typ_eq : RelDec_Correct RelDec_typ_eq}.
  
  Context {RelDec_func_eq : RelDec (@eq (expr typ func))}.

  Let Rbase := expr typ func.

  Definition m (T : Type) : Type :=
    rsubst Rbase -> option (T * rsubst Rbase).

  Definition rg_bind {T U} (a : m T) (b : T -> m U) : m U :=
    fun s => match a s with
               | None => None
               | Some (val,s') => b val s'
             end.
  Definition rg_fail {T} : m T := fun _ => None.
  Definition rg_ret {T} (v : T) : m T := fun s => Some (v, s).
  Definition rg_plus {T} (l r : m T) : m T :=
    fun s =>
      let v := l s in
      match v with
        | None => r s
        | Some _ => v
      end.
		
  Definition rw_type := expr typ func -> list (RG (expr typ func))
                        -> RG (expr typ func) -> m (expr typ func).

  Section interleave.
    Variables (rw rw' : rw_type -> rw_type).

    Fixpoint interleave (n : nat)
             (e : expr typ func) (rvars : list (RG (expr typ func)))
             (rg : RG (expr typ func)) : m (expr typ func) :=
      match n with
        | 0 => rg_fail
        | S n => rw (fun rs => rw' (fun e rvars rg rs => interleave n e rvars rg rs) rs) e rvars rg
      end.
  End interleave.

  Fixpoint rw_fix (n : nat)
    (rw : rw_type -> rw_type)
    (e : expr typ func) (rvars : list (RG Rbase)) (rg : RG Rbase)
    (rs : rsubst Rbase) : option (expr typ func * rsubst Rbase) :=
    match n with
      | 0 => Some (e,rs)
      | S n => rw (fun e rvars rg rs => rw_fix n rw e rvars rg rs) e rvars rg rs
    end.

  Definition sr_combine (f g : expr typ func -> list (RG (expr typ func)) -> RG (expr typ func) -> m (expr typ func))
    (e : (expr typ func)) (rvars : list (RG (expr typ func))) (rg : RG (expr typ func)) :
  	m (expr typ func) :=
    rg_plus (f e rvars rg) (g e rvars rg).

  Variable rel : typ -> Rbase.
  Variable rewrite_respects : Rbase -> list (RG Rbase) -> RG Rbase -> m (expr typ func).
  Variable rewrite_exs : Rbase -> list (RG Rbase) -> RG Rbase -> m (expr typ func).

  Definition setoid_rewrite (l : typ) (e : expr typ func) : expr typ func :=
    match
      rw_fix 10 (@setoid_rewrite typ func (expr typ func)
                       rel_dec
                       rewrite_exs rewrite_respects)
        e nil (RGinj (rel l))
        (rsubst_empty _)
    with
      | None => e
      | Some (e,_) => e
    end.
  
End SetoidRewrite.