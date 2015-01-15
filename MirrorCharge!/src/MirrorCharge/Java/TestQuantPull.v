Require Import MirrorCharge.Java.JavaType.
Require Import MirrorCharge.Java.JavaFunc.

Require Import MirrorCharge.SetoidRewrite.Base.
Require Import MirrorCharge.SetoidRewrite.ILSetoidRewrite.
Require Import MirrorCharge.SetoidRewrite.BILSetoidRewrite.
Require Import MirrorCharge.SetoidRewrite.EmbedSetoidRewrite.

Require Import MirrorCharge.PullQuant.BILPullQuant.
Require Import MirrorCharge.PullQuant.ILPullQuant.
Require Import MirrorCharge.PullQuant.EmbedPullQuant.

Require Import MirrorCharge.ModularFunc.BaseFunc.
Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.BILogicFunc.
Require Import MirrorCharge.ModularFunc.EmbedFunc.

Require Import MirrorCore.Lambda.Expr.

Section TestQuantPull.

Context {fs : Environment}.

Definition pull_quant vars :=
  setoid_rewrite  vars _ (fEntails : typ -> expr typ func) rw_fail
    (sr_combine il_respects
               (sr_combine (@il_respects_reflexive typ func _ _ _ ilops _ _)
                                        (sr_combine bil_respects (sr_combine embed_respects
                                                    (sr_combine eq_respects refl)))))
    (sr_combineK  (il_match_plus (fun _ => true) fEq)
                  (sr_combineK (bil_match_plus fEq) (eil_match_plus fEq))).
Definition goal : expr typ func :=
  mkAnd tySasn (mkTrue tySasn) (mkEmbed tyProp tySasn (mkExists tyNat tyProp (mkEq tyNat (Var 0) (Var 0)))).


Fixpoint crazy_goal n :=
  match n with
    | 0 => goal
    | S n => mkAnd tySasn (crazy_goal n) (crazy_goal n)
  end.

Fixpoint crazy_goal2 n :=
  match n with
    | 0 => goal
    | S n => mkStar tySasn (crazy_goal2 n) (crazy_goal2 n)
  end.

Fixpoint countArgs (e : expr typ func) : nat :=
  match e with
    | Inj _ | Var _ | UVar _ => 0
    | App x y => S (countArgs x + countArgs y)
    | Abs _ x => countArgs x
  end.

Eval vm_compute in countArgs (crazy_goal 7).

Fixpoint countExs (e : expr typ func) : nat :=
  match e with
    | App (Inj _) (Abs _ e') => S (countExs e')
    | _ => 0
  end.

Set Printing Width 140.
Eval vm_compute in crazy_goal2 2.
Eval vm_compute in 
  match pull_quant nil tySasn (crazy_goal2 2) with
    | Some (e, _) => e 
    | _ => mkFalse tySasn
  end.	
  
Time Eval vm_compute in
    match pull_quant nil tySasn (crazy_goal 3) with
      | Some (e,_) =>  countExs e
      | None => 0
    end.

End TestQuantPull.