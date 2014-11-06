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
Require Import MirrorCharge.ModularFunc.EmbedFunc.

Require Import MirrorCore.Lambda.Expr.

Let Rbase := expr typ func.

Definition rewriter :=
  expr typ func ->
  list (AutoSetoidRewrite.RG Rbase) ->
  AutoSetoidRewrite.RG Rbase -> m (typ:=typ) (func:=func) (expr typ func).

Section do_several.
  Variable (rw : rewriter).

  Fixpoint do_several (n : nat) a b c {struct n} :=
    match n with
      | 0 => rg_ret a
      | S n => fun d => match rw a b c d with
                          | None => rg_ret a d
                          | Some (a',d') => do_several n a' b c d'
                        end
    end.
End do_several.

Section do_severalK.
  Variable (rw : rewriter -> rewriter).

  Fixpoint do_severalK  (n : nat) (rw' : rewriter)
           (a : expr typ func) (b : list (AutoSetoidRewrite.RG Rbase))
           (c :  AutoSetoidRewrite.RG Rbase) {struct n} :=
    match n with
      | 0 => rg_ret a
      | S n => fun d =>
                 AutoSetoidRewrite.tryRewrite
                   (rw (fun a b c d => do_severalK n rw' a b c d))
                   a b c d
    end.
End do_severalK.

Definition setoid_rewrite' := 
fun (RelDec_func_eq : RelDec.RelDec eq) =>
let Rbase := expr typ func in
fun (rel : typ -> Rbase)
  (rewrite_respects : rewriter)
  (rewrite_exs : rewriter -> rewriter)
  (l : typ) (e : expr typ func) =>
(* match *)
(*  (rw_fix 4 *)
  (AutoSetoidRewrite.setoid_rewrite
     RelDec.rel_dec
     (fun a _ _ => rg_fail)
     rewrite_respects
     (do_severalK rewrite_exs 1000 (fun a _ _ => rg_ret a)))
    e nil (AutoSetoidRewrite.RGinj (rel l))
    (AutoSetoidRewrite.rsubst_empty Rbase)
(*with
| Some (e0, _) => e0
| None => e
end*).

Definition fEq (t : typ) : expr typ func.
  apply Inj. left. left. left. left. left. right. apply pEq. assumption.
Defined.

Definition eq_respects :=
  fun (e : expr typ func) (_ : list (AutoSetoidRewrite.RG Rbase))
      (rg : AutoSetoidRewrite.RG Rbase) =>
    match e with
      | Inj (inl (inl (inl (inl (inl (inr (pEq t))))))) =>
        rg_bind
          (AutoSetoidRewrite.unifyRG
             (RelDec.rel_dec (equ:=@eq (expr typ func))) rg
             (AutoSetoidRewrite.RGrespects
                (AutoSetoidRewrite.RGinj e)
                (AutoSetoidRewrite.RGrespects
                   (AutoSetoidRewrite.RGinj e)
                   (AutoSetoidRewrite.RGinj (fEntails tyProp)))))
          (fun _ : AutoSetoidRewrite.RG (expr typ func) => rg_ret e)
      | _ => rg_fail
    end.

Definition refl :=
  let Rbase := expr typ func in
  fun (e : expr typ func) (_ : list (AutoSetoidRewrite.RG Rbase))
      (rg : AutoSetoidRewrite.RG Rbase) =>
    match typeof_expr nil nil e with
      | Some t =>
        rg_bind
          (AutoSetoidRewrite.unifyRG (RelDec.rel_dec (equ:=@eq (expr typ func))) rg
                                     (AutoSetoidRewrite.RGinj (fEq t)))
          (fun _ : AutoSetoidRewrite.RG (expr typ func) => rg_ret e)
      | None => rg_fail
    end.

(*
Definition pull_quant :=
  setoid_rewrite' _ fEntails
    (sr_combine il_respects
                (sr_combine bil_respects
                            (sr_combine (il_respects_reflexive ilops)
                                        (sr_combine embed_respects
                                                    (sr_combine eq_respects refl)))))
    (sr_combineK  (il_match_plus (fun _ => true) fEq)
                  (sr_combineK (bil_match_plus fEq) (eil_match_plus fEq))).
*)

Definition pull_quant :=
  setoid_rewrite' _ fEntails
    (sr_combine il_respects
                (sr_combine (il_respects_reflexive ilops)
                                        (sr_combine embed_respects
                                                    (sr_combine eq_respects refl))))
    (sr_combineK  (il_match_plus (fun _ => true) fEq)
                  (sr_combineK (bil_match_plus fEq) (eil_match_plus fEq))).

Definition goal : expr typ func :=
  mkAnd tySasn (mkTrue tySasn) (mkEmbed tyProp tySasn (mkExists tyNat tyProp (mkEq tyNat (Var 0) (Var 0)))).


Fixpoint crazy_goal n :=
  match n with
    | 0 => goal
    | S n => mkAnd tySasn (crazy_goal n) (crazy_goal n)
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

Time Eval vm_compute in
    match pull_quant tySasn (crazy_goal 7) with
      | Some (e,_) => (* countExs e *) 1
      | None => 0
    end.
