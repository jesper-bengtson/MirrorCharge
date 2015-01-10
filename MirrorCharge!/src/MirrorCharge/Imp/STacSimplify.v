Require Import ExtLib.Core.RelDec.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCharge.ILogicFunc.
Require Import MirrorCharge.Imp.Syntax.

Set Implicit Arguments.
Set Strict Implicit.

Local Existing Instance SS.
Local Existing Instance SU.
Local Existing Instance RSym_ilfunc.
Local Existing Instance RS.
Local Existing Instance Expr_expr.

Local Notation "a @ b" := (@App typ _ a b) (at level 30).
Local Notation "\ t -> e" := (@Abs typ _ t e) (at level 40).
Local Notation "'Ap' '[' x , y ']'" := (Inj (inl (inr (pAp x y)))) (at level 0).
Local Notation "'Pure' '[' x ']'" := (Inj (inl (inr (pPure x)))) (at level 0).
Local Notation "x '|-' y" :=
  (App (App (Inj (inr (ilf_entails (tyArr tyLocals tyHProp)))) x) y) (at level 10).
Local Notation "'{{'  P  '}}'  c  '{{'  Q  '}}'" :=
  (Inj (inl (inl 1%positive)) @ P @ c @ Q) (at level 20).
Local Notation "c1 ;; c2" := (Inj (inl (inl 2%positive)) @ c1 @ c2) (at level 30).

Fixpoint expr_eq (a b : expr typ func) : option bool :=
  match a , b with
    | Var a , Var b => if a ?[ eq ] b then Some true else None
    | UVar a , UVar b => if a ?[ eq ] b then Some true else None
    | Inj a , Inj b => SymI.sym_eqb a b
    | App a b , App c d =>
      match expr_eq a c with
        | Some true => expr_eq b d
        | _ => None
      end
    | Abs t a , Abs t' b => expr_eq a b
    | _ , _ => None
  end.

Section interp_get.
  Variable v : expr typ func.

  Definition compare_expr (e1 e2 : expr typ func) : option bool :=
    expr_eq e1 e2.

  Fixpoint interp_get (updf : expr typ func)
  : expr typ func :=
    match updf with
      | App (App (Inj (inl (inr pLocals_upd))) v') val =>
        match compare_expr v v' with
          | Some true =>
            lpure tyNat val
          | Some false =>
            App flocals_get v
          | None =>
            App (App (Inj (inl (inr (pUpdate tyNat)))) updf) (App flocals_get v)
        end
      | _ =>
        App (App (Inj (inl (inr (pUpdate tyNat)))) updf) (App flocals_get v)
    end.

  Fixpoint interp_get' (mem : expr typ func)
  : expr typ func :=
    match mem with
      | App (App (App (Inj (inl (inr pLocals_upd))) v') val) mem' =>
        match compare_expr v v' with
          | Some true =>
            val
          | Some false =>
            interp_get' mem'
          | None =>
            App (App (Inj (inl (inr pLocals_get))) v) mem
        end
      | _ =>
        App (App (Inj (inl (inr pLocals_get))) v) mem
    end.

End interp_get.

Section pushUpdates.
  Variable f : expr typ func.

  Fixpoint pushUpdates (e : expr typ func) (t : typ)
  : expr typ func :=
    match e with
      | App (App (Inj (inl (inr (pStar t)))) L) R =>
        lstar t (pushUpdates L t) (pushUpdates R t)
      | Inj (inr (ilf_true t)) => Inj (inr (ilf_true t))
      | Inj (inr (ilf_false t)) => Inj (inr (ilf_false t))
      | App (App (Inj (inr (ilf_and t))) L) R =>
        App (App (Inj (inr (ilf_and t))) (pushUpdates L t)) (pushUpdates R t)
      | App (App (Inj (inr (ilf_or t))) L) R =>
        App (App (Inj (inr (ilf_or t))) (pushUpdates L t)) (pushUpdates R t)
      | App (App (Inj (inr (ilf_impl t))) L) R =>
        App (App (Inj (inr (ilf_impl t))) (pushUpdates L t)) (pushUpdates R t)
      | App (Inj (inr (ilf_exists X t))) (Abs t' e) =>
        App (Inj (inr (ilf_exists X t))) (Abs t' (pushUpdates e t))
      | App (Inj (inr (ilf_forall X t))) (Abs t' e) =>
        App (Inj (inr (ilf_forall X t))) (Abs t' (pushUpdates e t))
      | App (Pure [t]) e =>
        App (Pure [t]) e
      | App (App (Ap [t1,t2]) e1) e2 =>
        App (App (Ap [t1,t2]) (pushUpdates e1 (tyArr t1 t2))) (pushUpdates e2 t1)
      | App (Inj (inl (inr pLocals_get))) v =>
        interp_get v f
      | _ => App (App (Inj (inl (inr (pUpdate t)))) f) e
    end.
End pushUpdates.

Fixpoint redApplicative (a b : expr typ func) : expr typ func :=
  match a with
    | App (App (Inj (inl (inr (pAp _ _)))) x) y =>
      App (redApplicative x b) (redApplicative y b)
    | App (Inj (inl (inr (pPure _)))) x => x
    | _ => App a b
  end.

Fixpoint simplify (fuel : nat) (e : expr typ func) (args : list (expr typ func))
: expr typ func :=
  match e with
    | Inj (inl (inr pEval_expri)) =>
      match args with
        | App (Inj (inl (inr eVar))) X :: xs =>
          apps (App flocals_get X) xs
        | App (Inj (inl (inr eConst))) X :: xs =>
          X
        | App (App (Inj (inl (inr ePlus))) X) Y :: xs =>
          match fuel with
            | 0 =>
              apps e args
            | S fuel =>
              let X' := simplify fuel e (X :: xs) in
              let Y' := simplify fuel e (Y :: xs) in
              App (App (Inj (inl (inr natPlus))) X') Y'
          end
        | _ => apps e args
      end
    | Inj (inl (inr pLocals_get)) =>
      match args with
        | X :: Y :: xs =>
          apps (interp_get' X Y) xs
        | _ => apps e args
      end
    | Inj (inl (inr (pUpdate t))) =>
      match args with
        | f :: e :: nil =>
          pushUpdates f e t
        | _ => apps e args
      end
    | Inj (inr (ilf_and (tyArr _ d))) =>
      match args with
        | X :: Y :: Z :: args =>
          apps (Inj (inr (ilf_and d))) (App X Z :: App Y Z :: args)
        | _ => apps e args
      end
    | Inj (inr (ilf_or (tyArr _ d))) =>
      match args with
        | X :: Y :: Z :: args =>
          apps (Inj (inr (ilf_or d))) (App X Z :: App Y Z :: args)
        | _ => apps e args
      end
    | Inj (inr (ilf_impl (tyArr _ d))) =>
      match args with
        | X :: Y :: Z :: args =>
          apps (Inj (inr (ilf_impl d))) (App X Z :: App Y Z :: args)
        | _ => apps e args
      end
    | Inj (inr (ilf_forall z (tyArr t d))) =>
      match args with
        | X :: Y :: args =>
          apps (Abs t (App (Inj (inr (ilf_forall z d)))
                           (Abs z (App (App X (Var 0)) (Var 1))))) (Y :: args)
        | _ => apps e args
      end
    | Inj (inr (ilf_exists z (tyArr t d))) =>
      match args with
        | X :: Y :: args =>
          apps (Abs t (App (Inj (inr (ilf_exists z d)))
                           (Abs z (App (App X (Var 0)) (Var 1))))) (Y :: args)
        | _ => apps e args
      end
    | Inj (inr (ilf_true (tyArr _ d))) =>
      match args with
        | X :: args =>
          apps (Inj (inr (ilf_true d))) args
        | _ => apps e args
      end
    | Inj (inr (ilf_false (tyArr _ d))) =>
      match args with
        | X :: args =>
          apps (Inj (inr (ilf_false d))) args
        | _ => apps e args
      end
    | Inj (inl (inr (pStar (tyArr _ d)))) =>
      match args with
        | X :: Y :: Z :: args =>
          apps (Inj (inl (inr (pStar d)))) (App X Z :: App Y Z :: args)
        | _ => apps e args
      end
    | _ => apps e args
  end.

Definition simplifyApplicative (e : expr typ func) (args : list (expr typ func))
: expr typ func :=
  match e with
    | Inj (inl (inr (pAp _ _))) =>
      match args with
        | X :: Y :: Z :: args =>
          apps (App (redApplicative X Z) (redApplicative Y Z)) args
        | _ => apps e args
      end
    | Inj (inl (inr (pPure _))) =>
      match args with
        | X :: Y :: args => apps X args
        | _ => apps e args
      end
    | _ => apps e args
  end.
