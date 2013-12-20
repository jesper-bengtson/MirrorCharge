Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.CoMonad.
Require Import ExtLib.Structures.MonadPlus.
Require Import ExtLib.Data.Lazy.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.SymI.
Require Import MirrorCore.Subst.
Require Import MirrorCore.Ext.Expr.
Require Import BILNormalize.

Set Implicit Arguments.
Set Strict Implicit.

Section canceller.
  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.
  Variable RType_typ : RType typD.
  Variable func : Type.
  Variable RSym_func : RSym typD func.

  Local Notation "'expr'" := (expr func).

  (** The basic procedure takes two [conjunctives]
   ** and cancels the spatial terms that occur in both.
   **)
  Let Delay := Lazy.
  Let CoMonad_Delay : CoMonad Delay := _.
  Variable m : Type -> Type.
  Context {Monad_m : Monad m}.
  Context {MonadPlus_m : MonadPlus m}.
  Context {MonadZero_m : MonadZero m}.
  Variable unify : expr -> list expr -> expr -> list expr -> m bool.

  Definition facts := list (expr * list expr).

  Definition facts_add (f : expr) (es : list expr) : facts -> facts :=
    cons (f, es).

  Notation "'lazy' val" := (fun x : unit => val) (at level 50, val at next level).
  Notation "'force' val" := (val tt) (at level 50).

  Section fold.
    Variable b : Type.
    Variable cmd : expr -> list expr -> Lazy facts -> (Delay (m b)) -> Delay (m b).

    Fixpoint fold_rest (rem f : facts) (acc : Delay (m b)) : Delay (m b) :=
      match f with
        | nil => acc
        | fes :: f' =>
          cobind acc (fun acc =>
                        let '(f,es) := fes in
                        coret ((fold_rest (fes :: rem) f')
                                 (cmd f es (lazy (List.rev_append rem f')) acc)))
      end.

    Definition foldM (acc : Delay (m b)) (f : facts) : Delay (m b) :=
      fold_rest nil f acc.
  End fold.

  Import MonadNotation.
  Local Open Scope monad_scope.

  Variable wmjoin : forall T, (Delay (m T)) -> (Delay (m T)) -> Delay (m T).

  Fixpoint cancel_from' (ls : list (expr * list expr))
           (rhs : facts) (rem : facts) : Delay (m (facts * facts)) :=
    match ls with
      | nil => fun _ => ret (rem, rhs)
      | (lf,largs) :: ls =>
        foldM (fun f args rest =>
                 wmjoin (fun x =>
                           u <- unify lf largs f args ;;
                           if u then (cancel_from' ls (force rest) rem) x else mzero))
              (cancel_from' ls rhs (facts_add lf largs rem))
              rhs
    end.

  Fixpoint cancel_from'' (ls : list (expr * list expr))
           (rhs : facts) (rem : facts) : Delay (m (facts * facts)) :=
    match ls with
      | nil => fun _ => ret (rem, rhs)
      | (lf,largs) :: ls =>
        foldM (fun f args rest =>
                 wmjoin (cobind (cancel_from'' ls (force rest) rem)
                                (fun x =>
                                   u <- unify lf largs f args ;;
                                   if u then coret x else mzero)))
              (fun x => cancel_from'' ls rhs (facts_add lf largs rem) x)
              rhs
    end.

  Definition cancel_from :=
    Eval cbv beta iota zeta delta [ cancel_from'' cobind coret CoMonad_Lazy _lazy ] in
      cancel_from''.

End canceller.

Module demo.
  Require Import ExtLib.Data.Monads.StateMonad.
  Require Import ExtLib.Data.Monads.OptionMonad.
  Require Import ExtLib.Data.Monads.ListMonad.
  Require Import ExtLib.Core.RelDec.

  Let typ : Type := unit.
  Let typD : list Type -> typ -> Type := fun _ _ => nat.
  Let func : Type := nat.

  Let subst : Type := list (nat * expr func).

  Fixpoint sget (n : nat) (s : subst) : expr func :=
    match s with
      | nil => UVar n
      | (n', e) :: s =>
        if n' ?[ eq ] n then e else sget n s
    end.

  Fixpoint instantiate (s : subst) (e : expr func) : expr func :=
    match e with
      | UVar u => sget u s
      | Inj _
      | Var _ => e
      | App l r => App (instantiate s l) (instantiate s r)
      | Abs t e => Abs t (instantiate s e)
    end.

  Definition subst_add (n : nat) (e : expr func) (s : subst) : subst :=
    let e := instantiate s e in
    (n,e) :: s.

  Section unify.
    Variable m : Type -> Type.
    Context {Monad_m : Monad m} {MonadState_m : MonadState subst m}.

    Import MonadNotation.
    Local Open Scope monad_scope.

    Fixpoint unify1 (a b : expr func) : m bool :=
      match a , b with
        | UVar a , UVar b =>
          if a ?[ eq ] b
          then ret true
          else (s <- MonadState.get ;;
                MonadState.put (subst_add a (UVar b) s) ;;
                ret true)
        | UVar a , _ =>
          s <- MonadState.get ;;
          MonadState.put (subst_add a b s) ;;
          ret true
        | _ , UVar b =>
          s <- MonadState.get ;;
          MonadState.put (subst_add b a s) ;;
          ret true
        | App l r , App l' r' =>
          bind (unify1 l l') (fun x =>
                                if x then unify1 r r' else ret false)
        | Abs _ e , Abs _ e' =>
          unify1 e e'
        | Inj a , Inj b =>
          ret (a ?[ eq ] b)
        | Var a , Var b =>
          ret (a ?[ eq ] b)
        | _ , _ => ret false
      end.

    Definition try {T} (P : T -> bool) (cmd : m T) : m T :=
      s <- get ;;
      x <- cmd ;;
      (if P x then ret tt else put s) ;;
      ret x.

    Definition unify (f : expr func) (es : list (expr func))
                     (f' : expr func) (es' : list (expr func))
    : m bool :=
      try (fun x => x)
          (u <- unify1 f f' ;;
           if u then
             (fix try xs ys :=
                match xs , ys with
                  | nil , nil => ret true
                  | x :: xs , y :: ys =>
                    s <- get ;;
                    u <- unify1 (instantiate s x) (instantiate s y) ;;
                    if u then try xs ys else ret false
                  | _ , _ => ret false
                end) es es'
           else
             ret false).
  End unify.

  Fixpoint ptsto_chain (ctor : nat -> expr func) (n : nat) : facts func :=
    match n with
      | 0 => nil
      | S n => (Inj 0, (ctor n :: ctor (S n) :: nil)) :: ptsto_chain ctor n
    end.

  Section single.
    Let m : Type -> Type := stateT subst option.

    Let Monad_m : Monad m := Monad_stateT _ _.
    Let MonadPlus_m : MonadPlus m := MonadPlus_stateT _ _ _.
    Let MonadState_m : MonadState subst m := MonadState_stateT _ _.
    Let MonadZero_m : MonadZero m := MonadZero_stateT _ _ _.
    Local Existing Instance Monad_m.
    Local Existing Instance MonadPlus_m.
    Local Existing Instance MonadState_m.
    Local Existing Instance MonadZero_m.

    Definition wmjoin {T} (a b : Lazy (m T)) : Lazy (m T) :=
      fun x : unit => @mkStateT _ _ _ (fun s =>
                                         match runStateT (a x) s with
                                           | Some x => Some x
                                           | None => runStateT (b x) s
                                         end).

    Definition test_single (a : list (expr func * list (expr func))) (b : facts func)
    : option ((facts func * facts func) * subst) :=
      runStateT (force (@cancel_from func m _ _ (@unify _ _ _) (@wmjoin) a b nil)) nil.

    Definition test_single' (a : list (expr func * list (expr func))) (b : facts func)
    : option ((facts func * facts func) * subst) :=
      runStateT (force (@cancel_from'' func m _ _ (@unify _ _ _) (@wmjoin) a b nil)) nil.

    Eval compute in ptsto_chain UVar 1.
    Eval compute in ptsto_chain Var 1.

    Eval vm_compute in test_single (ptsto_chain Var 4) (List.rev (ptsto_chain UVar 4)).
    Time Eval vm_compute in match test_single' (ptsto_chain Var 200) (List.rev (ptsto_chain UVar 200)) with
                         | None => false
                         | Some _ => true
                       end.

    Time Eval vm_compute in match test_single (ptsto_chain Var 500) (List.rev (ptsto_chain UVar 500)) with
                         | None => false
                         | Some _ => true
                       end.

  End single.

  Section multi.
    Let m : Type -> Type := stateT subst list.

    Let Monad_m : Monad m := Monad_stateT _ _.
    Let MonadPlus_m : MonadPlus m := MonadPlus_stateT _ _ _.
    Let MonadState_m : MonadState subst m := MonadState_stateT _ _.
    Let MonadZero_m : MonadZero m := MonadZero_stateT _ _ _.
    Local Existing Instance Monad_m.
    Local Existing Instance MonadPlus_m.
    Local Existing Instance MonadState_m.
    Local Existing Instance MonadZero_m.

    Definition wmjoin_list {T} (a b : Lazy (m T)) : Lazy (m T) :=
      fun x : unit => @mkStateT _ _ _ (fun s =>
                                         runStateT (a x) s ++ runStateT (b x) s).
    Definition test_multi (a : list (expr func * list (expr func))) (b : facts func)
    : list ((facts func * facts func) * subst) :=
      runStateT (@cancel_from func m _ _ (@unify _ _ _) (@wmjoin_list) a b nil tt) nil.

    Eval vm_compute in test_multi (ptsto_chain Var 4) (List.rev (ptsto_chain UVar 4)).
  End multi.
End demo.
