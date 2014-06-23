Require Import Coq.Strings.String.
Require Import Coq.PArith.BinPos.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Nat.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.TypesI.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.STac.STac.
Require Import MirrorCore.provers.DefaultProver.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.Subst.FMapSubst3.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.ExprSubst.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.Lambda.Red.
Require Import MirrorCore.Lambda.AppN.
Require Import MirrorCharge.ILogicFunc.
Require Import MirrorCharge.OrderedCanceller.
Require Import MirrorCharge.BILNormalize.
Require Import MirrorCharge.SynSepLog.
Require Import MirrorCharge.SepLogFold.
Require Import MirrorCharge.Imp.Imp.
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

Let eapply_other :=
  @eapply_other typ (expr typ func) subst tyProp vars_to_uvars
                (fun tus tvs n e1 e2 t s =>
                   @exprUnify subst typ func _ _ RS SS SU 3 nil
                              tus tvs n s e1 e2 t)
                (@instantiate typ func) SS SU.


(** NOTE: Manual lemma reification for the time being **)
(** Skip **)
Definition skip_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyLProp :: tyLProp :: nil
 ; premises := lentails tyLProp (Var 0) (Var 1) :: nil
 ; concl := mkTriple (Var 0) mkSkip (Var 1)
 |}.

Definition skip_lemma2 : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyLProp :: nil
 ; premises := nil
 ; concl := mkTriple (Var 0) mkSkip (Var 0)
 |}.


(** Sequence **)
Definition seq_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyLProp :: tyLProp :: tyLProp :: tyCmd :: tyCmd :: nil
 ; premises := mkTriple (Var 0) (Var 3) (Var 1) ::
               mkTriple (Var 1) (Var 4) (Var 2) :: nil
 ; concl := mkTriple (Var 0) (mkSeq (Var 3) (Var 4)) (Var 2)
 |}.

Definition seq_assoc_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyLProp :: tyLProp :: tyCmd :: tyCmd :: tyCmd :: nil
 ; premises :=
     mkTriple (Var 0) (mkSeq (Var 2) (mkSeq (Var 3) (Var 4))) (Var 1) :: nil
 ; concl :=
     mkTriple (Var 0) (mkSeq (mkSeq (Var 2) (Var 3)) (Var 4)) (Var 1)
 |}.

(** Assignment **)
Definition assign_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyLProp :: tyVariable :: tyExpr :: nil
 ; premises := nil
 ; concl :=
     mkTriple (Var 0)
              (mkAssign (Var 1) (Var 2))
              (lex tyLProp tyNat
                   (land tyLProp
                         (lap tyProp tyHProp
                              (lpure (tyArr tyProp tyHProp) ((Inj (inr (ilf_embed tyProp tyHProp)))))
                              (lap tyNat tyProp (lap tyNat (tyArr tyNat tyProp) (lpure (tyArr tyNat (tyArr tyNat tyProp))
                                                                                       (fEq tyNat))
                                                     (App flocals_get (Var 2)))
                                   (lupdate tyNat (App (App flocals_upd (Var 2)) (Var 0)) (App feval_iexpr (Var 3)))))
                         (lupdate tyHProp (App (App flocals_upd (Var 2)) (Var 0)) (Var 1))))
 |}.

(** Read **)
Definition read_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyLProp :: tyVariable :: tyExpr ::
                   tyArr tyLocals tyNat :: nil
 ; premises :=
     lentails tyLProp
              (Var 0)
              (lstar tyLProp
                     (lap tyNat tyHProp (lap tyNat (tyArr tyNat tyHProp) (lpure (tyArr tyNat (tyArr tyNat tyHProp)) fPtsTo) (feval_iexpr @ Var 2)) (Var 3))
                     (ltrue tyLProp))
              :: nil
 ; concl :=
     mkTriple (Var 0)
              (mkRead (Var 1) (Var 2))
              (lex tyLProp tyNat
                   (land tyLProp
                         (lap tyProp tyHProp
                              (lpure (tyArr tyProp tyHProp) ((Inj (inr (ilf_embed tyProp tyHProp)))))
                              (lap tyNat tyProp (lap tyNat (tyArr tyNat tyProp) (lpure (tyArr tyNat (tyArr tyNat tyProp))
                                                                                       (fEq tyNat))
                                                     (App flocals_get (Var 2)))
                                   (lupdate tyNat (App (App flocals_upd (Var 2)) (Var 0)) (Var 4))))
                         (lupdate tyHProp (App (App flocals_upd (Var 2)) (Var 0)) (Var 1))))
 |}.

(** Write **)
Definition write_lemma : lemma typ (expr typ func) (expr typ func) :=
{| vars := tyLProp :: tyLProp :: tyExpr :: tyExpr :: nil
 ; premises :=
     lentails tyLProp
              (Var 0)
              (lex tyLProp tyNat
                   (lstar tyLProp
                          (lap tyNat tyHProp (lap tyNat (tyArr tyNat tyHProp)
                                                  (lpure (tyArr tyNat (tyArr tyNat tyHProp)) fPtsTo)
                                                  (feval_iexpr @ Var 3))
                               (lpure tyNat (Var 0)))
                          (Var 2)))
     :: nil
 ; concl :=
     mkTriple (Var 0)
              (mkWrite (Var 2) (Var 3))
              (lstar tyLProp
                     (lap tyNat tyHProp (lap tyNat (tyArr tyNat tyHProp) (lpure (tyArr tyNat (tyArr tyNat tyHProp)) fPtsTo) (feval_iexpr @ Var 2)) (feval_iexpr @ Var 3))
                     (Var 1))
 |}.

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
End interp_get.

Print flocals_get.

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
        (** TODO(gmalecha): forall, exists **)
      | App (Pure [t]) e =>
        App (Pure [t]) e
      | App (App (Ap [t1,t2]) e1) e2 =>
        App (App (Ap [t1,t2]) (pushUpdates e1 (tyArr t1 t2))) (pushUpdates e2 t1)
      | App (Inj (inl (inr pLocals_get))) v =>
        interp_get v f
      | _ => App (App (Inj (inl (inr (pUpdate t)))) f) e
    end.
End pushUpdates.

Definition apps' := apps.

Definition simplify (e : expr typ func) (args : list (expr typ func))
: expr typ func :=
  match e with
    | Inj (inl (inr pEval_expri)) =>
      match args with
        | App (Inj (inl (inr eVar))) X :: xs =>
          apps (App flocals_get X) xs
        | _ => apps e args
      end
    | Inj (inl (inr (pUpdate t))) =>
      match args with
        | f :: e :: nil =>
          pushUpdates f e t
        | _ => apps e args
      end
    | _ => apps' e args
  end.

(** NOTE: this is for [locals -> HProp] **)
Definition sls : SepLogSpec typ func :=
{| is_pure := fun (e : expr typ func) =>
                match e with
                  | Inj (inr (ilf_true _))
                  | Inj (inr (ilf_false _)) => true
                  | _ => false
                end
 ; is_emp := fun e => false
 ; is_star := fun (e : expr typ func) =>
                match e with
                  | Inj (inl (inr (pStar _))) => true
                  | _ => false
                end
 |}.

Let doUnifySepLog (tus tvs : EnvI.tenv typ) (s : subst) (e1 e2 : expr typ func)
: option subst :=
  @exprUnify subst typ func _ _ _ _ _ 10 nil tus tvs 0 s e1 e2 tyLProp.

Let ssl : SynSepLog typ func :=
{| e_star := fun l r =>
               match l with
                 | Inj (inl (inr (pEmp _))) => r
                 | _ => match r with
                          | Inj (inl (inr (pEmp _))) => l
                          | _ => lstar tyLProp l r
                        end
               end
 ; e_emp := lemp tyLProp
 ; e_and := fun l r =>
              match l with
                | Inj (inr (ilf_true _)) => r
                | _ => match r with
                         | Inj (inr (ilf_true _)) => l
                         | _ => land tyLProp l r
                       end
              end
 ; e_true := ltrue tyLProp
 |}.

Definition eproveTrue (s : subst) (e : expr typ func) : option subst :=
  match e with
    | Inj (inr (ilf_true _)) => Some s
    | _ => None
  end.

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

Definition the_canceller tus tvs (lhs rhs : expr typ func)
           (s : subst)
: (expr typ func * expr typ func * subst) + subst:=
  match @normalize typ _ _ func _ sls nil tus tvs tyLProp lhs
        , @normalize typ _ _ func _ sls nil tus tvs tyLProp rhs
  with
    | Some lhs_norm , Some rhs_norm =>
      match lhs_norm tt , rhs_norm tt with
        | Some lhs_norm , Some rhs_norm =>
          let '(lhs',rhs',s') :=
              OrderedCanceller.ordered_cancel
                (doUnifySepLog tus tvs) eproveTrue
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

Definition stac_cancel (thn : stac typ (expr typ func) subst)
: stac typ (expr typ func) subst :=
  fun e s tus tvs =>
    match e with
      | App (App (Inj (inr (ilf_entails (tyArr tyLocals tyHProp)))) L) R =>
        match the_canceller tus tvs L R s with
          | inl (l,r,s') =>
            let e' :=
                App (App (Inj (inr (ilf_entails (tyArr tyLocals tyHProp)))) l) r
            in
            thn e' s tus tvs
          | inr s' => @Solve _ _ _ s'
        end
      | _ => thn e s tus tvs
    end.

Definition all_cases : stac typ (expr typ func) subst :=
  let solve_entailment :=
      SIMPLIFY (fun _ _ => beta_all simplify nil nil)
               (stac_cancel (@IDTAC _ _ _))
  in
  REC 10 (fun rec =>
            let rec := rec in
            REPEAT 5
                   (FIRST (   eapply_other seq_assoc_lemma rec
                           :: eapply_other seq_lemma rec
                           :: eapply_other assign_lemma rec
                           :: eapply_other read_lemma solve_entailment
                           :: eapply_other write_lemma solve_entailment
                           :: eapply_other skip_lemma solve_entailment
                           :: nil)))
      (@FAIL _ _ _).

Definition test :=
  let vars := tyLProp :: tyCmd :: tyCmd :: tyCmd :: tyLProp :: nil in
  let goal :=
      mkTriple (Var 0)
               (mkSeq (mkSeq (Var 1) (Var 2)) (Var 3))
               (Var 4)
  in
  @all_cases goal (SubstI3.empty (expr :=expr typ func))
             nil vars.

Time Eval vm_compute in test.

Definition test' :=
  let uvars := tyLProp :: nil in
  let vars := tyLProp :: tyVariable :: tyCmd :: tyCmd :: tyLProp :: tyExpr :: nil in
  let goal :=
      mkTriple (Var 0)
               (mkSeq (mkAssign (Var 1) (Var 5)) (Var 2))
               (UVar 0)
  in
  @all_cases goal (SubstI3.empty (expr :=expr typ func))
             uvars vars.

Time Eval vm_compute in test'.

Definition test_read :=
  let uvars := tyLProp :: nil in
  let vars := nil in
  let goal :=
      mkTriple (lap tyNat tyHProp (lap tyNat (tyArr tyNat tyHProp) (lpure (tyArr tyNat (tyArr tyNat tyHProp)) fPtsTo)
                                       (flocals_get @ fVar "p"))%string
                    (lpure tyNat (fConst 1)))
               (mkRead (fVar "x") (Inj (inl (inr eVar)) @ (fVar "p")))%string
               (UVar 0)
  in
  let tac := all_cases in
  @tac goal (SubstI3.empty (expr :=expr typ func))
       uvars vars.

Time Eval vm_compute in test_read.

Definition lifted_ptsto (a b : expr typ func) : expr typ func :=
  lap tyNat tyHProp (lap tyNat (tyArr tyNat tyHProp)
                         (lpure (tyArr tyNat (tyArr tyNat tyHProp)) fPtsTo)
                         a) b.

Definition test_swap :=
  let uvars := nil in
  let vars := tyArr tyLocals tyNat :: tyArr tyLocals tyNat :: nil in
  let goal :=
      (mkTriple
         (lstar tyLProp
                (lifted_ptsto (flocals_get @ fVar "p1") (Var 0))
                (lifted_ptsto (flocals_get @ fVar "p2") (Var 1)))
         (mkSeq (mkRead (fVar "t1") (Inj (inl (inr eVar)) @ (fVar "p1")))
         (mkSeq (mkRead (fVar "t2") (Inj (inl (inr eVar)) @ (fVar "p2")))
         (mkSeq (mkWrite (Inj (inl (inr eVar)) @ fVar "t2") (Inj (inl (inr eVar)) @ (fVar "t1")))
                (mkWrite (Inj (inl (inr eVar)) @ fVar "t1") (Inj (inl (inr eVar)) @ (fVar "t2"))))))
         (lstar tyLProp
                (lifted_ptsto (flocals_get @ fVar "p1") (Var 1))
                (lifted_ptsto (flocals_get @ fVar "p2") (Var 0))))%string
  in
  let tac :=
      let solve_entailment :=
          SIMPLIFY (fun _ _ => beta_all simplify nil nil)
                   (stac_cancel (@IDTAC _ _ _))
      in
      REC 1 (fun rec =>
                let rec := rec in
                REPEAT 5
                       (FIRST (   eapply_other seq_assoc_lemma rec
                               :: eapply_other seq_lemma rec
                               :: eapply_other assign_lemma rec
                               :: eapply_other read_lemma solve_entailment
                               :: eapply_other write_lemma solve_entailment
                               :: nil)))
          (@FAIL _ _ _)
  in
  @tac goal (SubstI3.empty (expr :=expr typ func)) uvars vars.

(** TODO(gmalecha): Debug this!
Eval cbv beta iota zeta delta - [ REC REPEAT FIRST FAIL SIMPLIFY stac_cancel beta_all simplify ] in test_swap.
*)
