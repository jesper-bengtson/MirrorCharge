Require Import MirrorCore.Reify.Reify.
Require Import MirrorCharge.Imp.Imp.
Require Import MirrorCharge.Imp.Syntax.

Reify Declare Patterns patterns_imp_typ := Syntax.typ.

Reify Declare Patterns patterns_imp := (ExprCore.expr Syntax.typ Syntax.func).

Reify Declare Syntax reify_imp_typ : Syntax.typ :=
  { (Patterns patterns_imp_typ) }.
Reify Declare Syntax reify_imp : (ExprCore.expr Syntax.typ Syntax.func) :=
  { (Patterns patterns_imp)
    (App (@ExprCore.App Syntax.typ Syntax.func))
    (Abs _ (@ExprCore.Abs Syntax.typ Syntax.func))
    (Var (@ExprCore.Var Syntax.typ Syntax.func))
  }.


Let _Inj := @ExprCore.Inj Syntax.typ Syntax.func.

Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
Local Notation "'#'" := RIgnore (only parsing, at level 0).


Reify Pattern patterns_imp_typ += (@RImpl (@RGet 0 RIgnore) (@RGet 1 RIgnore)) => (fun (a b : function reify_imp_typ) => tyArr a b).
Reify Pattern patterns_imp_typ += (!! locals)  => tyLocals.
Reify Pattern patterns_imp_typ += (!! lprop)  => (tyArr tyLocals tyProp).
Reify Pattern patterns_imp_typ += (!! icmd) => tyCmd.
Reify Pattern patterns_imp_typ += (!! SProp) => tySProp.
Reify Pattern patterns_imp_typ += (!! HProp) => tyHProp.
Reify Pattern patterns_imp_typ += (!! Prop) => tyProp.
Reify Pattern patterns_imp_typ += (!! var) => tyVariable.
Reify Pattern patterns_imp_typ += (!! iexpr) => tyExpr.
Reify Pattern patterns_imp_typ += (!! nat)  => tyNat.


Reify Pattern patterns_imp += (RHasType var (?0)) => (fun (x : id var) => fVar x).
Reify Pattern patterns_imp += (RHasType String.string (?0)) => (fun (x : id var) => fVar x).
Reify Pattern patterns_imp += (RHasType nat (?0)) => (fun (x : id nat) => fConst x).
Reify Pattern patterns_imp += (!! (@eq) @ ?0) => (fun (x : function reify_imp_typ) => (fEq x)).

(** Commands **)
Reify Pattern patterns_imp += (!! Skip) => fSkip.
Reify Pattern patterns_imp += (!! Seq) => fSeq.
Reify Pattern patterns_imp += (!! Assign) => fAssign.
Reify Pattern patterns_imp += (!! Read) => fRead.
Reify Pattern patterns_imp += (!! Write) => fWrite.
(** TODO: Call **)

(** Expressions **)
Reify Pattern patterns_imp += (!! iConst) => fConst.
Reify Pattern patterns_imp += (!! iVar) => fVar.


(** Intuitionistic Operators **)
Reify Pattern patterns_imp += (!! @ILogic.lentails @ ?0 @ #) => (fun (x : function reify_imp_typ) => (_Inj (inr (ILogicFunc.ilf_entails x)))).
Reify Pattern patterns_imp += (!! @ILogic.ltrue @ ?0 @ #) => (fun (x : function reify_imp_typ) => (_Inj (inr (ILogicFunc.ilf_true x)))).
Reify Pattern patterns_imp += (!! @ILogic.lfalse @ ?0 @ #) => (fun (x : function reify_imp_typ) => (_Inj (inr (ILogicFunc.ilf_false x)))).
Reify Pattern patterns_imp += (!! @ILogic.land @ ?0 @ #) => (fun (x : function reify_imp_typ) => (_Inj (inr (ILogicFunc.ilf_and x)))).
Reify Pattern patterns_imp += (!! @ILogic.lor @ ?0 @ #) => (fun (x : function reify_imp_typ) => (_Inj (inr (ILogicFunc.ilf_or x)))).
Reify Pattern patterns_imp += (!! @ILogic.limpl @ ?0 @ #) => (fun (x : function reify_imp_typ) => (_Inj (inr (ILogicFunc.ilf_impl x)))).
Reify Pattern patterns_imp += (!! @ILogic.lforall @ ?0 @ # @ ?1) => (fun (x y : function reify_imp_typ) => (_Inj (inr (ILogicFunc.ilf_exists x y)))).
Reify Pattern patterns_imp += (!! @ILogic.lforall @ ?0 @ # @ ?1) => (fun (x y : function reify_imp_typ) => (_Inj (inr (ILogicFunc.ilf_exists x y)))).

(** Special cases for Coq's primitives **)
Reify Pattern patterns_imp += (!! True) => (_Inj (inr (ILogicFunc.ilf_true tyProp))).
Reify Pattern patterns_imp += (!! False) => (_Inj (inr (ILogicFunc.ilf_false tyProp))).
Reify Pattern patterns_imp += (!! and) => (_Inj (inr (ILogicFunc.ilf_and tyProp))).
Reify Pattern patterns_imp += (!! or) => (_Inj (inr (ILogicFunc.ilf_or tyProp))).
Reify Pattern patterns_imp += (RPi (?0) (?1)) => (fun (x : function reify_imp_typ) (y : function reify_imp) =>
                                                   ExprCore.App (_Inj (inr (ILogicFunc.ilf_forall tyProp x)))
                                                                (ExprCore.Abs x y)).
Reify Pattern patterns_imp += (RImpl (?0) (?1)) => (fun (x y : function reify_imp) => ExprCore.App (ExprCore.App (_Inj (inr (ILogicFunc.ilf_impl tyProp))) x) y).

(** Separation Logic Operators **)
Reify Pattern patterns_imp += (!! @BILogic.sepSP @ ?0 @ #) => (fun (x : function reify_imp_typ) => (fStar x)).
Reify Pattern patterns_imp += (!! @BILogic.empSP @ ?0 @ #) => (fun (x : function reify_imp_typ) => (fEmp x)).

(** Program Logic **)
Reify Pattern patterns_imp += (!! triple) => fTriple.
Reify Pattern patterns_imp += (!! eval_iexpr) => feval_iexpr.


Ltac reify_imp e :=
  let k e := pose e in
  reify_expr reify_imp k [ e ].

Goal True.
  reify_imp 1.
  reify_imp Skip.
  reify_imp (ILogic.lentails True True).
  reify_imp ((True -> False) -> True).
  reify_imp (forall G P Q, ILogic.lentails G (triple P Skip Q)).
  exact I.
Defined.