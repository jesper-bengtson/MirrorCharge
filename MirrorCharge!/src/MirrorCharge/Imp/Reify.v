Require Import Coq.Lists.List.
Require Import MirrorCore.Reify.Reify.
Require Import MirrorCharge.Imp.Imp.
Require Import MirrorCharge.Imp.Syntax.

Reify Declare Patterns patterns_imp_typ := Syntax.typ.

Reify Declare Patterns patterns_imp := (ExprCore.expr Syntax.typ Syntax.func).

Reify Declare Syntax reify_imp_typ :=
  { (@Patterns.CPatterns Syntax.typ patterns_imp_typ) }.


Reify Declare Typed Table term_table : BinNums.positive => reify_imp_typ.

Let Ext x := @ExprCore.Inj Syntax.typ Syntax.func (inl (inl x)).

Reify Declare Syntax reify_imp :=
  { (@Patterns.CFirst _ ((@Patterns.CVar _ (@ExprCore.Var Syntax.typ Syntax.func)) ::
                         (@Patterns.CPatterns _ patterns_imp) ::
                         (@Patterns.CApp _ (@ExprCore.App Syntax.typ Syntax.func)) ::
                         (@Patterns.CAbs _ reify_imp_typ (@ExprCore.Abs Syntax.typ Syntax.func)) ::
                         (@Patterns.CTypedTable _ _ _ term_table Ext) :: nil))
  }.

Let _Inj := @ExprCore.Inj Syntax.typ Syntax.func.

Local Notation "x @ y" := (@RApp x y) (only parsing, at level 30).
Local Notation "'!!' x" := (@RExact _ x) (only parsing, at level 25).
Local Notation "'?' n" := (@RGet n RIgnore) (only parsing, at level 25).
Local Notation "'?!' n" := (@RGet n RConst) (only parsing, at level 25).
Local Notation "'#'" := RIgnore (only parsing, at level 0).

Reify Pattern patterns_imp_typ += (@RImpl (?0) (?1)) => (fun (a b : function reify_imp_typ) => tyArr a b).
Reify Pattern patterns_imp_typ += (!! locals)  => tyLocals.
Reify Pattern patterns_imp_typ += (!! lprop)  => (tyArr tyLocals tyHProp).
Reify Pattern patterns_imp_typ += (!! icmd) => tyCmd.
Reify Pattern patterns_imp_typ += (!! SProp) => tySProp.
Reify Pattern patterns_imp_typ += (!! HProp) => tyHProp.
Reify Pattern patterns_imp_typ += (!! Prop) => tyProp.
Reify Pattern patterns_imp_typ += (!! Imp.var) => tyVariable.
(*Reify Pattern patterns_imp_typ += (!! function_name) => tyVariable. *)
Reify Pattern patterns_imp_typ += (!! iexpr) => tyExpr.
Reify Pattern patterns_imp_typ += (!! nat)  => tyNat.
Reify Pattern patterns_imp_typ += (!! value)  => tyNat.
Reify Pattern patterns_imp_typ += (!! Fun @ ?0 @ ?1) => (fun (a b : function reify_imp_typ) => tyArr a b).
Reify Pattern patterns_imp_typ += (!! ILInsts.Fun @ ?0 @ ?1) => (fun (a b : function reify_imp_typ) => tyArr a b).


Reify Pattern patterns_imp += (RHasType var (?!0)) => (fun (x : id Imp.var) => fVar x).
Reify Pattern patterns_imp += (RHasType String.string (?!0)) => (fun (x : id Imp.var) => fVar x).
Reify Pattern patterns_imp += (RHasType nat (?!0)) => (fun (x : id nat) => fConst x).
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
Reify Pattern patterns_imp += (!! @ILogic.lexists @ ?0 @ # @ ?1) => (fun (x y : function reify_imp_typ) => (_Inj (inr (ILogicFunc.ilf_exists y x)))).
Reify Pattern patterns_imp += (!! @ILogic.lforall @ ?0 @ # @ ?1) => (fun (x y : function reify_imp_typ) => (_Inj (inr (ILogicFunc.ilf_forall y x)))).

(** Embedding Operators **)
Reify Pattern patterns_imp += (!! @ILEmbed.embed @ ?0 @ ?1 @ #) => (fun (x y : function reify_imp_typ) => (_Inj (inr (ILogicFunc.ilf_embed x y)))).

(** Special cases for Coq's primitives **)
Reify Pattern patterns_imp += (!! True) => (_Inj (inr (ILogicFunc.ilf_true tyProp))).
Reify Pattern patterns_imp += (!! False) => (_Inj (inr (ILogicFunc.ilf_false tyProp))).
Reify Pattern patterns_imp += (!! and) => (_Inj (inr (ILogicFunc.ilf_and tyProp))).
Reify Pattern patterns_imp += (!! or) => (_Inj (inr (ILogicFunc.ilf_or tyProp))).
Reify Pattern patterns_imp += (RPi (?0) (?1)) => (fun (x : function reify_imp_typ) (y : function reify_imp) =>
                                                   ExprCore.App (_Inj (inr (ILogicFunc.ilf_forall x tyProp )))
                                                                (ExprCore.Abs x y)).
Reify Pattern patterns_imp += (RImpl (?0) (?1)) => (fun (x y : function reify_imp) => ExprCore.App (ExprCore.App (_Inj (inr (ILogicFunc.ilf_impl tyProp))) x) y).

(** Separation Logic Operators **)
Reify Pattern patterns_imp += (!! @BILogic.sepSP @ ?0 @ #) => (fun (x : function reify_imp_typ) => (fStar x)).
Reify Pattern patterns_imp += (!! @BILogic.empSP @ ?0 @ #) => (fun (x : function reify_imp_typ) => (fEmp x)).

(** Program Logic **)
Reify Pattern patterns_imp += (!! triple) => fTriple.
Reify Pattern patterns_imp += (!! eval_iexpr) => feval_iexpr.
Reify Pattern patterns_imp += (!! locals_get) => flocals_get.
Reify Pattern patterns_imp += (!! locals_upd) => flocals_upd.

Reify Pattern patterns_imp += (!! PtsTo) => fPtsTo.

(** Applicative **)
Reify Pattern patterns_imp += (!! @Applicative.ap @ !! (ILInsts.Fun locals) @ # @ ?0 @ ?1) => (fun (x y : function reify_imp_typ) => (fAp x y)).
Reify Pattern patterns_imp += (!! @Applicative.pure @ !! (ILInsts.Fun locals) @ # @ ?0) => (fun (x : function reify_imp_typ) => (fPure x)).

(** Table Entries **)
Local Notation "a >> b" := (tyArr a b) (at level 31,right associativity).

Reify Seed Typed Table term_table += 1 => [ (tyLProp >> tyCmd >> tyLProp >> tySProp) , triple ].
Reify Seed Typed Table term_table += 2 => [ (tyCmd >> tyCmd >> tyCmd) , Seq ].
Reify Seed Typed Table term_table += 3 => [ (tyVariable >> tyExpr >> tyCmd) , Assign ].
Reify Seed Typed Table term_table += 4 => [ (tyVariable >> tyExpr >> tyCmd) , Read ].
Reify Seed Typed Table term_table += 5 => [ (tyExpr >> tyExpr >> tyCmd) , Write ].
Reify Seed Typed Table term_table += 6 => [ tyCmd , Skip ].
Reify Seed Typed Table term_table += 7 => [ (tyNat >> tyNat >> tyHProp) , PtsTo ].
(*
Reify Seed Typed Table term_table += 8 => [ (tyVariable >> (tyNat >> tyLProp) >> (tyNat >> tyLProp) >> tySProp) , function_spec ].
*)

Definition elem_ctor : forall x : Syntax.typ, (typD x) -> @SymEnv.function _ _ :=
  @SymEnv.F _ _.

Ltac reify_imp e :=
  let k fs e :=
      pose e in
  reify_expr reify_imp k
             [ (fun (y : @mk_dvar_map _ _ _ _ term_table elem_ctor) => True) ]
             [ e ].

Goal True.
  reify_imp 1.
  reify_imp Skip.
  reify_imp (ILogic.lentails True True).
  reify_imp ((True -> False) -> True).
  reify_imp (forall G P Q, ILogic.lentails G (triple P Skip Q)).
  generalize (String.EmptyString).
  intro x.
  exact I.
Defined.
