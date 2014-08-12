Require Import Coq.Strings.String.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Data.Fun.
Require Import Charge.Logics.ILogic.
Require Import Charge.Logics.BILogic.
Require Import Charge.Logics.ILEmbed.
Require Import Charge.Logics.ILInsts.
Require Import Charge.Logics.BILInsts.

Set Implicit Arguments.
Set Strict Implicit.

Definition var := string.
Definition value := nat.

Parameter iexpr : Type.
Parameter iConst : value -> iexpr.
Parameter iVar : var -> iexpr.

Parameter icmd : Type.

Parameter locals : Type.
Parameter locals_upd : var -> value -> locals -> locals.
Parameter locals_get : var -> locals -> value.
Parameter HProp : Type.
Parameter SProp : Type.
Instance ILogicOps_HProp : ILogicOps HProp. Admitted.
Instance ILogic_HProp : ILogic HProp. Admitted.
Instance BILogicOps_HProp : BILOperators HProp. Admitted.
Instance ILogicOps_SProp : ILogicOps SProp. Admitted.
Instance ILogic_SProp : ILogic SProp. Admitted.
Instance BILogicOps_SProp : BILOperators SProp. Admitted.

Definition lprop := locals -> HProp.

Local Instance Applicative_Fun A : Applicative (Fun A) :=
{ pure := fun _ x _ => x
; ap := fun _ _ f x y => (f y) (x y)
}.

Local Instance ILogicOps_lprop : ILogicOps lprop :=
  @ILFun_Ops locals HProp _.
Local Instance BILOps : BILOperators lprop :=
  @BILFun_Ops _ _ _.
Local Instance EmbedOp_Prop_HProp : EmbedOp Prop HProp. Admitted.
Local Instance EmbedOp_HProp_lprop : EmbedOp HProp lprop :=
  @EmbedILFunDropOp HProp _ (@EmbedOpId _) _.

Parameter eval_iexpr : iexpr -> locals -> value.

Parameter triple : lprop -> icmd -> lprop -> SProp.

(** Quantifier Rules **)
Axiom triple_exL
: forall G P c Q,
    (G |-- Forall x : value, triple (P x) c Q) ->
    G |-- triple (Exists x : value, P x) c Q.

Axiom triple_pureL
: forall (P : Prop) G c Q R,
    (P -> G |-- triple Q c R) ->
    G |-- triple (land (embed (embed P)) Q) c R.

(** Skip **)
Parameter Skip : icmd.

Axiom Skip_rule
: forall G P Q,
    P |-- Q ->
    G |-- triple P Skip Q.

(** Sequence **)
Parameter Seq : icmd -> icmd -> icmd.

Axiom Seq_rule
: forall G P Q R c1 c2,
    G |-- triple P c1 Q ->
    G |-- triple Q c2 R ->
    G |-- triple P (Seq c1 c2) R.

Axiom SeqA_rule
: forall G P Q c1 c2 c3,
    G |-- triple P (Seq c1 (Seq c2 c3)) Q ->
    G |-- triple P (Seq (Seq c1 c2) c3) Q.

(** Assignment **)
Parameter Assign : var -> iexpr -> icmd.

Axiom Assign_rule
: forall G P x e,
    G |-- triple P
                 (Assign x e)
                 (fun l => Exists v' : value,
                             embed (locals_get x l = eval_iexpr e l)
                       //\\  P  (locals_upd x v' l)).

(** Read **)
Parameter Read : var -> iexpr -> icmd.

Parameter PtsTo : value -> value -> HProp.

Axiom Read_rule
: forall G (P : lprop) x e (v : locals -> value),
    (P |-- ap (T := Fun locals) (ap (pure PtsTo) (eval_iexpr e)) v ** ltrue) ->
    G |-- triple P
                 (Read x e)
                 (fun l =>
                    Exists v' : value,
                          embed (locals_get x l = v (locals_upd x v' l))
                    //\\  P (locals_upd x v' l)).

(** Write **)
Parameter Write : iexpr -> iexpr -> icmd.

Axiom Write_rule
: forall G (P Q : lprop) p v,
    (P |-- Exists v', ap (T := Fun locals) (ap (pure PtsTo) (eval_iexpr p)) (pure v') ** Q) ->
    G |-- triple P
           (Write p v)
           (ap (T := Fun locals) (ap (pure PtsTo) (eval_iexpr p)) (eval_iexpr v) ** Q).

Definition function_name := string.

Parameter Call : function_name -> iexpr -> icmd.

Axiom function_spec : function_name -> (nat -> lprop) -> (nat -> lprop) -> SProp.

Axiom Call_rule
: forall G (P Q : lprop) (P' Q' : nat -> lprop) F f e v,
    (P |-- ap (T := Fun locals) (ap (pure PtsTo) (eval_iexpr e)) v ** ltrue) ->
    G |-- function_spec f P' Q' -> (** Get the method spec **)
    P |-- ap (T := Fun locals) (fun l v => P' v l) v ** F -> (* P |- P' ** F *)
    ap (T := Fun locals) (fun l v => Q' v l) v ** F |-- Q -> (* Q' ** F |- Q *)
    G |-- triple P
                 (Call f e)
                 Q.