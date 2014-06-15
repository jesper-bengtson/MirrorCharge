Require Import MirrorCore.Lambda.Expr.
(** Java **)
Require Import Lang.

Axiom typ : Type.

(** TODO: These just have to be included into things **)
Inductive fcmd :=
| CSeq
| CInj : cmd -> fcmd
  (** This includes sequences.
   ** The previous constructor lets me take care of foreign terms
   **)
| Var : var -> fcmd
| Triple.

Axiom ext : Type.

Definition expr := expr typ (fcmd + ext).

(** The representation of formulas **)
Record predicate : Type :=
{ Exs : list typ
; Formula : expr (** TODO: I probably, ultimately, want a better representation **)
  (** TODO: This should probably also have information about variables **)
}.

Inductive FResult :=
| NoProgress
| Done : predicate -> FResult (** Done = Progress Skip **)
| Progress : expr -> predicate -> FResult.

Local Notation "a @ b" := (@ExprCore.App typ (fcmd + ext) a b) (at level 30).

(** TODO: Convert language expressions into logical expressions **)
Axiom dexpr_to_expr : dexpr -> predicate -> expr.

(** TODO: Simplification of predicates.
 ** - This shouldn't change the meaning at all, but should simplify the
 **   formula if there is any common work that is needed to post-process
 **   certain results. Good things to do here might be:
 **   - eliminate unnecessary variables & redundent equations
 **)
Definition predicate_simpl : predicate -> predicate :=
  fun P => P.

(** TODO: The result of reading a value from a predicate **)
Axiom do_read : expr -> field -> predicate -> option expr.
(** TODO: The result of writing a value in a predicate **)
Axiom do_write : expr -> field -> expr -> predicate -> option predicate.

(** TODO: The result of assigning to a stack variable.
 ** This will probably introduce an existential quantifier
 **)
Axiom do_assign : var -> expr -> predicate -> predicate.

Fixpoint forward_cmd (c : cmd) (P : predicate) : FResult :=
  match c with
    | cskip => Done P
    | cseq c1 c2 =>
      match forward_cmd c1 P with
        | NoProgress => NoProgress
        | Done Q => forward_cmd c2 Q
        | Progress c1' P' =>
          Progress (App (App (Inj (inl CSeq)) c1') (Inj (inl (CInj c2)))) P'
      end
    | cassign v e =>
      Done (do_assign v (dexpr_to_expr e P) P)
    | cassert e => NoProgress
    | cread v o f => (* v = o.f *)
      match do_read (dexpr_to_expr (E_var o) P) f P with
        | None => NoProgress
        | Some val => Done (do_assign v val P)
      end
    | cwrite v f e =>
      let e := dexpr_to_expr e P in
      match do_write (dexpr_to_expr (E_var v) P) f e P with
        | None => NoProgress
        | Some Q => Done Q
      end
    | _ => NoProgress (** TODO **)
  end.

Fixpoint forward (c : expr) (P : predicate) : FResult :=
  match c with
    | Inj (inl (CInj cmd)) =>
      forward_cmd cmd P
    | App (App (Inj (inl CSeq)) c1) c2 =>
      match forward c1 P with
        | NoProgress => NoProgress
        | Done Q => forward c2 Q
        | Progress c1' P' => Progress (App (App (Inj (inl CSeq)) c1') c2) P'
      end
    | _ => NoProgress
  end.