Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Tactics.Consider.

Require Import MirrorCore.TypesI.
Require Import MirrorCore.syms.SymEnv.
Require Import MirrorCore.Lambda.Expr.

Require Import Charge.Logics.ILogic.

Require Import Coq.Strings.String.

Require Import MirrorCharge.ModularFunc.ListType.
Require Import MirrorCharge.ModularFunc.BaseType.

Set Implicit Arguments.
Set Strict Implicit.
Set Maximal Implicit Insertion.

Open Scope string.

Open Scope list.

Fixpoint zip {A} {B} (lst1 : list A) (lst2 : list B) : list (A * B) :=
  match lst1, lst2 with
    | nil, nil => nil
    | x::xs, nil => nil
    | nil, y::ys => nil
    | x::xs, y::ys => (x, y) :: zip xs ys
  end.

Print combine.


Class ListFunc (typ func : Type) := {
  fNil  : typ -> func;
  fCons : typ -> func;
  fLength : typ -> func;
  fMap : typ -> typ -> func;
  fZip : typ -> typ -> func
}.

Section ListFuncSum.
	Context {typ func : Type} {H : ListFunc typ func}.

	Global Instance ListFuncSumL (A : Type) : 
		ListFunc typ (func + A) := {
		  fNil t := inl (fNil t);
	      fCons t := inl (fCons t);
	      fLength t := inl (fLength t);
          fMap t1 t2 := inl (fMap t1 t2);
          fZip t1 t2 := inl (fZip t1 t2)
        }.

	Global Instance ListFuncSumR (A : Type) : 
		ListFunc typ (A + func) := {
		  fNil t := inr (fNil t);
	      fCons t := inr (fCons t);
	      fLength t := inr (fLength t);
          fMap t1 t2 := inr (fMap t1 t2);
          fZip t1 t2 := inr (fZip t1 t2)
        }.

    Global Instance ListFuncExpr :
    	ListFunc typ (expr typ func) := {
    	  fNil t := Inj (fNil t);
    	  fCons t := Inj (fCons t);
    	  fLength t := Inj (fLength t);
    	  fMap t1 t2 := Inj (fMap t1 t2);
    	  fZip t1 t2 := Inj (fZip t1 t2)
    }.
        
End ListFuncSum.

Section ListFuncInst.
	Context {typ : Type} {HR : RType typ} 
	        {HTB : BaseType typ} {HTBD : BaseTypeD}
	        {HT : ListType typ} {HTD: ListTypeD}.
	Context {func : Type} {H : ListFunc typ func}.
	Context {Heq : RelDec (@eq typ)} {HC : RelDec_Correct Heq}.

    Variable Typ2_tyArr : Typ2 _ Fun.
    Variable Typ0_tyProp : Typ0 _ Prop.

    Let tyArr : typ -> typ -> typ := @typ2 _ _ _ _.
    Let tyProp : typ := @typ0 _ _ _ _.

	Inductive list_func :=
	  | pNil : typ -> list_func
	  | pCons : typ -> list_func
	  | pLength : typ -> list_func
	  | pMap : typ -> typ -> list_func
	  | pZip : typ -> typ -> list_func.

	Global Instance ListFuncInst : ListFunc typ list_func := {
	  fNil := pNil;
	  fCons := pCons;
	  fLength := pLength;
	  fMap := pMap;
	  fZip := pZip
	}.

	Definition typeof_list_func lf :=
		match lf with
		  | pNil t => Some (tyList t)
		  | pCons t => Some (tyArr t (tyArr (tyList t) (tyList t)))
		  | pLength t => Some (tyArr (tyList t) tyNat)
		  | pMap t1 t2 => Some (tyArr (tyArr t1 t2) (tyArr (tyList t1) (tyList t2)))
		  | pZip t1 t2 => Some (tyArr (tyList t1) (tyArr (tyList t2) (tyList (tyPair t1 t2))))
		end.

	Definition list_func_eq (a b : list_func) : option bool :=
	  match a , b with
	    | pNil t1, pNil t2 => Some (t1 ?[ eq ] t2)
	    | pCons t1, pCons t2 => Some (t1 ?[ eq ] t2)
	    | pLength t1, pLength t2 => Some (t1 ?[ eq ] t2)
	    | pMap t1 t2, pMap t3 t4 => Some (t1 ?[ eq ] t3 &&
	      								    t2 ?[ eq ] t4)%bool
	    | pZip t1 t2, pZip t3 t4 => Some (t1 ?[ eq ] t3 &&
	      								    t2 ?[ eq ] t4)%bool
	    | _, _ => None
	  end.

	 Definition list_func_symD lf :=
		match lf as lf return match typeof_list_func lf with
								| Some t => typD t
								| None => unit
							  end with
	    | pNil t => eq_rect_r id (@nil (typD t)) (btList t)
	    | pCons t => 
	       eq_rect_r id
             (eq_rect_r (fun T : Type => typD t -> T)
               (fun x xs => 
                    let xs := eq_rect _ id xs _ (btList t) in
                    eq_rect_r id (cons x xs) (btList t))
               (typ2_cast (tyList t) (tyList t)))
             (typ2_cast t (typ2 (tyList t) (tyList t)))
	    | pLength t => 
	        eq_rect_r id 
	          (fun lst : typD (tyList t) =>
	    	     let lst := eq_rect (typD (tyList t)) id lst (list (typD t)) (btList t) in
	    			        eq_rect_r id (List.length lst) btNat)
	          (typ2_cast (tyList t) (tyNat))
	    | pMap t1 t2 => 
	        eq_rect_r id 
	          (eq_rect_r (fun T : Type => typD (tyArr t1 t2) -> T)
	            (fun f lst =>
	              let f := eq_rect _ id f _ (typ2_cast t1 t2) in
	              let lst := eq_rect _ id lst _ (btList t1) in
	                eq_rect_r id (List.map f lst) (btList t2))
	            (typ2_cast (tyList t1) (tyList t2)))
	          (typ2_cast (tyArr t1 t2) (typ2 (tyList t1) (tyList t2)))
	    | pZip t1 t2 => 
	        eq_rect_r id 
	          (eq_rect_r (fun T : Type => typD (tyList t1) -> T)
	            (fun xs ys =>
	              let xs := eq_rect _ id xs _ (btList t1) in
	              let ys := eq_rect _ id ys _ (btList t2) in
	                eq_rect_r id (zip xs ys) 
	                  (eq_ind_r (fun T => T = list ((typD t1 * typD t2)%type))
	                    (eq_ind_r (fun T => list T = list ((typD t1 * typD t2)%type)) eq_refl
	                  	  (btPair t1 t2))
	                  	(btList (tyPair t1 t2))))
	            (typ2_cast (tyList t2) (tyList (tyPair t1 t2))))
	          (typ2_cast (tyList t1) (typ2 (tyList t2) (tyList (tyPair t1 t2))))
	 end.

	Global Instance RSym_ListFunc : SymI.RSym list_func := {
	  typeof_sym := typeof_list_func;
	  symD := list_func_symD;
	  sym_eqb := list_func_eq
	}.

	Global Instance RSymOk_ListFunc : SymI.RSymOk RSym_ListFunc.
	Proof.
		split; intros.
		destruct a, b; simpl; try apply I.
		+ consider (t ?[ eq ] t0); intuition congruence.
		+ consider (t ?[ eq ] t0); intuition congruence.
		+ consider (t ?[ eq ] t0); intuition congruence.
		+ consider (t ?[ eq ] t1 && t0 ?[ eq ] t2)%bool; intuition congruence. 
		+ consider (t ?[ eq ] t1 && t0 ?[ eq ] t2)%bool; intuition congruence. 
	Qed.

End ListFuncInst.

Section MakeList.
	Context {typ func : Type} {H : ListFunc typ func}.

	Definition mkNil := fNil.
	Definition mkCons (t : typ) (x xs : expr typ func) := App (App (fCons t) x) xs.
	Definition mkLength (t : typ) (lst : expr typ func) := App (fLength t) lst.
	Definition mkMap (t u : typ) (f lst : expr typ func) :=  App (App (fMap t u) f) lst.
	Definition mkZip (t u : typ) (xs ys : expr typ func) := App (App (fZip t u) xs) ys.
	
End MakeList.