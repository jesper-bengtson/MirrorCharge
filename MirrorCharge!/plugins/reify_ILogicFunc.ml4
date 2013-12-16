(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

open Reify_gen
open Reify_ext
open Plugin_utils.Term_match

let contrib_name = "reify_MirrorCharge.ILogicFunc"

module Std = Plugin_utils.Coqstd.Std (struct let contrib_name = contrib_name end)

let resolve_symbol = Std.resolve_symbol
let to_positive = Std.to_positive

(** The extension type **)
let ilfunc_pkg = [(*"MirrorCharge";*)"ILogicFunc"]

let func = lazy (resolve_symbol ilfunc_pkg "ilfunc")

let ilogic_pkg = [(*"Charge";*)"Logics";"ILogic"]
let tm_true = lazy (resolve_symbol ilogic_pkg "ltrue")
let tm_false = lazy (resolve_symbol ilogic_pkg "lfalse")
let tm_entails = lazy (resolve_symbol ilogic_pkg "lentails")
let tm_and = lazy (resolve_symbol ilogic_pkg "land")
let tm_or = lazy (resolve_symbol ilogic_pkg "lor")
let tm_impl = lazy (resolve_symbol ilogic_pkg "limpl")
let tm_forall = lazy (resolve_symbol ilogic_pkg "lforall")
let tm_exists = lazy (resolve_symbol ilogic_pkg "lexists")
let tm_embed = lazy (resolve_symbol ilogic_pkg "lexists")

module ExprBuilder = Reify_ext.ExprBuilder (struct let ext_type = func end)

module REIFY_MONAD =
struct
  type 'a m = Environ.env ->
    Evd.evar_map ->
    (bool list) ->
    (** Type class environment
     ** - This is [map <reified_type, type_class_instance>]
     ** - For now we'll assume that all types are constructed
     **   in the same way
     **)
    ((Term.constr, Term.constr) Hashtbl.t) ->
    (Term.constr list) ref ->
    (Term.constr option list) ref ->
    (Term.constr option list) ref -> 'a

  let ret (x : 'a) : 'a m =
    fun _ _ _ _ _ _ _ -> x

  let bind (c : 'a m) (f : 'a -> 'b m) : 'b m =
    fun e em look w z x y ->
      let b = c e em look w z x y in
      f b e em look w z x y

  let ask_env = fun e _ _ _ _ _ _ -> e
  let local_env f c = fun e -> c (f e)

  let get_logic_typeclasses = fun _ _ _ t _ _ _ -> t

  let under_type bind_no_bind c =
    fun e em look ->
      c e em (bind_no_bind :: look)
  let lookup_type n =
    let rec go n ls =
      match ls with
	[] -> assert false
      | l :: ls ->
	if n = 1 then
	  let _ = assert (l = true) in 0
	else if n > 1 then
	  let res = go (n - 1) ls in
	  if l then res + 1 else res
	else
	  assert false
    in
    fun _ _ look _ _ _ _ -> go n look

  let ask_evar = fun _ e _ _ _ _ _ -> e
  let local_evar _ _ = fun _ _ _ _ _ _ _ -> assert false

  let get_types = fun _ _ _ _ _ ts _ -> !ts
  let put_types ts = fun _ _ _ _ _ rts _ -> rts := ts

  let get_funcs = fun _ _ _ _ _ _ fs -> !fs
  let put_funcs fs = fun _ _ _ _ _ _ rfs -> rfs := fs

  let get_evars = fun _ _ _ _ fs _ _ -> !fs
  let put_evars fs = fun _ _ _ _ rfs _ _ -> rfs := fs

  let runM (c : 'a m) ts fs tcs evs e em : ('a * Term.constr option list * Term.constr option list * Term.constr list) =
    let ts = ref ts in
    let fs = ref fs in
    let evs = ref evs in
    let res = c e em [] tcs evs ts fs in
    (res, !ts, !fs, !evs)
end

(** To reify types **)
module ReifyExtTypes =
  Reify_ext.ReifyExtTypes (REIFY_MONAD)

module REIFY_ENV_FUNC =
  ReifyEnvOption (REIFY_MONAD)
    (struct
      type state = Term.constr option list
      type 'a m = 'a REIFY_MONAD.m
      let put = REIFY_MONAD.put_funcs
      let get = REIFY_MONAD.get_funcs
     end)

module ReifyILFunc
: REIFY with type 'a m = 'a REIFY_MONAD.m
        with type result = Term.constr =
struct
  module M = REIFY_MONAD

  type 'a m = 'a M.m
  type result = Term.constr

  let tc_ilogicops_prop = lazy (resolve_symbol ilogic_pkg "ILogicOps_Prop")

  let reify_typeclass rt tc =
    M.bind M.get_logic_typeclasses (fun ltc ->
      try
	let res = Hashtbl.find ltc rt in
	if Term.eq_constr tc res then
	  M.ret true
	else
	  M.bind M.ask_env (fun env ->
	    M.bind M.ask_evar (fun evar ->
	      M.ret (Reductionops.is_conv env evar tc res)))
      with
	Not_found ->
	  let _ = Hashtbl.add ltc rt tc in
	  M.ret true)

  let build_for_typeclass t tc f =
    M.bind (ReifyExtTypes.reify t) (fun rt ->
      M.bind (reify_typeclass rt tc) (fun tc ->
	if tc then
	  M.ret (Term.mkApp (Lazy.force f, [| rt |]))
	else
	    (** This slot is already taken **)
	  assert false))

  let build_for_typeclass_quant t tc tq f =
    M.bind (ReifyExtTypes.reify t) (fun rt ->
      M.bind (reify_typeclass rt tc) (fun tc ->
	if tc then
	  M.bind (ReifyExtTypes.reify tq) (fun rtq ->
	    M.ret (Term.mkApp (Lazy.force f, [| rt ; rtq |])))
	else
	  (** This slot is already taken **)
	  assert false))

  let expr_true = lazy (resolve_symbol ilfunc_pkg "ilf_true")
  let expr_false = lazy (resolve_symbol ilfunc_pkg "ilf_false")
  let expr_entails = lazy (resolve_symbol ilfunc_pkg "ilf_entails")
  let expr_and = lazy (resolve_symbol ilfunc_pkg "ilf_and")
  let expr_or = lazy (resolve_symbol ilfunc_pkg "ilf_or")
  let expr_impl = lazy (resolve_symbol ilfunc_pkg "ilf_impl")
  let expr_exists = lazy (resolve_symbol ilfunc_pkg "ilf_exists")
  let expr_forall = lazy (resolve_symbol ilfunc_pkg "ilf_forall")
  let expr_embed = lazy (resolve_symbol ilfunc_pkg "ilf_embed")
  let expr_fref = lazy (resolve_symbol ilfunc_pkg "ilf_fref")

  let class_binary_assoc =
    [(tm_true, expr_true); (tm_false, expr_false);
     (tm_and, expr_and); (tm_or, expr_or); (tm_impl, expr_impl);
     (tm_entails, expr_entails)]

  let class_quant_assoc =
    [(tm_exists, expr_exists); (tm_forall, expr_forall)]

  let class_binary_operators =
    Choice (List.map (fun (x,_) -> Glob x) class_binary_assoc)

  let class_quant_operators =
    Choice (List.map (fun (x,_) -> Glob x) class_quant_assoc)

  let get nm = As (Ignore, nm)

  let tm_and_prop = lazy (resolve_symbol ["Coq";"Init";"Logic"] "and")
  let tm_or_prop = lazy (resolve_symbol ["Coq";"Init";"Logic"] "or")
  let prop = Term.mkProp

  let reify (tm : Term.constr) : result m =
    M.bind (M.ask_env) (fun ctx ->
      matches ctx
	[ (App (App (As (class_binary_operators, "op") , get "t"), get "tc"),
	   fun s ->
	     let op = Hashtbl.find s "op" in
	     let t = Hashtbl.find s "t" in
	     let tc = Hashtbl.find s "tc" in
	     let (_,ctor) =
	       List.find
		 (fun (x,_) -> Term.eq_constr op (Lazy.force x))
		 class_binary_assoc
	     in
	     build_for_typeclass t tc ctor)
	; (App (App (App (As (class_quant_operators, "op"), get "t"), get "tc"), get "ty"),
	   fun s ->
	     let op = Hashtbl.find s "op" in
	     let t = Hashtbl.find s "t" in
	     let tc = Hashtbl.find s "tc" in
	     let ty = Hashtbl.find s "ty" in
	     let (_,ctor) =
	       List.find
		 (fun (x,_) -> Term.eq_constr op (Lazy.force x))
		 class_quant_assoc
	     in
	     build_for_typeclass_quant t tc ty ctor)
	; (Glob tm_and_prop,
	   fun _ ->
	     build_for_typeclass prop (Lazy.force tc_ilogicops_prop) expr_and)
	; (Glob tm_or_prop,
	   fun _ ->
	     build_for_typeclass prop (Lazy.force tc_ilogicops_prop) expr_or)
        ; (Ignore,
	   fun _ ->
	     (** TODO: Add a case for seeing Prod, this isn't supported by
	      **       Term_match at the moment.
	      **)
	     M.bind (REIFY_ENV_FUNC.reify tm) (fun t ->
	       let idx = to_positive (1 + t) in
	       M.ret (Term.mkApp (Lazy.force expr_fref, [| idx |]))))
	]
	tm)
end

module REIFY_MONAD_READ_ENV =
struct
  type env = Environ.env
  type 'a m = 'a REIFY_MONAD.m
  let local = REIFY_MONAD.local_env
  let ask = REIFY_MONAD.ask_env
end

module REIFY_MONAD_READ_EVAR =
struct
  type env = Evd.evar_map
  type 'a m = 'a REIFY_MONAD.m
  let local = REIFY_MONAD.local_evar
  let ask = REIFY_MONAD.ask_evar
end

module REIFY_APP_WITH_TYPECLASS =
struct
  type result = Term.constr
  type 'a m = 'a REIFY_MONAD.m

  module DELEGATE = ReifyAppDep (REIFY_MONAD)
    (REIFY_MONAD_READ_ENV) (REIFY_MONAD_READ_EVAR)
    (ReifyILFunc)

  let proj_and_args =
    [(tm_true, 2);
     (tm_false, 2);
     (tm_entails, 2);
     (tm_and, 2);
     (tm_or, 2);
     (tm_impl, 2);
     (tm_forall, 3);
     (tm_exists, 3);
     (tm_embed, 3)]

  let reify_app (no_progress : result m Lazy.t)
      (reify_expr : Term.constr -> result m)
      (build_app : result -> result list -> result m)
      (t : Term.constr) (ts : Term.constr array) =
    (** The only reason that I need to special-case this is that
     ** the type class instance is not dependent, so I need to look
     ** at the head symbol and determine if it is a type class
     ** function that I understand and then reify appropriately given
     ** the arguments
     **)
    try
      let (res, cnt) =
	List.find (fun (x,_) -> Term.eq_constr t (Lazy.force x)) proj_and_args
      in
      let ary_len = Array.length ts in
      if cnt = ary_len then
	ReifyILFunc.reify (Term.mkApp (t,ts))
      else if cnt > ary_len then
	Array.fold_left (fun acc x ->
	  REIFY_MONAD.bind acc (fun acc ->
	    REIFY_MONAD.bind (reify_expr x) (fun x ->
	      REIFY_MONAD.ret (ExprBuilder.mkApp acc x))))
	  (ReifyILFunc.reify (Term.mkApp (t,Array.sub ts 0 cnt)))
	  (Array.sub ts cnt (ary_len - cnt))
      else
	assert false (** We can't reify this term **)
    with
      Not_found ->
	(** this isn't a type-class function, so we just do the usual thing **)
	DELEGATE.reify_app no_progress reify_expr build_app t ts
end

module ReifyExtILFunc
: REIFY with type 'a m = 'a REIFY_MONAD.m
        with type result = Term.constr =
  ReifyExpr
    (REIFY_MONAD)
    (REIFY_MONAD_READ_ENV)
    (ExprBuilder)
    (ReifyExtTypes)
    (ReifyILFunc)
    (ReifyEnv (REIFY_MONAD)
      (struct
	type state = Term.constr list
	type 'a m = 'a REIFY_MONAD.m
	let put = REIFY_MONAD.put_evars
	let get = REIFY_MONAD.get_evars
       end))
    (REIFY_APP_WITH_TYPECLASS)
;;

(** extract the values from an environment **)
let types_empty = lazy (resolve_symbol ["MirrorCore";"Ext";"Types"] "TEemp")
let types_branch = lazy (resolve_symbol ["MirrorCore";"Ext";"Types"] "TEbranch")

let mapM (f : 'a -> 'b REIFY_MONAD.m) =
  let rec mapM (ls : 'a list) : 'b list REIFY_MONAD.m =
    match ls with
      [] -> REIFY_MONAD.ret []
    | l :: ls -> REIFY_MONAD.bind (f l) (fun l ->
      REIFY_MONAD.bind (mapM ls) (fun ls ->
	REIFY_MONAD.ret (l :: ls)))
  in mapM

(*
let mkFunction = lazy (resolve_symbol ["MirrorCore";"Ext";"SymEnv"] "F")

(** reify ML-style function types **)
let reify_function_scheme reify_type =
  let rec reify_function_scheme n ft =
    match Term.kind_of_term ft with
      Term.Prod (_,t1,t2) ->
	if Term.noccurn 1 t2 then
	  (** It is a lambda **)
	  REIFY_MONAD.bind
	    (REIFY_MONAD.under_type true (reify_type ft)) (fun rft ->
	    REIFY_MONAD.ret (n, rft))
	else
	  reify_function_scheme (1+n) t2
    | _ ->
      REIFY_MONAD.bind (reify_type ft) (fun rft ->
	REIFY_MONAD.ret (n, rft))
  in reify_function_scheme 0

let build_functions evar env : (Term.constr -> Term.constr) list REIFY_MONAD.m =
  let do_func f =
    match f with
      None -> assert false (** TODO **)
    | Some f ->
      let tf = Typing.type_of env evar f in
      REIFY_MONAD.bind (reify_function_scheme ReifyExtTypes.reify tf) (fun (n, rft) ->
	REIFY_MONAD.ret (fun ts ->
	  Term.mkApp (Lazy.force mkFunction,
		      [| ts ; Std.to_nat n ; rft ; f |])))
  in
  REIFY_MONAD.bind REIFY_MONAD.get_funcs (fun fs ->
    mapM do_func fs)
*)

let build_functions evar env : (Term.constr -> Term.constr) list REIFY_MONAD.m =
  REIFY_MONAD.ret []

(** TODO: Move this **)
let extract_types (ls : Term.constr option list) =
  let rtype = Term.mkSort (Term.Type (Termops.new_univ ())) in
  Std.to_posmap (Lazy.force types_empty)
    (fun a b c ->
      Term.mkApp (Lazy.force types_branch,
		  [| a ; Std.to_option rtype b ; c |]))
    (fun x -> x) ls
;;

let ctor_branch =
  lazy (resolve_symbol ["Coq";"FSets";"FMapPositive";"PositiveMap"] "Node")

let ctor_leaf =
  lazy (resolve_symbol ["Coq";"FSets";"FMapPositive";"PositiveMap"] "Leaf")

let e_function =
  lazy (resolve_symbol ilfunc_pkg "function")

(** the simplest version of the tactic will just construct the version of the
 ** environment and return that with the expression.
 ** NOTE: In the future, we'll need to write more plugins to do more specialized
 **       instantiation
 **)
TACTIC EXTEND reify_Ext_SymEnv_reify_expr
  | ["reify_expr" constr(e) tactic(k) ] ->
    [ fun gl ->
        let env = Tacmach.pf_env gl in
	let evar_map = Tacmach.project gl in
	let i_types = [] in
	let i_funcs = [] in
	let i_tcs = Hashtbl.create 3 in
        let (res, r_types, r_funcs) =
	  let cmd = REIFY_MONAD.bind (ReifyExtILFunc.reify e) (fun re ->
	    REIFY_MONAD.bind (build_functions evar_map env) (fun fs ->
	      REIFY_MONAD.ret (re, fs)))
	  in
	  let ((res, r_funcs), r_types, _, r_evars) =
	    REIFY_MONAD.runM cmd i_types i_funcs i_tcs [] env evar_map in
	  (res, r_types, r_funcs)
	in
	let r_types = extract_types r_types in
	Plugin_utils.Use_ltac.pose "types" r_types (fun r_types ->
	  let typ = Term.mkApp (Lazy.force e_function, [| r_types |]) in
	  let leaf = Term.mkApp (Lazy.force ctor_leaf, [| typ |]) in
	  let r_funcs = Std.to_posmap leaf
	    (fun a b c ->
	      Term.mkApp (Lazy.force ctor_branch, [| typ ; a ; Std.to_option typ b ; c |]))
	    (fun f -> Some (f r_types)) r_funcs in
	  Plugin_utils.Use_ltac.pose "funcs" r_funcs (fun r_funcs ->
	    let ltac_args = List.map Plugin_utils.Use_ltac.to_ltac_val [r_types; r_funcs; res] in
	    Plugin_utils.Use_ltac.ltac_apply k ltac_args)) gl
    ]
END;;
