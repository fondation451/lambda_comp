open Lambda;;

exception Type_Error of string;;
exception Mutual_Def;;

(* ALGORITHM W *)

module IntSet = Set.Make(struct
  type t = int;;
  let compare = compare;;
end);;

let intset_str intset =
  "[" ^ (IntSet.fold (fun a out -> out ^ (Printf.sprintf "alpha%d, " a)) intset "") ^ "]"
;;

module IntMap = Map.Make(struct
  type t = int;;
  let compare = compare;;
end);;

module VarMap = Map.Make(struct
  type t = Atom.atom;;
  let compare = Atom.compare;;
end);;

type type_mono =
  |TAlpha of int
  |TInt
  |TFun of type_mono * type_mono
and type_poly =
  |TPoly of int list * type_mono
[@@deriving show { with_path = false }]
;;

let intmap_str intmap =
  "[" ^ (IntMap.fold (fun a mty out -> out ^ (Printf.sprintf "alpha%d : %s, " a (show_type_mono mty))) intmap "") ^ "]"
;;

let varmap_str varmap =
  "[" ^ (VarMap.fold (fun var ty out -> out ^ (Printf.sprintf "%s%d : %s, " (Atom.hint var) (Atom.identity var) (show_type_poly ty))) varmap "") ^ "]"
;;

let mk_alpha =
  let cpt = ref 0 in fun () -> incr cpt; !cpt
;;

let fv_mty mty =
  let rec loop mty out =
    match mty with
    |TAlpha(a) -> IntSet.add a out
    |TInt -> out
    |TFun(mty1, mty2) -> loop mty1 (loop mty2 out)
  in loop mty IntSet.empty
;;

let fv_mty_l mty_l = List.fold_left (fun out mty -> IntSet.union (fv_mty mty) out) IntSet.empty mty_l;;

let fv_ty (TPoly(alpha_l, mty)) = IntSet.diff (fv_mty mty) (IntSet.of_list alpha_l);;

let fv_ty_l ty_l = List.fold_left (fun out ty -> IntSet.union (fv_ty ty) out) IntSet.empty ty_l;;

let rec apply_m s mty =
  match mty with
  |TAlpha(a) -> (try IntMap.find a s with Not_found -> TAlpha(a))
  |TInt -> TInt
  |TFun(mty1, mty2) -> TFun(apply_m s mty1, apply_m s mty2)
;;

let apply s (TPoly(alpha_l, mty)) = TPoly(alpha_l, apply_m (List.fold_left (fun out a -> IntMap.remove a out) s alpha_l) mty);;

let subs_empty = IntMap.empty;;

let compose_subs s1 s2 = IntMap.union (fun alpha mty1 mty2 -> Some(mty1)) (IntMap.map (apply_m s1) s2) s1;;

let remove_env env var = VarMap.remove var env;;

let fv_env env = fv_ty_l (List.rev_map snd (VarMap.bindings env));;

let apply_env s env = VarMap.map (apply s) env;;

let generalize env mty = TPoly(IntSet.elements (IntSet.diff (fv_mty mty) (fv_env env)), mty);;

let instanciate (TPoly(alpha_l, mty)) =
  let alpha_l_ty = List.rev_map (fun _ -> TAlpha(mk_alpha ())) alpha_l in
  let s = List.fold_left2 (fun out alpha ty_alpha -> IntMap.add alpha ty_alpha out) IntMap.empty alpha_l alpha_l_ty in
  apply_m s mty
;;

let varbind alpha mty =
  match mty with
  |TAlpha(alpha') when alpha = alpha' -> subs_empty
  |_ ->
    if IntSet.mem alpha (fv_mty mty) then
      raise (Type_Error(Printf.sprintf "Varbind : alpha%d occurs in %s      %s" alpha (show_type_mono mty) (intset_str (fv_mty mty))))
    else
      IntMap.singleton alpha mty
;;

let rec mgu mty1 mty2 =
  Printf.printf "Mgu %s    ||||    %s\n\n\n" (show_type_mono mty1) (show_type_mono mty2);
  match mty1, mty2 with
  |TInt, TInt -> subs_empty
  |TAlpha(a1), _ -> varbind a1 mty2
  |_, TAlpha(a2) -> varbind a2 mty1
  |TFun(src1, dst1), TFun(src2, dst2) ->
    let s1 = mgu src1 src2 in
    Printf.printf "---- s1 = %s\n\n" (intmap_str s1);
    let s2 = mgu (apply_m s1 dst1) (apply_m s1 dst2) in
    Printf.printf "---- s2 = %s\n\n" (intmap_str s2);
    compose_subs s1 s2
  |_ -> raise (Type_Error("Mgu"))
;;

let rec type_infer env t =
  Printf.printf "Type_infer %s\n\n\n" (show_term t);
  match t with
  |Var(var) -> (try subs_empty, instanciate (VarMap.find var env) with Not_found -> raise (Type_Error("Type_infer")))
  |Lit(_) -> subs_empty, TInt
  |Lam(s, var, e) ->
    let env =
      match s with
      |Self(f_var) ->
        let alpha = mk_alpha () in
        let env' = remove_env env f_var in
        VarMap.union (fun v ty1 ty2 -> Some(ty2)) env' (VarMap.singleton f_var (TPoly([], TAlpha(alpha))))
      |_ -> env
    in
    let alpha = mk_alpha () in
    let env' = remove_env env var in
    let env'' = VarMap.union (fun v ty1 ty2 -> Some(ty2)) env' (VarMap.singleton var (TPoly([], TAlpha(alpha)))) in
    let s1, t1 = type_infer env'' e in
    s1, TFun(apply_m s1 (TAlpha(alpha)), t1)
  |App(e1, e2) ->
    Printf.printf "typing App\n";
    Printf.printf "env1 : %s\n\n" (varmap_str env);
    let alpha = mk_alpha () in
    let s1, t1 = type_infer env e1 in
    Printf.printf "t1 : %s\n\n" (show_type_mono t1);
    Printf.printf "s1 : %s\n\n" (intmap_str s1);
    let s2, t2 = type_infer (apply_env s1 env) e2 in
    Printf.printf "t2 : %s\n\n" (show_type_mono t2);
    Printf.printf "s2 : %s\n\n" (intmap_str s2);
    let s3 = mgu (apply_m s2 t1) (TFun(t2, TAlpha(alpha))) in
    compose_subs s3 (compose_subs s2 s1), apply_m s3 (TAlpha(alpha))
  |Let(var, e1, e2) ->
    let s1, t1 = type_infer env e1 in
    let env' = remove_env env var in
    let t' = generalize (apply_env s1 env) t1 in
    let env'' = VarMap.add var t' env' in
    let s2, t2 = type_infer (apply_env s1 env'') e2 in
    compose_subs s1 s2, t2
  |BinOp(e1, op, e2) ->
    let s1, t1 = type_infer env e1 in
    let s2, t2 = type_infer (apply_env s1 env) e2 in
    let s3 = mgu (apply_m s1 t1) TInt in
    let s4 = mgu (apply_m s2 t2) TInt in
    compose_subs s1 (compose_subs s2 (compose_subs s3 s4)), TInt
  |Print(e1) ->
    let s1, t1 = type_infer env e1 in
    let s2 = mgu (apply_m s1 t1) TInt in
    compose_subs s1 s2, TInt
  |IfZero(e1, e2, e3) ->
    let s1, t1 = type_infer env e1 in
    let s1' = mgu (apply_m s1 t1) TInt in
    let s2, t2 = type_infer (apply_env s1 env) e2 in
    let s3, t3 = type_infer (apply_env s1 env) e3 in
    let s4 = mgu (apply_m s2 t2) (apply_m s3 t3) in
    compose_subs s1' (compose_subs s2 (compose_subs s3 s4)), apply_m s4 t2
  |BeginMutual(e1) -> raise Mutual_Def
;;

let type_inference env t =
  try
    let s, t = type_infer env t in
    apply_m s t
  with Mutual_Def -> TInt
;;

let type_term t =
  let ty = type_inference VarMap.empty t in
(*  Printf.printf "TYPAGE : %s\n\n\n" (show_type_mono ty);*)
  t
;;
