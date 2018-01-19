(* The source calculus. *)
module S = Tail
(* The target calculus. *)
module T = Top

module VarMap = Map.Make(struct
  type t = Atom.atom;;
  let compare = Atom.compare;;
end);;

let fun_apply = Atom.fresh "apply";;
let this_apply = Atom.fresh "this_apply";;
let that_apply = [Atom.fresh "that1_apply" ; Atom.fresh "that2_apply"];;
let apply_nb_arg = List.length that_apply;;

let mk_tag =
  let cpt = ref 0 in fun () -> incr cpt; !cpt
;;

(*
and term =
  | Exit
  | TailCall of variable * value list
  | Print of value * term
  | LetVal of variable * value * term
  | LetBlo of variable * block * term
  | Swi of value * branch list

and block =
  | Con of tag * value list *)
(*
let find_fv_value fv var_env =
  let rec loop fv out =
    match fv with
    |[] -> List.rev out
    |var::t -> try
(*      Printf.printf "LOOKING FOR VAR %s\n\n" (Atom.hint var);*)
      let tmp = VarMap.find var var_env in
      match tmp with
      |T.VVar(_) -> loop t ((T.VVar(var))::out)
      |_ -> loop t (tmp::out)
    with Not_found -> assert false
  in loop fv []
;;
*)
let normalize_fun_arg var_l =
  let rec loop var_l len =
    if len >= apply_nb_arg then
      List.rev var_l
    else
      loop ((Atom.fresh "__dumb__arg__")::var_l) (len+1)
  in loop (List.rev var_l) (List.length var_l)
;;

let normalize_fun_call v_l =
  let rec loop v_l len =
    if len >= apply_nb_arg then
      List.rev v_l
    else
      loop ((T.VLit(0))::v_l) (len+1)
  in loop (List.rev v_l) (List.length v_l)
;;

let rec defun t evar efun apply lambda =
  match t with
  |S.Exit -> T.Exit, evar, efun, apply
  |S.TailCall(v, v_l) -> begin
    match v with
    |S.VVar(var) -> T.TailCall(fun_apply, (T.VVar(var))::(normalize_fun_call v_l)), evar, efun, apply
    |S.VLit(_) |S.VBinOp(_) -> assert false
  end
  |S.Print(v, t') ->
    let t'', evar, efun, apply = defun t' evar efun apply lambda in
    T.Print(v, t''), evar, efun, apply
  |S.LetVal(var, v, t') ->
    let evar = VarMap.add var v evar in
    let t'', evar, efun, apply = defun t' evar efun apply lambda in
    T.LetVal(var, v, t''), evar, efun, apply
  |S.LetBlo(var, b, t') ->
    let S.Lam(s, var_l, t_lam) = b in
    let tag = mk_tag () in
    let fv =
      match s with
      |S.Self(fix) -> fix::(Atom.Set.elements (S.fv_block b))
      |_ -> Atom.Set.elements (S.fv_block b)
    in
    let evar_lam =
      match s with
      |S.Self(fix) -> List.fold_left (fun out arg -> VarMap.add arg (T.VVar(arg)) out) evar (fix::var_l)
      |_ -> List.fold_left (fun out arg -> VarMap.add arg (T.VVar(arg)) out) evar var_l
    in
    let t_lam', evar, efun, apply = defun t_lam evar_lam efun apply lambda in
    let t_lam' = List.fold_right2 (fun arg that out -> T.LetVal(arg, T.VVar(that), out)) (normalize_fun_arg var_l) that_apply t_lam' in
    let branch = T.Branch(tag, fv, t_lam') in
    let efun = VarMap.add var (tag, fv) efun in
    let evar = VarMap.add var (T.VVar(var)) evar in
    let t'', evar, efun, apply = defun t' evar efun (branch::apply) lambda in
(*    Printf.printf "FV fun : %s%d : \n" (Atom.hint var) (Atom.identity var);
    List.iter (fun var -> Printf.printf "| %s%d |" (Atom.hint var) (Atom.identity var)) fv;
    Printf.printf "\n";*)
    T.LetBlo(var, T.Con(tag, List.map (fun var -> T.VVar(var)) fv(*find_fv_value fv evar*)), t''), evar, efun, apply
  |S.IfZero(v, t1, t2) ->
    let t1', evar, efun, apply = defun t1 evar efun apply lambda in
    let t2', evar, efun, apply = defun t2 evar efun apply lambda in
    T.IfZero(v, t1', t2'), evar, efun, apply
;;

let mk_apply apply = T.Fun(fun_apply, this_apply::that_apply, T.Swi(T.VVar(this_apply), apply));;

let defun_term (t : S.term) : T.program =
  let t', _, _, apply = defun t VarMap.empty VarMap.empty [] [] in
  T.Prog([mk_apply apply], t')
;;
