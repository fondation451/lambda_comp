(* The source calculus. *)
module S = Lambda
(* The target calculus. *)
module T = Tail

let mk_fun () = Atom.fresh "fun";;

let var_eq = Atom.equal;;

let to_tail_value t =
  match t with
  |S.Var(v) -> T.VVar(v)
  |S.Lit(i) -> T.VLit(i)
  |_ -> assert false
;;

let rec subs_val v var v_tg =
  let subs var_src var v_src v_tg = if var_eq var_src var then v_tg else v_src in
  match v with
  |T.VVar(var1) -> subs var1 var v v_tg
  |T.VLit(_) -> v
  |T.VBinOp(v1, op, v2) -> T.VBinOp(subs_val v1 var v_tg, op, subs_val v2 var v_tg)
;;

let rec substitution t1 x v_tg =
  match t1 with
  |T.Exit -> t1
  |T.TailCall(v, v_l) -> T.TailCall(subs_val v x v_tg, List.map (fun v -> subs_val v x v_tg) v_l)
  |T.Print(v, t) -> T.Print(subs_val v x v_tg, substitution t x v_tg)
  |T.LetVal(varia, v, t) -> T.LetVal(varia, subs_val v x v_tg, substitution t x v_tg)
  |T.LetBlo(varia, T.Lam(s, var_l, t_lam), t) -> T.LetBlo(varia, T.Lam(s, var_l, substitution t_lam x v_tg), substitution t x v_tg)
  |T.IfZero(v, t1, t2) -> T.IfZero(subs_val v x v_tg, substitution t1 x v_tg, substitution t2 x v_tg)
;;

type lambda_value =
  |LAMBVAL of T.value
  |LAMBLAM of T.self * T.variable list * T.term
;;

type continuation =
  |COBJ of T.variable
  |META of S.variable * T.term
;;

let apply c v namespace =
  match c with
  |COBJ(k) -> begin
    match v with
    |LAMBVAL(v') -> T.TailCall(T.VVar(k), [v'])
    |LAMBLAM(s, var_l, t') ->
      let f_anonymous = namespace in
      T.LetBlo(f_anonymous, T.Lam(s, var_l, t'), T.TailCall(T.VVar(k), [T.VVar(f_anonymous)]))
  end
  |META(x, t) -> begin
    match v with
    |LAMBVAL(v') -> substitution t x v'
    |LAMBLAM(s, var_l, t') ->
      let f_anonymous = namespace in
      T.LetBlo(f_anonymous, T.Lam(s, var_l, t'), substitution t x (T.VVar(f_anonymous)))
  end
;;

let reify c =
  match c with
  |COBJ(t) -> LAMBVAL(T.VVar(t))
  |META(x, t) -> LAMBLAM(T.NoSelf, [x], t)
;;

let rec cps_lambda t c namespace =
  match t with
  |S.Var(v) -> apply c (LAMBVAL(T.VVar(v))) namespace
  |S.Lit(i) -> apply c (LAMBVAL(T.VLit(i))) namespace
  |S.Lam(s, v, t') ->
    let k = Atom.fresh "k" in
    let new_namespace = Atom.fresh (Atom.hint namespace) in
    apply c (LAMBLAM(s, [v ; k], cps_lambda t' (COBJ (k)) new_namespace)) namespace
  |S.App(t1, t2) -> begin
    let x1 = Atom.fresh "x1" in
    let x2 = Atom.fresh "y2" in
    match reify c with
    |LAMBVAL(k) ->
      cps_lambda t1 (META(x1, cps_lambda t2 (META(x2, T.TailCall(T.VVar(x1), [T.VVar(x2) ; k]))) namespace)) namespace
    |LAMBLAM(s, v_l, t') ->
      let f = mk_fun () in
      cps_lambda t1 (META(x1, cps_lambda t2 (META(x2, T.LetBlo(f, T.Lam(s, v_l, t'), T.TailCall(T.VVar(x1), [T.VVar(x2) ; T.VVar(f)])))) namespace)) namespace
  end
  |S.Let(v, t1, t2) -> begin
    match t1 with
    |S.Lam(s', v', t') ->
      let x1 = Atom.fresh "LETB" in
      cps_lambda t1 (META(x1, cps_lambda t2 c namespace)) v
    |_ ->
      let x1 = Atom.fresh "LET" in
      cps_lambda t1 (META(x1, T.LetVal(v, T.VVar(x1), cps_lambda t2 c namespace))) namespace
  end
  |S.BinOp(t1, op, t2) -> begin
    match t1 with
    |S.Var(_) |S.Lit(_) -> begin
      match t2 with
      |S.Var(_) |S.Lit(_) -> apply c (LAMBVAL(T.VBinOp(to_tail_value t1, op, to_tail_value t2))) namespace
      |_ ->
        let lett2 = Atom.fresh "OP_R" in
        cps_lambda (S.Let(lett2, t2, S.BinOp(t1, op, S.Var(lett2)))) c namespace
    end
    |_ -> begin
      let lett1 = Atom.fresh "OP_L" in
      match t2 with
      |S.Var(_) |S.Lit(_) -> cps_lambda (S.Let(lett1, t1, S.BinOp(S.Var(lett1), op, t2))) c namespace
      |_ ->
        let lett2 = Atom.fresh "OP_R" in
        cps_lambda (S.Let(lett1, t1, S.Let(lett2, t2, S.BinOp(S.Var(lett1), op, S.Var(lett2))))) c namespace
    end
  end
  |S.Print(t') -> begin
    match t' with
    |S.Var(_) |S.Lit(_) -> T.Print(to_tail_value t', cps_lambda (S.App(S.Var(T.identity_fun), t')) c namespace)
    |_ ->
      let lett = Atom.fresh "PRINT" in
      cps_lambda (S.Let(lett, t', S.Print(S.Var(lett)))) c namespace
  end
  |S.IfZero(t1, t2, t3) -> begin
    match t1 with
    |S.Var(_) |S.Lit(_) -> T.IfZero(to_tail_value t1, cps_lambda t2 c namespace, cps_lambda t3 c namespace)
    |_ ->
      let lett = Atom.fresh "IFCLAUSE" in
      cps_lambda (S.Let(lett, t1, S.IfZero(S.Var(lett), t2, t3))) c namespace
  end
;;

let add_headers t =
  let x = Atom.fresh "x" in
  S.Let(T.identity_fun, S.Lam(S.NoSelf, x, S.Var(x)), t)
;;

let cps_term (t : S.term) : T.term =
  let x = Atom.fresh "x" in
  T.LetBlo(
    T.end_fun,
    T.Lam(T.NoSelf, [x], T.Exit),
    cps_lambda (add_headers t) (COBJ(T.end_fun)) (mk_fun ()))
;;
