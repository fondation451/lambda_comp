(* The source calculus. *)
module S = Lambda
(* The target calculus. *)
module T = Tail

type lambda_self = S.self;;

type lambda_var = S.variable;;

let var_eq = Atom.equal;;

type lambda_term = S.term;;

let rec substitution t1 x t2 =
  match t1 with
  |Var(v) -> if var_eq x v then t2 else t1
  |Lam(s, v, t) -> if var_eq x v then t1 else Lam(s, v, substitution t x t2)
  |App(t, t') -> App(substitution t x t2, substitution t' x t2)
  |Lit(i) -> t1
  |BinOp(t, op, t') -> BinOp(substitution t x t2, op, substitution t' x t2)
  |Print(t) -> Print(substitution t x t2)
  |Let(v, t, t') -> Let(v, substitution t x t2, if var_eq v x then t' else substitution t' x t2)
;;

type continuation =
  |COBJ of lambda_term
  |META of lambda_var * lambda_term
;;

let apply c v =
  match c with
  |COBJ(t) -> App(t, v)
  |META(x, t) -> substitution t x v
;;

let reify c =
  match c with
  |COBJ(t) -> t
  |META(x, t) -> Lam(NoSelf, x, t)
;;

let rec cps_lambda t c =
  match t with
  |Var(v) -> apply c t
  |Lam(s, v, t') ->
    let k = Atom.fresh "k" in
    apply c (Lam(s, v, Lam(NoSelf, k, cps_lambda t' (COBJ (Var(k))))))
  |App(t1, t2) ->
    let x1 = Atom.fresh "x1" in
    let x2 = Atom.fresh "x2" in
    cps_lambda t1 (META(x1, cps_lambda t2 (META(x2, App(App(Var(x1), Var(x2)), reify c)))))
  |Lit(i) -> t
  |BinOp(t1, op, t2) -> t
  |Print(t') -> t
  |Let(v, t1, t2) ->
    let x1 = Atom.fresh "x1" in
    cps_lambda t1 (META(x1, Let(v, Var(x1), cps_lambda t2 c)))
;;


let rec cps_term (t : S.term) : T.term =
  assert false
;;
