open Error

(* The source calculus. *)
module S = RawLambda
(* The target calculus. *)
module T = Lambda

(* Environments map strings to atoms. *)
module Env =
  Map.Make(String)

(* [bind env x] creates a fresh atom [a] and extends the environment [env]
   with a mapping of [x] to [a]. *)
let bind env x =
  let a = Atom.fresh x in
  Env.add x a env, a

let rec cook_term env { S.place; S.value } =
  match value with
  | S.Var x ->
      begin try
        T.Var (Env.find x env)
      with Not_found ->
        error place "Unbound variable: %s" x
      end
  | S.Lam (x, t) ->
      let env, x = bind env x in
      T.Lam (T.NoSelf, x, cook_term env t)
  | S.App (t1, t2) ->
      T.App (cook_term env t1, cook_term env t2)
  | S.Lit i ->
      T.Lit i
  | S.BinOp (t1, op, t2) ->
      T.BinOp (cook_term env t1, op, cook_term env t2)
  | S.Print t ->
      T.Print (cook_term env t)
  | S.Let (S.NonRecursive, x, t1, t2) ->
      let t1 = cook_term env t1 in
      let env, x = bind env x in
      let t2 = cook_term env t2 in
      T.Let (x, t1, t2)
  | S.Let (S.Recursive, f, { S.value = S.Lam (x, t1); _ }, t2) ->
      let env, f = bind env f in
      let x, t1 =
        let env, x = bind env x in
        x, cook_term env t1
      in
      let t2 = cook_term env t2 in
      T.Let (f, T.Lam (T.Self f, x, t1), t2)
  | S.Let (S.Recursive, _, { S.place; _ }, _) ->
      error place "the right-hand side of 'let rec' must be a lambda-abstraction"
  | S.IfZero (t1, t2, t3) ->
      T.IfZero (cook_term env t1, cook_term env t2, cook_term env t3)
  | S.AndLet(f_l, t1_l, t2) ->
    let env, f_l = List.fold_right (fun f (env, out) -> let env, f = bind env f in env, f::out) f_l (env, []) in
    T.BeginMutual(List.fold_right2
                  (fun f t1 out ->
                    match t1 with
                    |{S.value = S.Lam (x, t1); _} ->
                      let x, t1 =
                        let env, x = bind env x in
                        x, cook_term env t1
                      in
                      T.Let(f, T.Lam(T.Self f, x, t1), out))
                  f_l
                  t1_l
                  (T.EndMutual(cook_term env t2)))

let cook_term t =
  cook_term Env.empty t
