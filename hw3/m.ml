(**************************)
(*    syntax              *)
(**************************)
type inst = 
  | Push of int 
  | Add
  | Mul
  | Sub
  | True
  | False
  | Eq
  | Le
  | And
  | Neg
  | Fetch of var
  | Store of var 
  | Noop
  | Branch of cmd * cmd
  | Loop of cmd * cmd
  | Read
  | Print

and cmd = inst list
and var = string

(**************************)
(*    pretty printer      *)
(**************************)
let rec i2s inst =
  match inst with
  | Push n -> "push("^string_of_int n^")"
  | Add -> "add"
  | Mul -> "mul"
  | Sub -> "sub"
  | True -> "true"
  | False -> "false"
  | Eq -> "eq"
  | Le -> "le"
  | And -> "and"
  | Neg -> "neg"
  | Fetch x -> "fetch("^x^")"
  | Store x -> "store("^x^")"
  | Noop -> "noop"
  | Branch (c1,c2) -> "branch("^c2s c1^","^c2s c2^")"
  | Loop (c1,c2) -> "loop("^c2s c1^","^c2s c2^")"
  | Read -> "read"
  | Print -> "print"
and c2s cmd = List.fold_left (fun s i -> s ^ " " ^ i2s i) "" cmd
let pp cmd = print_endline (c2s cmd)

(**************************)
(*    semantics           *)
(**************************)
type value = Z of int | T of bool
type stack = value list
type state = (var, int) PMap.t

let state_empty = PMap.empty
let state_lookup x s = PMap.find x s
let state_bind x v s = PMap.add x v s

let rec next : inst list * stack * state -> inst list * stack * state
=fun (cc,ee,ss) -> 
  let total = (cc,ee,ss) in
    match total with
    | ([],e,s) -> ([],e,s)
    | (Push(i)::tl,e,s) -> next (tl,[Z(i)]@e,s) 
    | (Add::tl,Z(i)::Z(j)::e,s) -> next (tl,[Z(i+j)]@e,s)
    | (Mul::tl,Z(i)::Z(j)::e,s) -> next (tl,[Z(i*j)]@e,s)
    | (Sub::tl,Z(i)::Z(j)::e,s) -> next (tl,[Z(i-j)]@e,s)
    | (True::tl,e,s) -> next (tl,[T(true)]@e,s)
    | (False::tl,e,s) -> next (tl,[T(false)]@e,s)
    | (Eq::tl,Z(i)::Z(j)::e,s) -> next (tl,[T(i=j)]@e,s)
    | (Le::tl,Z(i)::Z(j)::e,s) -> next (tl,[T(i<=j)]@e,s)
    | (And::tl,T(i)::T(j)::e,s) -> if (i = true && j = true) then (next (tl,[T(true)]@e,s))
                                   else (next (tl,[T(false)]@e,s))
    | (Neg::tl,T(i)::e,s) -> if (i = false) then (next (tl,[T(true)]@e,s))
                             else (next (tl,[T(false)]@e,s))
    | (Fetch(x)::tl,e,s) -> next (tl,[Z(state_lookup x s)]@e,s)
    | (Store(x)::tl,Z(i)::e,s) -> next (tl,e,(state_bind x i s))
    | (Noop::tl,e,s) -> next (tl,e,s)
    | (Branch(c1,c2)::tl,T(i)::e,s) -> if (i = true) then (next (c1@tl,e,s))
                                       else (next (c2@tl,e,s))
    | (Loop(c1,c2)::tl,e,s) -> next (c1@[Branch(c2@[Loop(c1,c2)],[])]@tl,e,s)
    | (Read::tl,e,s)-> let i = read_int() in next (tl,Z(i)::e,s)
    | (Print::tl, Z(i)::e,s) -> let _ = (print_endline (string_of_int i)) in (tl,Z(i)::e,s)

(*type inst = 
  | Push of int 
  | Add
  | Mul
  | Sub
  | True
  | False
  | Eq
  | Le
  | And
  | Neg
  | Fetch of var
  | Store of var 
  | Noop
  | Branch of cmd * cmd
  | Loop of cmd * cmd
  | Read
  | Print
*)
let run : cmd -> state
=fun c -> 
  let iconf = (c, [], state_empty) in
  let rec iter (c,e,s) = 
    match next (c,e,s) with
    | [], _, s  -> s
    | c', e',s' -> iter (c',e',s') in
    iter iconf
