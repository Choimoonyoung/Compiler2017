(**********************************)
(*        Syntax of WHILE          *)
(***********************************)
type stmt = ASSIGN of var * aexp 
          | SKIP 
          | SEQ of stmt * stmt
          | IF of bexp * stmt * stmt 
          | WHILE of bexp * stmt
          | READ of var
          | PRINT of aexp 
and aexp  = NUM of int
          | VAR of var
          | ADD of aexp * aexp
          | SUB of aexp * aexp
          | MUL of aexp * aexp
and bexp  = TRUE | FALSE
          | EQ of aexp * aexp 
          | LE of aexp * aexp 
          | AND of bexp * bexp
          | NEG of bexp
and var = string

type program = stmt

(***********************************)
(* pretty printer for the langauge *)
(***********************************)
let p x = print_string (x)

let rec p_aexp e = 
  match e with
  | NUM i -> print_int i
  | VAR x -> print_string x
  | ADD (e1,e2) -> p_aexp e1; p "+"; p_aexp e2
  | SUB (e1,e2) -> p_aexp e1; p "-"; p_aexp e2
  | MUL (e1,e2) -> p_aexp e1; p "*"; p_aexp e2

and p_bexp e = 
  match e with
  | TRUE -> p "true"
  | FALSE -> p "false"
  | EQ (e1,e2) -> p_aexp e1; p "=="; p_aexp e2
  | LE (e1,e2) -> p_aexp e1; p "<="; p_aexp e2
  | NEG e -> p "!"; p_bexp e
  | AND (b1,b2) -> p_bexp b1; p"&&"; p_bexp b2

and p_stmt : stmt -> unit
=fun stmt -> 
  match stmt with
  | ASSIGN (x, exp) -> print_string x; p " = "; p_aexp exp 
  | SKIP -> p "skip"
  | SEQ (c1,c2) -> p_stmt c1; print_string "; "; p_stmt c2; 
  | IF (bexp,stmt1,stmt2) -> p "if ("; p_bexp bexp; p ") {"; p_stmt stmt1; p "} else {"; p_stmt stmt2; p "}"
  | WHILE (b, s) -> p "while ("; p_bexp b; p ") { "; p_stmt  s; p " }"
  | READ x -> p "read "; p x; p ""
  | PRINT e -> p "print "; p_aexp e; p ""

let pp : program -> unit
=fun p -> p_stmt p; print_endline ""

(***************************************************)
(*        Operational Semantics for WHILE          *)
(***************************************************)
type state = (var, int) PMap.t
let state_empty = PMap.empty
let state_lookup x s = PMap.find x s
let state_bind x v s = PMap.add x v s


let rec eval_aexp: aexp -> state -> int
=fun aaexp state ->
  match aaexp with
  | NUM(i) -> i
  | VAR(v) -> state_lookup v state
  | ADD(aexp1,aexp2) -> (eval_aexp aexp1 state) + (eval_aexp aexp2 state)
  | SUB(aexp1,aexp2) -> (eval_aexp aexp1 state) - (eval_aexp aexp2 state)
  | MUL(aexp1,aexp2) -> (eval_aexp aexp1 state) * (eval_aexp aexp2 state)

let rec eval_bexp: bexp -> state -> bool
=fun bbexp state ->
  match bbexp with
  | TRUE -> true
  | FALSE -> false
  | EQ(aexp1,aexp2) -> (eval_aexp aexp1 state) = (eval_aexp aexp2 state)
  | LE(aexp1,aexp2) -> (eval_aexp aexp1 state) <= (eval_aexp aexp2 state)
  | AND(bexp1,bexp2) -> (eval_bexp bexp1 state) && (eval_bexp bexp2 state)
  | NEG(bexp1) -> (eval_bexp bexp1 state) = false

let rec eval_stmt : stmt -> state -> state
=fun c s ->
  match c with
  | ASSIGN (x, aaexp) -> (state_bind x (eval_aexp aaexp s) s)
  | SKIP -> s
  | SEQ (c1,c2) -> (eval_stmt c2 (eval_stmt c1 s))
  | IF (bbexp,stmt1,stmt2) -> if (eval_bexp bbexp s) then (eval_stmt stmt1 s)
                             else (eval_stmt stmt2 s)
  | WHILE (bbexp, c) -> if (eval_bexp bbexp s) then (eval_stmt (WHILE(bbexp,c)) (eval_stmt c s))
                       else s
  | READ x -> (state_bind x (read_int()) s)
  | PRINT(aaexp) -> let _ = (print_endline (string_of_int(eval_aexp aaexp s))) in s

(*type stmt = ASSIGN of var * aexp 
          | SKIP 
          | SEQ of stmt * stmt
          | IF of bexp * stmt * stmt 
          | WHILE of bexp * stmt
          | READ of var
          | PRINT of aexp *)

let run : stmt -> unit 
=fun pgm -> ignore (eval_stmt pgm state_empty)
