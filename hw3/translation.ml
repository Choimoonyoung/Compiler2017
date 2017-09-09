open While
open M

let rec transa: aexp-> inst list
=fun aex->
 match aex with
  | NUM(i) -> [Push(i)]
  | VAR(v) -> [Fetch(v)]
  | ADD(aexp1,aexp2) ->(transa aexp2)@(transa aexp1)@[Add]
  | SUB(aexp1,aexp2) ->(transa aexp2)@(transa aexp1)@[Sub]
  | MUL(aexp1,aexp2) ->(transa aexp2)@(transa aexp1)@[Mul]

let rec transb: bexp->inst list
=fun bex->
	match bex with
	| TRUE -> [True]
	| FALSE -> [False]
	| EQ(aexp1,aexp2) ->(transa aexp2)@(transa aexp1)@[Eq]
	| LE(aexp1,aexp2) ->(transa aexp2)@(transa aexp1)@[Le]
	| AND(bexp1,bexp2) ->(transb bexp2)@(transb bexp1)@[Add]
	| NEG(bexp1) ->(transb bexp1)@[Neg]

let rec trans : stmt -> inst list
=fun c ->
	match c with
		| ASSIGN(v,aex) -> (transa aex)@[Store(v)]
	    | SKIP -> []
	    | SEQ(stmt1,stmt2) -> (trans stmt1)@(trans stmt2)
	    | IF(bexp1,stmt1,stmt2) ->(transb bexp1)@[Branch((trans stmt1),(trans stmt2))]
	    | WHILE(bexp1,stmt1) -> [Loop((transb bexp1),(trans stmt1))]
	    | READ(x) -> [Read]@[Store(x)]
	    | PRINT(aexp1) -> (transa aexp1)@[Print]

(*type stmt = ASSIGN of var * aexp 
          | SKIP 
          | SEQ of stmt * stmt
          | IF of bexp * stmt * stmt 
          | WHILE of bexp * stmt
          | READ of var
          | PRINT of aexp *)

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