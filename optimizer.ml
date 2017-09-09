(* TODO: Implement an optimizer *)

type env = (T.var,int) PMap.t

let rec eliminate_skip : T.program -> T.program
=fun tprog->
	match tprog with
	| [] -> []
	| hd::next::tl -> 
		(match hd with
		|(label,T.SKIP) -> let (zlabel,zcode) = next in 
							(label,zcode)::(eliminate_skip tl)
		| _ -> hd::(eliminate_skip (next::tl))
		)
	| _ -> tprog


(*type program = linstr list
and linstr = label * instr (* labeled instruction *)
and instr = 
  | SKIP
  | ALLOC of var * int  (* x = alloc(n) *)
  | ASSIGNV of var * bop * var * var (* x = y bop z *)
  | ASSIGNC of var * bop * var * int (* x = y bop n *)
  | ASSIGNU of var * uop * var  (* x = uop y *)
  | COPY of var * var           (* x = y *)
  | COPYC of var * int          (* x = n *)
  | UJUMP of label              (* goto L *)
  | CJUMP of var * label        (* if x goto L *)
  | CJUMPF of var * label       (* ifFalse x goto L *)
  | LOAD of var * arr           (* x = a[i] *)
  | STORE of arr * var          (* a[i] = x *)
  | READ of var                 (* read x *)
  | WRITE of var                (* write x *)
  | HALT
and var = string
and label = int
and arr = var * var
and bop = ADD | SUB | MUL | DIV | LT | LE | GT | GE | EQ | AND | OR
and uop = MINUS | NOT
*)

(*array folding*)

let rec constant_first_folding : T.program -> env -> env
=fun tprog env ->
	match tprog with
	|[] -> env
	|hd::tl ->
		let (label,code) = hd in
		(match code with
			| T.COPYC(var,c) -> if ((String.get var 0) = 't') 
								then (constant_first_folding tl (PMap.add var c env))
								else (constant_first_folding tl env)
			| T.SKIP -> (constant_first_folding tl env)
			| T.ALLOC(var,c) -> (* x = alloc(n) *)
				(constant_first_folding tl env)
			| T.ASSIGNV(v1,bop,v2,v3) ->(* x = y bop z *)
				let bool1 = (PMap.mem v2 env) in
				let bool2 = (PMap.mem v3 env) in
				if(bool1 = true && bool2 = true && bop !=T.ADD &&bop !=T.SUB &&bop !=T.DIV && bop !=T.MUL)
					then (constant_first_folding tl (PMap.remove v2 (PMap.remove v3 env)))
				else if(bool1 = false && bool2 = true)
					then (constant_first_folding tl env)
				else if(bool2 = false && bool1 = true)
					then (constant_first_folding tl env)
				else (constant_first_folding tl env)
			| T.ASSIGNC(v1,bop,v2,c) ->(* x = y bop n *)
				let bool1 = (PMap.mem v2 env) in
				if(bool1 = true && bop !=T.ADD &&bop !=T.SUB &&bop !=T.DIV && bop !=T.MUL) 
					then (constant_first_folding tl (PMap.remove v2 env))
				else (constant_first_folding tl env)
			| T.ASSIGNU(v1,uop,v2) -> (* x = uop y *)
				let bool1 = (PMap.mem v2 env) in
				if(bool1 = true && uop != T.MINUS) 
					then (constant_first_folding tl (PMap.remove v2 env))
				else (constant_first_folding tl env)
			(*| COPY(v1,v2) ->          (* x = y *)
				let bool1 = (PMap.mem v2 env) in
				if(bool1 = true) 
					then (constant_first_folding tl (PMap.remove v2 env))
				else (constant_first_folding tl env)*)
			| T.CJUMP(v2,label) ->       (* if x goto L *)
				let bool1 = (PMap.mem v2 env) in
				if(bool1 = true) 
					then (constant_first_folding tl (PMap.remove v2 env))
				else (constant_first_folding tl env)
			| T.CJUMPF(v2,label) ->      (* ifFalse x goto L *)
				let bool1 = (PMap.mem v2 env) in
				if(bool1 = true) 
					then (constant_first_folding tl (PMap.remove v2 env))
				else (constant_first_folding tl env)
			| T.LOAD(v1,(v3,v2)) ->         (* x = a[i] *)
				let bool1 = (PMap.mem v2 env) in
				if(bool1 = true) 
					then (constant_first_folding tl (PMap.remove v2 env))
				else (constant_first_folding tl env)
			| T.STORE((v1,v2),v3) -> (* a[i] = x *)
				let bool1 = (PMap.mem v2 env) in
				let bool2 = (PMap.mem v3 env) in
				if(bool1 = true && bool2 = true)
					then (constant_first_folding tl (PMap.remove v2 (PMap.remove v3 env)))
				else if(bool1 = false && bool2 = true)
					then (constant_first_folding tl (PMap.remove v3 env))
				else if(bool2 = false && bool1 = true)
					then (constant_first_folding tl (PMap.remove v2 env))
				else (constant_first_folding tl env)
			| T.READ(v2) ->                (* read x *)
				let bool1 = (PMap.mem v2 env) in
				if(bool1 = true) 
					then (constant_first_folding tl (PMap.remove v2 env))
				else (constant_first_folding tl env)
			| T.WRITE(v2) ->             (* write x *)
				let bool1 = (PMap.mem v2 env) in
				if(bool1 = true) 
					then (constant_first_folding tl (PMap.remove v2 env))
				else (constant_first_folding tl env)
			| T.HALT -> (constant_first_folding tl env)
			| _ -> (constant_first_folding tl env)
		)


let rec constant_folding : T.program -> env -> T.program
=fun tprog env->
	match tprog with
	|[] -> []
	|hd::tl -> 
		let (label,code) = hd in
		(match code with
		| T.COPYC(var,c) -> 
			if ((PMap.mem var env) = true)
				then 
					(match tl with
					|[] -> []
					|(label2,code2)::tl2 -> (constant_folding ((label,code2)::tl2) env)
				)
			else (hd::(constant_folding tl env))
		| T.ASSIGNC(v1,bop,v2,c) ->(* x = y bop n *)
			let bool1 = (PMap.mem v2 env) in
			if(bool1 = true) 
				then
					(match bop with
						| T.ADD -> (label,T.COPYC(v1,((PMap.find v2 env)+c)))::(constant_folding tl env)
						| T.SUB -> (label,T.COPYC(v1,((PMap.find v2 env)-c)))::(constant_folding tl env)
						| T.MUL -> (label,T.COPYC(v1,((PMap.find v2 env)*c)))::(constant_folding tl env)
						| T.DIV -> (label,T.COPYC(v1,((PMap.find v2 env)/c)))::(constant_folding tl env)
						| _ -> hd::(constant_folding tl env)
					)
			else hd::(constant_folding tl env)
		| T.ASSIGNU(v1,uop,v2) -> (* x = uop y *)
			let bool1 = (PMap.mem v2 env) in
			if(bool1 = true && uop = T.MINUS) 
				then (label,T.COPYC(v1,-(PMap.find v2 env)))::(constant_folding tl env)
			else hd::(constant_folding tl env)	
		| T.ASSIGNV(v1,bop,v2,v3) ->
			let bool1 = (PMap.mem v2 env) in
			let bool2 = (PMap.mem v3 env) in
			if(bool1 = true && bool2 = true)
				then 
					(match bop with
						| T.ADD -> (label,T.COPYC(v1,((PMap.find v2 env)+(PMap.find v3 env))))::(constant_folding tl env)
						| T.SUB -> (label,T.COPYC(v1,((PMap.find v2 env)-(PMap.find v3 env))))::(constant_folding tl env)
						| T.MUL -> (label,T.COPYC(v1,((PMap.find v2 env)*(PMap.find v3 env))))::(constant_folding tl env)
						| T.DIV -> (label,T.COPYC(v1,((PMap.find v2 env)/(PMap.find v3 env))))::(constant_folding tl env)
						| _ -> hd::(constant_folding tl env)
					)
			else if(bool1 = false && bool2 = true)
				then (label,T.ASSIGNC(v1,bop,v2,(PMap.find v3 env)))::(constant_folding tl env)
			else if(bool2 = false && bool1 = true)
				then (label,T.ASSIGNC(v1,bop,v2,(PMap.find v2 env)))::(constant_folding tl env)
			else hd::(constant_folding tl env)
		| T.COPY(v1,v2) ->          (* x = y *)
			let bool1 = (PMap.mem v2 env) in
			if(bool1 = true)
				then (label,T.COPYC(v1,(PMap.find v2 env)))::(constant_folding tl env)
			else hd::(constant_folding tl env)
		| _ -> hd::(constant_folding tl env)
		)

let rec optimize_constant_folding : T.program -> T.program -> T.program
=fun prog prog2->
   if (prog = prog2) then prog
  else 
   let prog2 = prog in
   let prog = (constant_folding prog (constant_first_folding prog (PMap.empty))) in
  optimize_constant_folding prog prog2

let optimize : T.program -> T.program
=fun t -> 
	let prog = (eliminate_skip t) in
	(optimize_constant_folding prog [])

