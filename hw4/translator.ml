(* TODO: Write a translator *)

let new_t = ref 0
let new_tv() = (new_t := !new_t + 1; "t"^(string_of_int !new_t))
let new_label = ref 0
let new_label() = new_label := !new_label + 1; !new_label

let rec trans_exp : S.exp -> (string * T.linstr list)
=fun exp->
   match exp with
   | S.NUM(n)-> let t = new_tv() in (t, [(0,T.COPYC(t,n))])
   | S.LV(lv) ->
      (match lv with
      | S.ID(id) -> let t = new_tv() in (t,[(0,T.COPY(t,id))])
      | S.ARR(id,e) ->
         let t = new_tv() in
         let (tt,linstr1) = (trans_exp e) in
         (t,linstr1@[(0,T.LOAD(t,(id,tt)))])
      )
   | S.ADD (e1,e2) -> 
      let (t,linstr1) = (trans_exp e1) in
      let (t2,linstr2) = (trans_exp e2) in
      let t3 = new_tv() in
      (t3, linstr1@linstr2@[(0,T.ASSIGNV(t3,T.ADD,t,t2))])
   | S.SUB(e1,e2) ->
      let (t,linstr1) = (trans_exp e1) in
      let (t2,linstr2) = (trans_exp e2) in
      let t3 = new_tv() in
      (t3, linstr1@linstr2@[(0,T.ASSIGNV(t3,T.SUB,t,t2))])
   | S.MUL(e1,e2) ->
      let (t,linstr1) = (trans_exp e1) in
      let (t2,linstr2) = (trans_exp e2) in
      let t3 = new_tv() in
      (t3, linstr1@linstr2@[(0,T.ASSIGNV(t3,T.MUL,t,t2))])
   | S.DIV(e1,e2) ->
      let (t,linstr1) = (trans_exp e1) in
      let (t2,linstr2) = (trans_exp e2) in
      let t3 = new_tv() in
      (t3, linstr1@linstr2@[(0,T.ASSIGNV(t3,T.DIV,t,t2))])
   | S.MINUS(e) ->
      let (t,linstr1) = (trans_exp e) in
      let t2 = new_tv() in
      (t2, linstr1@[(0,T.ASSIGNU(t2,T.MINUS,t))])
   | S.NOT(e) ->
      let (t,linstr1) = (trans_exp e) in
      let t2 = new_tv() in
      (t2,linstr1@[(0,T.ASSIGNU(t2,T.NOT,t))])
   | S.LT (e1,e2) ->
      let (t,linstr1) = (trans_exp e1) in
      let (t2,linstr2) = (trans_exp e2) in
      let t3 = new_tv() in
      (t3, linstr1@linstr2@[(0,T.ASSIGNV(t3,T.LT,t,t2))])
   | S.LE (e1,e2) ->
      let (t,linstr1) = (trans_exp e1) in
      let (t2,linstr2) = (trans_exp e2) in
      let t3 = new_tv() in
      (t3, linstr1@linstr2@[(0,T.ASSIGNV(t3,T.LE,t,t2))])
   | S.GT (e1,e2)->
      let (t,linstr1) = (trans_exp e1) in
      let (t2,linstr2) = (trans_exp e2) in
      let t3 = new_tv() in
      (t3, linstr1@linstr2@[(0,T.ASSIGNV(t3,T.GT,t,t2))])
   | S.GE (e1,e2) ->
      let (t,linstr1) = (trans_exp e1) in
      let (t2,linstr2) = (trans_exp e2) in
      let t3 = new_tv() in
      (t3, linstr1@linstr2@[(0,T.ASSIGNV(t3,T.GE,t,t2))])
   | S.EQ (e1,e2) ->
      let (t,linstr1) = (trans_exp e1) in
      let (t2,linstr2) = (trans_exp e2) in
      let t3 = new_tv() in
      (t3, linstr1@linstr2@[(0,T.ASSIGNV(t3,T.EQ,t,t2))]) 
   | S.AND (e1,e2)->
      let (t,linstr1) = (trans_exp e1) in
      let (t2,linstr2) = (trans_exp e2) in
      let t3 = new_tv() in
      (t3, linstr1@linstr2@[(0,T.ASSIGNV(t3,T.AND,t,t2))])  
   | S.OR (e1,e2)->
      let (t,linstr1) = (trans_exp e1) in
      let (t2,linstr2) = (trans_exp e2) in
      let t3 = new_tv() in
      (t3, linstr1@linstr2@[(0,T.ASSIGNV(t3,T.OR,t,t2))])   



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
and trans_stmt : S.stmt -> T.linstr list
=fun stmt->
   match stmt with
   | S.ASSIGN(lv,exp)-> 
      (match lv with
      |S.ID(str) ->
         let (tt,linstr1) = (trans_exp exp) in
         (linstr1@[(0,T.COPY(str,tt))])
      |S.ARR(id,e2) ->
         let (tt,linstr1) = (trans_exp e2) in
         let (ttt,linstr2) = (trans_exp exp) in
         (linstr1@linstr2@[(0,T.STORE((id,tt),ttt))])
      )
   | S.IF(e,s1,s2) ->
      let (tt,linstr1) = (trans_exp e) in
      let tcode = (trans_stmt s1) in
      let fcode = (trans_stmt s2) in
      let tlabel = new_label() in
      let flabel = new_label() in
      let outlabel = new_label() in
      linstr1@
      [(0,T.CJUMP(tt,tlabel));(0,T.UJUMP(flabel));(tlabel,T.SKIP)]@
      tcode@
      [(0,T.UJUMP(outlabel));(flabel,T.SKIP)]@
      fcode@
      [(0,T.UJUMP(outlabel));(outlabel,T.SKIP)]
   | S.WHILE(e,s) ->
      let (tt,linstr1) = (trans_exp e) in
      let tcode = (trans_stmt s) in
      let tlabel = new_label() in
      let outlabel = new_label() in
      [(tlabel,T.SKIP)]@
      linstr1@
      [(0,T.CJUMPF(tt,outlabel))]@
      tcode@
      [(0,T.UJUMP(tlabel))]@
      [(outlabel,T.SKIP)]
   | S.DOWHILE(s,e) ->
      let tcode = (trans_stmt s) in
      tcode@(trans_stmt (S.WHILE (e,s)))
   | S.READ(id) -> [(0,T.READ(id))]
   | S.PRINT(e) ->
      let (tt,linstr1) = (trans_exp e) in
      linstr1@[(0,T.WRITE(tt))]
   | S.BLOCK(bl) -> (translate_block bl)

and trans_stmts: S.stmts -> T.linstr list
=fun stmts->
   match stmts with
   |[]->[]
   |hd::tl -> (trans_stmt hd)@(trans_stmts tl)


and trans_decl : S.decl -> T.linstr
=fun decl ->
   match decl with
   |(S.TINT,id) ->
      (0,T.COPYC(id,0))
   |(S.TARR(n),id) ->
      (0,T.ALLOC(id,n))

and trans_decls : S.decls -> T.linstr list
= fun decls->
   match decls with
   |[] -> []
   |hd::tl -> (trans_decl hd)::(trans_decls tl)

and translate_block : S.program -> T.program
=fun s ->
match s with
   |(decls, stmts) -> (trans_decls decls)@(trans_stmts stmts)



let translate : S.program -> T.program
=fun s ->
match s with
   |(decls, stmts) -> (trans_decls decls)@(trans_stmts stmts)@[(0,T.HALT)]
   |_ -> raise (Failure "translator: Not implemented")
