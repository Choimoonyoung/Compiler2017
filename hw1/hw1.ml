open Regex 

exception Not_implemented

let rec regex2nfa : Regex.t -> Nfa.t 
=fun regex -> 
   match regex with
   | Empty -> 
      let nfa = Nfa.create_new_nfa () in
      let (acc,nfa) = Nfa.create_state nfa in
      let nfa = Nfa.add_final_state nfa acc in
      nfa

   | Epsilon ->
      let nfa = Nfa.create_new_nfa () in
      let (acc,nfa) = Nfa.create_state nfa in
      let nfa = Nfa.add_final_state nfa acc in
      let sts = Nfa.get_initial_state nfa in
      let nfa = Nfa.add_epsilon_edge nfa (sts,acc) in
      nfa

   | Alpha(k) -> 
      let nfa = Nfa.create_new_nfa () in
      let (acc,nfa) = Nfa.create_state nfa in
      let nfa = Nfa.add_final_state nfa acc in
      let sts = Nfa.get_initial_state nfa in
      let nfa = Nfa.add_edge nfa (sts,k,acc) in
      nfa

   | OR(k,c) ->
      let n1 = regex2nfa k in
      let n2 = regex2nfa c in
      let n = Nfa.create_new_nfa () in
      let n1states = Nfa.get_states n1 in
      let n2states = Nfa.get_states n2 in
      let n1edges = Nfa.get_edges n1 in
      let n2edges = Nfa.get_edges n2 in
      let n = Nfa.add_states n n1states in
      let n = Nfa.add_states n n2states in (*state랑 edge 받아왓음*)
      let ins1 = Nfa.get_initial_state n1 in
      let ins2 = Nfa.get_initial_state n2 in
      let ins = Nfa.get_initial_state n in
      let n = Nfa.add_epsilon_edge n (ins,ins1) in
      let n = Nfa.add_epsilon_edge n (ins,ins2) in (*initial*)
      let acs1 = Nfa.get_final_states n1 in
      let acs2 = Nfa.get_final_states n2 in
      let (acs,n) = Nfa.create_state n in
      let n = Nfa.add_final_state n acs in 
      let n = Nfa.add_epsilon_edge n (BatSet.choose acs1,acs) in
      let n = Nfa.add_epsilon_edge n (BatSet.choose acs2,acs) in (*final*)
      let n = Nfa.add_edges n n1edges in
      let n = Nfa.add_edges n n2edges in
      n

   | CONCAT(k,c) ->
      let n1 = regex2nfa k in
      let n2 = regex2nfa c in
      let n = Nfa.create_new_nfa () in
      let n1states = Nfa.get_states n1 in
      let n2states = Nfa.get_states n2 in
      let n1edges = Nfa.get_edges n1 in
      let n2edges = Nfa.get_edges n2 in
      let ins1 = Nfa.get_initial_state n1 in
      let ins2 = Nfa.get_initial_state n2 in
      let acs1 = Nfa.get_final_states n1 in
      let acs2 = Nfa.get_final_states n2 in (*state edge받아왓음*)
      let n = Nfa.add_states n n1states in
      let n = Nfa.add_states n n2states in
      let n = Nfa.add_edges n n1edges in
      let n = Nfa.add_edges n n2edges in (*원래 edge 추가해줘음*)
      let n = Nfa.add_epsilon_edge n (BatSet.choose acs1,ins2) in
      let n = Nfa.add_epsilon_edge n (Nfa.get_initial_state n,ins1) in
      let n = Nfa.add_final_state n (BatSet.choose acs2) in
         n

   | STAR(k) ->
      let n1 = regex2nfa k in
      let n = Nfa.create_new_nfa () in
      let acs1 = Nfa.get_final_states n1 in
      let ins1 = Nfa.get_initial_state n1 in
      let ins = Nfa.get_initial_state n in
      let n1edges = Nfa.get_edges n1 in
      let n1states = Nfa.get_states n1 in
      let n = Nfa.add_states n n1states in
      let n = Nfa.add_edges n n1edges in
      let (acs,n) = Nfa.create_state n in
      let n = Nfa.add_final_state n acs in
      let n = Nfa.add_epsilon_edge n (ins,ins1) in
      let n = Nfa.add_epsilon_edge n (ins,acs) in
      let n = Nfa.add_epsilon_edge n (BatSet.choose acs1,ins1) in
      let n = Nfa.add_epsilon_edge n (BatSet.choose acs1,acs) in
      n

let rec epsilon_find : Nfa.state list -> Nfa.t -> Dfa.state
=fun t nfa->
   match t with
   |[]->BatSet.empty
   |hd::tl->BatSet.union (Nfa.get_next_state_epsilon nfa hd) (epsilon_find tl nfa) 

let rec epsilon_closure : Dfa.state-> Nfa.t ->Dfa.state-> Dfa.state
=fun t nfa t2->
   let t2 = t in
      let t = BatSet.union t (epsilon_find (BatSet.to_list t) nfa) in
         if (BatSet.equal t t2) 
            then t 
            else (epsilon_closure t nfa t2) 

let rec checklist : Dfa.state->Dfa.state list->bool
=fun stl d->
   match d with
   |[]-> false
   |hd::tl-> if (hd=stl) then true else (checklist stl tl)


let rec updatew : Dfa.state list->Dfa.state list->(Dfa.state* alphabet) list -> Dfa.state list
=fun w d nextstatelist->
   match nextstatelist with
   |[]->w
   |(dfastate,alpha)::tl->
      if (checklist dfastate d) then (updatew w d tl) else (updatew (dfastate::w) d tl)
   (*d내부에 nextstatelist와 똑같은 state가 있으면 넣지 않고 업ㅄ으면 넣는다.*)


let rec updated : Dfa.state list->(Dfa.state* alphabet) list ->Dfa.state list
=fun d nextstatelist->
   match nextstatelist with
   |[]->d
   |(stl,alpha)::tl->if (checklist stl d) then (updated d tl) else (updated (stl::d) tl)



let rec alphagetnextstate : Nfa.state list->Nfa.t ->alphabet->Dfa.state
=fun hdepcllist nfa alpha->
   match hdepcllist with
   |[]->BatSet.empty
   |hd::tl->
     let state = Nfa.get_next_state nfa hd alpha in
      BatSet.union (epsilon_closure state nfa BatSet.empty) (alphagetnextstate tl nfa alpha)

let rec getnextstate : Nfa.state list ->Nfa.t ->alphabet list-> (Dfa.state * alphabet) list
=fun hdepcllist nfa alphabet->
   match alphabet with
   |[]->[]
   |hd::tl ->
      let newelement = ((alphagetnextstate hdepcllist nfa hd) , hd) in
      newelement::(getnextstate hdepcllist nfa tl)

(*sort and remove duplicate inside the list*)

let addstate : Dfa.t -> Dfa.state ->Nfa.states-> Dfa.t
=fun prev dfastate nfafinal->
   if BatSet.equal (BatSet.intersect dfastate nfafinal) BatSet.empty 
      then (Dfa.add_state prev dfastate)
   else (Dfa.add_final_state (Dfa.add_state prev dfastate) dfastate)


let rec draw : Dfa.t-> Dfa.state-> (Dfa.state* alphabet) list ->Dfa.state list ->Nfa.states-> Dfa.t
=fun prev prevstate nextstatelist d nfafinal->
   match nextstatelist with
   |[]->prev
   |(dfastate,alpha)::tl->
      if checklist dfastate d 
         then (draw (Dfa.add_edge prev (prevstate,alpha,dfastate)) prevstate tl d nfafinal)
         else (draw (Dfa.add_edge (addstate prev dfastate nfafinal) (prevstate,alpha,dfastate)) prevstate tl d nfafinal) 
   

let rec nfa2dfa2: Nfa.t -> Dfa.t -> Dfa.state list -> Dfa.state list -> alphabet list-> Dfa.t
= fun nfa prev d w alphabet->
   match w with
   |[]-> prev
   |hd::tl -> 
      (*let hdepclset = epsilon_closure hd nfa BatSet.empty in*)
         let nextstatelist = getnextstate (BatSet.to_list hd) nfa alphabet in
            let nfafinal = Nfa.get_final_states nfa in
               let newdfa = draw prev hd nextstatelist d nfafinal in
                  let w = updatew tl d nextstatelist in
                     let d = updated d nextstatelist in
                        nfa2dfa2 nfa newdfa d w alphabet


let nfa2dfa : Nfa.t -> Dfa.t
=fun nfa -> 
   let initialstate = Nfa.get_initial_state nfa in
      let dfainitialstate = (epsilon_closure (BatSet.singleton initialstate) nfa BatSet.empty) in
         let dfa = Dfa.create_new_dfa dfainitialstate in
         let dfa = if BatSet.equal (BatSet.intersect dfainitialstate (Nfa.get_final_states nfa)) BatSet.empty 
               then dfa
               else (Dfa.add_final_state dfa dfainitialstate) in
        nfa2dfa2 nfa dfa [dfainitialstate] [dfainitialstate] [A;B]


(* Do not modify this function *)
let regex2dfa : Regex.t -> Dfa.t
=fun regex -> 
  let nfa = regex2nfa regex in
  let dfa = nfa2dfa nfa in
    dfa

let rec run_dfa2 : Dfa.t-> Dfa.state->alphabet list->Dfa.state
=fun dfa stt alphabet ->
   match alphabet with
   |[]->stt
   |hd::tl->run_dfa2 dfa (Dfa.get_next_state dfa stt hd) tl


let run_dfa : Dfa.t -> alphabet list -> bool
=fun dfa str -> 
   Dfa.is_final_state dfa (run_dfa2 dfa (Dfa.get_initial_state dfa) str) 

