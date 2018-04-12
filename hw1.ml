
let rec equal x b =
	match b with 
	| [] -> false
	| hd::tl -> if x = hd then true else equal x tl

let rec insert a b = 
	match a with
		[] -> [b]
	| 	h :: t->h :: (insert t b)

(* 1 *)
let rec subset a b = 
	match a with
	| [] -> true
	| hd::tl -> if equal hd b then subset tl b else false;;

(* 2 *)
let equal_sets a b =
	subset a b && subset b a;; 


(* 3 *)
let set_union a b =
	let rec set a d =
		match a with 
		| [] -> d
		| hd::tl -> if equal hd d then set tl d else set tl (insert d hd)
	in
	set b (set a []);;

(* 4 *)
let set_intersection a b = 
	let rec intersec a b d =
		match a with 
		| [] -> d 
		| hd::tl -> if equal hd b && not (equal hd d) then intersec tl b (insert d hd) else intersec tl b d
	in
	intersec b a (intersec a b []);;

(* 5 *)
let set_diff a b =
	let rec diff a b d = 
		match a with
		| [] -> d
		| hd :: tl -> if not (equal hd b) && not (equal hd d) then diff tl b (insert d hd) else diff tl b d
	in
	diff a b [];;

(* 6 *)
let rec computed_fixed_point eq f x =
	let n = f x in
	if eq n x then x
	else computed_fixed_point eq f n;;

(* 7 *)
let rec computed_periodic_point eq f p x = 
	let rec fpg f p x = 
		match p with 
		| 0 -> x
		| p -> f (fpg f (p-1) x)
	in
	if p = 0 then x
	else if eq (fpg f p x) x then x
	else computed_periodic_point eq f p (f x);;


(* 8 *)
let while_away s p x =
	let rec generateList s p x f = 
		if p x then generateList s p (s x) (f @ [x])
		 else f
	in 
	generateList s p x [];;

(* 9 *)
let rec rle_decode lp =
	let rec am i s l =
		match i with
		| 0 -> l
		| i -> am (i-1) s (l @ [s])
	in
	match lp with 
	| [] -> [] 
	| hd :: tl -> (am (Pervasives.fst hd) (Pervasives.snd hd) []) @ rle_decode tl;;	

type ('nonterminal, 'terminal) symbol =
  | N of 'nonterminal
  | T of 'terminal

(* checks whether list is terminal solution*)
let rec check l =
	match l with
	| [] -> true
	| hd :: tl -> match hd with
				  | (N a) -> false
				  | (T a) -> check tl;;

let checkGrammer rule =
	let (a, b) = rule in check b;; 

let rec getNonTerminal li g= 
	match li with
	| [] -> g
	| hd :: tl -> match hd with
				  | (N a) -> getNonTerminal tl (g @ [(a)])
				  | (T a) -> getNonTerminal tl g;;
	
let rec getNonTerminalWithType li g= 
	match li with
	| [] -> g
	| hd :: tl -> match hd with
				  | (N a) -> getNonTerminalWithType tl (g @ [(N a)])
				  | (T a) -> getNonTerminalWithType tl g;;

let rec getRules g item li = 
	match g with 
	| [] -> li
	| hd :: tl -> if (Pervasives.fst hd) = item then getRules tl item (li @ [(Pervasives.snd hd)]) 
				  else getRules tl item li;;

let checkTerminality g item = 
	let rules = getRules g item [] in
 	let rec checkl rul = 
 		match rul with
 		| [] -> false 
 		| hd :: tl -> if check hd then true else checkl tl
 	in
 	checkl rules;;

let rec getNonTerminalFromRules rules g =
	match rules with 
	| [] -> g
	| hd :: tl -> getNonTerminalFromRules tl (g @ (getNonTerminal hd []));;

(*let rec ges g l used end = 
	match l with 
	| [] -> false
	| hd :: tl -> if hd = end then true 
				  else if equal hd used then ges tl 
				  else ges g (tl @ [(getNonTerminalFromRules (getRules g hd) [])]) (used @ hd);;

let rec ge g l start end = 
		match l with
		| [] -> false
		| hd :: tl -> if ges g (getNonTerminal hd [] [start]) then true else ge g tl end;;
*)

let rec cre s e l used g =
	match l with
	| [] -> false
	| hd :: tl -> if hd = e then true 
				  else (cre s e (set_diff tl (used @ [hd])) (used @ [hd]) g) || cre s e (set_diff (getNonTerminalFromRules (getRules g hd []) []) (used @ [hd])) (used @ [hd]) g

(*let find s e g = 
	if s = e then true
	else
	let rules = getNonTerminalFromRules (getRules g s []) [] in
	cre s e rules [s] g
*)

(*let rec checkRule rule g used =
	match check rule with
	| true -> true
	| false -> let t = getNonTerminal rule [] in
			   

let rec checkRe rules g = *)
	
let rec getAll g s = 
	match g with 
	| [] -> s
	| hd :: tl -> match hd with 
				 | (a , b) ->  getAll tl (s @ [b])
(* 
let rec filter_unreachable s g l rules =	 
	match g with
	| [] -> l 
	| hd :: tl -> if find s (Pervasives.fst hd) rules then filter_unreachable s tl (l @ [hd]) rules 
				  else filter_unreachable s tl l rules
*)

let rec containSubset u g = 
	equal_sets u (getAll g [])


let remove s = 
	set_union s s;;

let rec check_rule rule ge used = 
	let rec check_Na li = 
		match li with
		| [] -> true
		| hd :: tl -> if containSubset used ge 
						then false 
						else match hd with
						|(N a) -> check_rule_rec (getRules ge a []) ge used tl
	in
	if check rule then true else check_Na (remove (getNonTerminalWithType rule []))
and check_rule_rec rules g used l = 
	match rules with 
	| [] -> false
	| hd :: tl -> if equal hd used then check_rule_rec (remove tl) g used l 
					else let r = l @ (getNonTerminalWithType hd [])  in
					(check_rule r g (used @ [hd]) || check_rule_rec (remove tl) g used l)


let getAnswer s g = 
	let ans = g in
	let rec checkAllRules a g l=  
		match a with 
		| [] -> l
		| hd :: tl -> match hd with
					  | (a, b) -> if check_rule b g [] then checkAllRules tl g (l@ [hd]) else checkAllRules tl g l
	in
	checkAllRules ans g [] 


(* 10 *)
let filter_blind_alleys g =
	match g with 
	| (s,l) -> s, getAnswer s l




