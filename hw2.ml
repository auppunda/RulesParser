type ('nonterminal, 'terminal) symbol =
  | N of 'nonterminal
  | T of 'terminal ;;

let rec getL g l f =
	match g with 
	| [] -> l
	| hd::tl -> match hd with
				 | (c, d) -> if c == f then getL tl (l@[d]) f else getL tl l f;;

let convert_grammar gram1 =
	match gram1 with
	| (a, b)-> (a, getL b []);;


let rec checkrule gram rule acc ls c  = 
	match rule with
	| [] -> (acc ls c)
	| hd :: tl-> checkInd gram hd rule ls c	acc	 
and checkInd g item rule l ce acc=
	match item with
	| (T a) -> if ce = [] then None else if a = (List.hd ce) then checkrule g (List.tl rule) acc l (List.tl ce) else None
	| (N a) -> checkHigh a g (List.tl rule) (g a) l (acc) ce
and checkHigh start gramm r srules le acc co = 
	match srules with
	| [] -> None 
	| hd :: tl -> match checkrule gramm (hd@r) acc (le@[start, hd]) co with
				 | None -> checkHigh start gramm r tl le acc co
				 | Some r -> Some r

let parse_prefix gram = 
	match gram with 
	| (a,b) -> (checkHigh a b [] (b a) [])

