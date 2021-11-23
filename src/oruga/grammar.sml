import "core.cspace";

signature GRAMMAR =
sig
    datatype parseToken = Terminal of string | NonTerminal of string * string;
    datatype parsedToken = DTerminal of string | DNonTerminal of string * string
    datatype representation = BaseRep of Type.typ | ConRep of CSpace.constructor * parsedToken list

    type reduction = {from : parseToken list, to : representation};
    type grammar  = {name : string, conSpec : CSpace.conSpec, reductions : (string * reduction list) list};
    
    val parse : grammar -> string -> string list -> Construction.construction list;
end;

structure Grammar : GRAMMAR =
struct
    datatype parseToken = Terminal of string | NonTerminal of string * string;
    datatype parsedToken = DTerminal of string | DNonTerminal of string * string
    datatype representation = BaseRep of Type.typ | ConRep of CSpace.constructor * parsedToken list

    type reduction = {from : parseToken list, to : representation};
    type grammar  = {name : string, conSpec : CSpace.conSpec, reductions : (string * reduction list) list};
    val counter = ref 0;
    fun unique_name () = (counter := !counter + 1; "t" ^ (PolyML.makestring (!counter)));
    val ParseError = Parser.ParseError;

    fun parse (gmr:grammar) (nonTerminal:string) (tokenized:string list) =
        let (*val tokenized = String.tokens (fn x => x = #"\n" orelse x = #" ") str;*)
            fun find_type (tstr:string) : Type.typ = Type.typeOfString tstr;
            fun parseTokens (nont:string) (tokens:string list) : (Construction.construction list) =
                let fun splitMatch (pattern : parseToken list) (target : string list): (string -> string list) list = (
                    case (pattern, target) of
                      ([],[]) => [fn x => raise ParseError (x ^ " is not in pattern.")]
                    | ([],_) => []
                    | (Terminal(s)::pp, x::tt) => if x = s then splitMatch pp tt else []
                    | (Terminal(s)::pp, []) => []
                    | (NonTerminal(id,nt)::pp, _) => 
                        let val splits = (map (fn (n,_) => List.split (target, n)) (List.enumerate (""::target)));
                        in 
                            (List.flatmap
                                (fn (fst, snd) => List.map (fn f => (fn x => if x = id then fst else f x)) (splitMatch pp snd))
                                splits)
                        end);
                    fun parseOneReduction (red:reduction) (tokens:string list) : Construction.construction list = 
                        case red of {from=from, to=to} =>
                        case to of 
                            BaseRep(t) => 
                                let val splits = splitMatch from tokens;
                                in
                                    if List.length splits = 0 then [] else [Construction.Source(CSpace.makeToken (unique_name ()) t)]
                                end
                          | ConRep(toConstructor, toTokens) =>
                                let val splits = splitMatch from tokens;
                                    val options : Construction.construction list list =  List.map 
                                        (fn 
                                            DTerminal(s) => if List.length splits = 0 then [] else
                                                [Construction.Source(CSpace.makeToken (unique_name ()) (find_type s))]
                                          | DNonTerminal(pn, pt) => List.flatmap (fn split => parseTokens pt (split pn)) splits
                                        ) 
                                        toTokens;
                                    fun prod (l : 'a list list) : 'a list list = 
                                        case l of [] => [[]] | x::xs => List.flatmap (fn y => List.map (fn z => y::z) (prod xs)) x;
                                in 
                                    List.map 
                                        (fn option => 
                                            Construction.TCPair ({
                                                token = CSpace.makeToken (unique_name ()) (#2(CSpace.csig toConstructor)), 
                                                constructor = toConstructor
                                            }, option)
                                        ) 
                                        (prod options) 
                                end
                    fun parseReductionGroups (rgs: reduction list list) (tokens:string list) : Construction.construction list =
                        case rgs of
                            [] => []
                          | rg::xrgs => 
                                case List.flatmap (fn r => parseOneReduction r tokens) rg of
                                    [] => parseReductionGroups xrgs tokens
                                  | x => x;
                in parseReductionGroups (map (#2) (List.filter (fn x => (#1)x = nont) (#reductions gmr))) tokens
                end
            (*fun renameOuter (construction : Construction.construction) (name:string) : Construction.construction =
                case construction of
                    TCPair ({token=token, constructor=constructor}, clist) => TCPair ({token=, constructor=constructor})*)
        in
            parseTokens nonTerminal tokenized
        end;
end;