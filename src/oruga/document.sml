import "oruga.parser";
import "latex.latex";
import "oruga.grammar";
import "postprocessing.postprocessing";

signature DOCUMENT =
sig
  type documentContent
  val joinDocumentContents : documentContent list -> documentContent
  val read : string -> documentContent
  val knowledgeOf : documentContent -> Knowledge.base
  val typeSystemsOf : documentContent -> Type.typeSystem list
  val conSpecsOf : documentContent -> CSpace.conSpec list
  val constructionsOf : documentContent -> {name : string, conSpec : string, construction : Construction.construction} FiniteSet.set
  val grammarsOf : documentContent -> Grammar.grammar list
  val transferRequestsOf : documentContent ->  (string list) list
  val findTypeSystemWithName : documentContent -> string -> Type.typeSystem
  val findConSpecWithName : documentContent -> string -> CSpace.conSpec
  val findConstructionWithName : documentContent -> string -> {name : string, conSpec : string, construction : Construction.construction}
  val findCorrespondenceWithName : documentContent -> string -> Correspondence.corr
  val findGrammarWithName : documentContent -> string -> Grammar.grammar

end;

structure Document : DOCUMENT =
struct

  val ParseError = Parser.ParseError;

  val importKW = "import"
  val typeSystemKW = "typeSystem"
  val conSpecKW = "conSpec"
  val correspondenceKW = "correspondence"
  val constructionKW = "construction"
  val transferKW = "transfer"
  val commentKW = "comment"
  val grammarKW = "grammar"
  val inputKW = "input"
  val bigKeywords = [importKW,typeSystemKW,conSpecKW,correspondenceKW,constructionKW,transferKW,commentKW, grammarKW, inputKW]

  val typesKW = "types"
  val subTypeKW = "order"
  val typeKeywords = [typesKW,subTypeKW]

  val targetKW = "target"
  val sourceKW = "source"
  val tokenRelsKW = "tokenRels"
  val constructRelKW = "constructRel"
  val pullListKW = "pull"
  val strengthKW = "strength"
  val corrKeywords = [targetKW,sourceKW,tokenRelsKW,constructRelKW,pullListKW,strengthKW]

  val sourceTypeSystemKW = "sourceTypeSystem"
  val targetTypeSystemKW = "targetTypeSystem"
  val sourceConstructionKW = "sourceConstruction"
  val goalKW = "goal"
  val outputKW = "output"
  val limitKW = "limit"
  val postprocessKW = "postprocess"
  val iterativeKW = "iterative"
  val unistructuredKW = "unistructured"
  val matchTargetKW = "matchTarget"
  val targetConSpecKW = "targetConSpec"
  val transferKeywords = [postprocessKW, targetTypeSystemKW,sourceConstructionKW,goalKW,outputKW,limitKW,iterativeKW,unistructuredKW,matchTargetKW,targetConSpecKW]


  fun breakOn s [] = ([],"",[])
  | breakOn s (w::ws) = if w = s then ([],s,ws) else (case breakOn s ws of (x,s',y) => (w::x,s',y))

  fun contentForKeywords _ [] = []
  | contentForKeywords ks (w::ws) =
    let fun getKeywordMatch (k::K) = if k = w then SOME k else getKeywordMatch K
          | getKeywordMatch [] = NONE
    in (case getKeywordMatch ks of
          SOME k => (case contentForKeywords ks ws of
                        (NONE,x) :: L => (SOME k,x) :: L
                      | L => (SOME k, []) :: L)
        | NONE => (case contentForKeywords ks ws of
                      (NONE,x) :: L => (NONE, w :: x) :: L
                    | L => (NONE,[w]) :: L))
    end

  type documentContent = {typeSystems : Type.typeSystem list,
                          conSpecs : CSpace.conSpec list,
                          knowledge : Knowledge.base,
                          constructions : {name : string, conSpec : string, construction : Construction.construction} list,
                          transferRequests : (string list) list,
                          strengths : string -> real option,
                          grammars : Grammar.grammar list}
  val emptyDocContent = {typeSystems = [],
                         conSpecs = [],
                         knowledge = Knowledge.empty,
                         constructions = [],
                         transferRequests = [],
                         strengths = (fn _ => NONE),
                         grammars = []}

  val typeSystemsOf = #typeSystems
  val conSpecsOf = #conSpecs
  val knowledgeOf = #knowledge
  val constructionsOf = #constructions
  val transferRequestsOf = #transferRequests
  val strengthsOf = #strengths
  val grammarsOf = #grammars

  fun findTypeSystemWithName DC n =
    valOf (List.find (fn x => #name x = n) (typeSystemsOf DC))
    handle Option => raise ParseError ("no type system with name " ^ n)

  fun findConSpecWithName DC n =
    valOf (List.find (fn x => #name x = n) (conSpecsOf DC))
    handle Option => raise ParseError ("no constructor specification with name " ^ n)

  fun findConstructionWithName DC n =
    valOf (FiniteSet.find (fn x => #name x = n) (constructionsOf DC))
    handle Option => raise ParseError ("no construction with name " ^ n)

  fun findCorrespondenceWithName DC n =
    valOf (Knowledge.findCorrespondenceWithName (knowledgeOf DC) n)
    handle Option => raise ParseError ("no correspondence with name " ^ n)
  
  fun findGrammarWithName DC n =
    valOf (List.find (fn x => #name x = n) (grammarsOf DC))
    handle Option => raise ParseError ("no grammar with name " ^ n)

  fun inequality s =
    (case String.breakOn "<" s of
        (x,"<",y) => (x,y)
      | (x,">",y) => (y,x)
      | _ => raise ParseError s)

  (* The function below not only parses a type from a string, but if in notation _:t it makes it a subtype of t (and of any supertype of t) *)
  fun parseTyp subType s =
    case String.breakOn ":" s of
        ("_",":",superTyp) => (fn x => x = Type.typeOfString superTyp orelse String.isSuffix (":"^superTyp) (Type.nameOfType x),
                               fn (x,y) => String.isSuffix (":"^superTyp) (Type.nameOfType x) andalso subType (Type.typeOfString superTyp,y))
      | _ => (fn x => x = Type.typeOfString s, fn _ => false)

  fun addTypeSystem (name, tss) dc =
  let val blocks = contentForKeywords typeKeywords tss
      fun getTyps _ [] = []
        | getTyps subType ((x,c)::L) =
            if x = SOME typesKW
            then map (parseTyp subType) (String.tokens (fn x => x = #",") (String.concat c))
            else getTyps subType L
      fun getOrder [] = []
        | getOrder ((x,c)::L) =
            if x = SOME subTypeKW
            then map inequality (String.tokens (fn x => x = #",") (String.concat c))
            else getOrder L
      val ordList = getOrder blocks
      fun getTypsInOrdList ((x,y)::L) = FiniteSet.insert (Type.typeOfString x) (FiniteSet.insert (Type.typeOfString y) (getTypsInOrdList L))
        | getTypsInOrdList [] = FiniteSet.empty
      val typsInOrdList = getTypsInOrdList ordList
      fun eq (x,y) (x',y') = Type.equal x x' andalso Type.equal y y'
      fun subType_raw x = List.exists (eq x) ordList
      val subType' = Type.fixFiniteSubTypeFunction typsInOrdList subType_raw

      fun processTys ((typs,subty)::L) = (case processTys L of (Ty,subtype) => (fn x => typs x orelse Ty x, fn (x,y) => subtype (x,y) orelse subty (x,y)))
        | processTys [] = (fn _ => false, subType')

      val TypsAndSubTypeList = getTyps subType' blocks
      val (Ty,subType) = processTys TypsAndSubTypeList

      val typSys = {name = name, Ty = Ty, subType = subType}
  in {typeSystems = typSys :: (#typeSystems dc),
      conSpecs = #conSpecs dc,
      knowledge = #knowledge dc,
      constructions = #constructions dc,
      transferRequests = #transferRequests dc,
      strengths = #strengths dc,
      grammars = #grammars dc}
  end

  fun parseConstructor s =
    case String.breakOn ":" s of
      (cname,":",csig) =>
          (case String.breakOn "->" csig of
            (inTyps,"->",outTyp) => CSpace.makeConstructor (cname, CSpace.makeCTyp (Parser.list Type.typeOfString inTyps, Type.typeOfString outTyp))
          | _ => raise ParseError ("bad signature for constructor: " ^ s)
          )
    | _ => raise ParseError ("badly specified constructor: " ^ s)


  fun addConSpec (r, tss) dc =
  let val (name,x,typeSystemN) = String.breakOn ":" r
      (*val _ = if x = ":" then () else raise ParseError "no type system specified for conSpec"*)
      val chars = List.concat (map String.explode tss)
      val crs = map parseConstructor (Parser.splitLevelWithSeparatorApply' (fn x => x) (fn x => x = #",") chars)
      val _ = Logging.write ("\nAdding constructors for constructor specification " ^ name ^ " of type system " ^ typeSystemN ^ "...\n")
      val _ = map ((fn x => Logging.write ("  " ^ x ^ "\n")) o CSpace.stringOfConstructor) crs
      val _ = Logging.write "...done\n"
      val cspec = {name = name, typeSystem = typeSystemN, constructors = FiniteSet.ofList crs}
  in {typeSystems = #typeSystems dc,
      conSpecs = cspec :: #conSpecs dc,
      knowledge = #knowledge dc,
      constructions = #constructions dc,
      transferRequests = #transferRequests dc,
      strengths = #strengths dc,
      grammars = #grammars dc}
  end

  fun findConstructorInConSpec s cspec =
    valOf (CSpace.findConstructorWithName s cspec)
      handle Option => raise ParseError ("no constructor " ^ s ^ " in " ^ (#name cspec))

  fun tcpair s cspec =
    case String.breakOn "<-" (String.stripSpaces s) of
          (ts,_,cfgs) => {token = Parser.token ts, constructor = findConstructorInConSpec cfgs cspec}

  fun parseConstruction s cspec =
    let
      fun c tacc s' =
        case String.breakOn "[" s' of
          (ts,"",_) =>
            let val tok = Parser.token ts
            in if List.exists (CSpace.sameTokens tok) tacc
               then Construction.Reference tok
               else Construction.Source tok
            end
        | (tcps,_,ss) =>
            let val tcp = tcpair tcps cspec
                val tok = #token tcp
                val (xs,ys) = Parser.breakOnClosingDelimiter (#"[",#"]") ss
                val _ = if ys = [] then ()
                        else raise ParseError ("invalid input sequence to constructor: " ^ ss)
            in Construction.TCPair (tcp, Parser.splitLevelApply ((c (tok::tacc)) o String.removeParentheses) xs)
            end
    in Construction.fixReferences (c [] (String.stripSpaces s))
    end;

  fun addCorrespondence (nn,cs) dc =
  let val (name,x,cspecNs) = String.breakOn ":" nn
      val _ = if x = ":" then () else raise ParseError ("construction " ^ nn ^ " needs source and target cspecs")
      val (sourceCSpecN,y,targetCSpecN) = String.breakOn "," (String.removeParentheses cspecNs)
      val _ = if y = "," then () else raise ParseError ("construction " ^ nn ^ " needs source and target cspecs")
      val sourceCSpec = findConSpecWithName dc sourceCSpecN
      val sourceTySys = findTypeSystemWithName dc (#typeSystem sourceCSpec)
      val targetCSpec = findConSpecWithName dc targetCSpecN
      val targetTySys = findTypeSystemWithName dc (#typeSystem targetCSpec)
      val _ = Logging.write ("\nAdding correspondence " ^ name ^ "...")
      fun getPattern k [] = (Logging.write ("  ERROR: " ^ k ^ " pattern not specified");
                              raise ParseError ("no " ^ k ^ " in correspondence " ^ String.concat cs))
        | getPattern k ((x,ps) :: L) =
            if x = SOME k
            then parseConstruction (String.concat ps) (if k = sourceKW then sourceCSpec else targetCSpec)
            else getPattern k L
      fun getTokenRels [] = (Logging.write ("  ERROR: token relation not specified");
                              raise ParseError ("no token rels in correspondence " ^ String.concat cs))
        | getTokenRels ((x,trss) :: L) =
            if x = SOME tokenRelsKW
            then Parser.relaxedList Parser.relationship (String.concat trss)
            else getTokenRels L
      fun getConstructRel [] = (Logging.write ("  ERROR: construct relation not specified");
                                raise ParseError ("no construct rel in correspondence " ^ String.concat cs))
        | getConstructRel ((x,crs) :: L) =
            if x = SOME constructRelKW
            then Parser.relationship (String.concat crs)
            else getConstructRel L
      fun parsePull s =
        (case String.breakOn " to " s of
          (Rs," to ",S) => (case String.breakOn " as " S of
                              (tks," as ",Rs') => (Parser.relation (String.stripSpaces Rs), Parser.relation (String.stripSpaces Rs'), Parser.list Parser.token (String.stripSpaces tks))
                            | _ => (Parser.relation (String.stripSpaces Rs), Parser.relation (String.stripSpaces Rs), Parser.list Parser.token (String.stripSpaces S)))
        | _ => raise ParseError ("badly specified pull list in correspondence " ^ s))
      fun getPullList [] = []
        | getPullList ((x,pl) :: L) =
            if x = SOME pullListKW
            then Parser.relaxedList parsePull (Parser.deTokenise " " pl)
            else getPullList L
      fun getStrength [] = (Logging.write ("  ERROR: strength not specified");
                            raise ParseError ("no strength in correspondence " ^ String.concat cs))
        | getStrength ((x,ss) :: L) =
            if x = SOME strengthKW
            then valOf (Real.fromString (String.concat ss)) handle Option => (Logging.write ("strength is not a real number in correspondence " ^ String.concat cs);raise Option)
            else getStrength L
      val blocks = contentForKeywords corrKeywords cs
      val sPatt = getPattern sourceKW blocks
      val tPatt = getPattern targetKW blocks
      val _ = if Construction.wellFormed sourceTySys sPatt
              then Logging.write "\n  source pattern is well formed"
              else Logging.write "\n  WARNING: source pattern is not well formed"
      val _ = if Construction.wellFormed targetTySys tPatt
              then Logging.write "\n  target pattern is well formed\n"
              else Logging.write "\n  WARNING: target pattern is not well formed\n"
      val corr = {name = name,
                  sourcePattern = sPatt,
                  targetPattern = tPatt,
                  tokenRels = getTokenRels blocks,
                  constructRel = getConstructRel blocks,
                  pullList = getPullList blocks}
      val strengthVal = getStrength blocks
      fun strengthsUpd c = if c = name then SOME strengthVal else (#strengths dc) c
      val _ = Logging.write ("done\n");
      fun ff (c,c') = Real.compare (valOf (strengthsUpd (Correspondence.nameOf c')), valOf (strengthsUpd (Correspondence.nameOf c)))
  in {typeSystems = #typeSystems dc,
      conSpecs = #conSpecs dc,
      knowledge = Knowledge.addCorrespondence (#knowledge dc) corr strengthVal ff,
      constructions = #constructions dc,
      transferRequests = #transferRequests dc,
      strengths = strengthsUpd,
      grammars = #grammars dc}
  end

  fun addConstruction (nn, cts) dc =
  let val (name,x,cspecN) = String.breakOn ":" nn
      val _ = if x = ":" then () else raise ParseError ("construction " ^ nn ^ " needs a cspec")
      val cspec = findConSpecWithName dc cspecN
      val ct = parseConstruction cts cspec
      val T = findTypeSystemWithName dc (#typeSystem cspec)

      val _ = print ("\nChecking well-formedness of construction " ^ name ^ "...");
      val startTime = Time.now();
      val _ = if Construction.wellFormed  T ct then Logging.write ("\n  "^ name ^ " is well formed\n")
                else print ("\n  WARNING: "^ name ^" is not well formed\n")
      val endTime = Time.now();
      val runtime = Time.toMilliseconds endTime - Time.toMilliseconds startTime;
      val _ = print ("  well-formedness check runtime: "^ LargeInt.toString runtime ^ " ms \n...done\n  ");

      val ctRecord = {name = name, conSpec = cspecN, construction = ct}
  in {typeSystems = #typeSystems dc,
      conSpecs = #conSpecs dc,
      knowledge = #knowledge dc,
      constructions = ctRecord :: (#constructions dc),
      transferRequests = #transferRequests dc,
      strengths = #strengths dc,
      grammars = #grammars dc}
  end

  fun addInput (nn, tokens) dc = 
  let val (conName, x, gmrName) = String.breakOn ":" nn;
      val gmr = findGrammarWithName dc gmrName;
      val str = String.implode (List.concat (map String.explode tokens));
      val constructions = Grammar.parse gmr "equality" tokens;
      val _ = if x = ":" then () else raise ParseError ("No parse found for " ^ conName)
      val _ = print ("\nFound " ^ Int.toString (List.length (constructions)) ^ " possible parses for " ^ conName);
      val _ = map (fn x => (print "\n"; PolyML.print (Construction.toString x))) constructions;
  in
    {typeSystems = #typeSystems dc,
      conSpecs = #conSpecs dc,
      knowledge = #knowledge dc,
      constructions = {name = conName, conSpec = #name (#conSpec gmr), construction = List.hd constructions} :: (#constructions dc),
      transferRequests = #transferRequests dc,
      strengths = #strengths dc,
      grammars = #grammars dc}
  end

  fun addGrammar (nn, tokens) dc = 
  let val (grammarName, x, cspecN) = String.breakOn ":" nn;
      val _ = if x = ":" then () else raise ParseError ("grammar " ^ nn ^ " needs a cspec");
      val cspec = findConSpecWithName dc cspecN;
      val chars = List.concat (map String.explode tokens);
      fun find_type (tstr:string) : Type.typ = Type.typeOfString tstr;
      fun parseReduction reductionString =
          let val (_, x, reductionString) = String.breakOn "[" reductionString;
              val _ = if x = "[" then () else raise ParseError ("grammar " ^ nn ^ " expected a [ somewhere");
              val (parseTokens, x, reductionString) = String.breakOn "]" reductionString;
              val _ = if x = "]" then () else raise ParseError ("grammar " ^ nn ^ " expected a ] somewhere");
              val (_, x, reductionString) = String.breakOn "->" reductionString;
              val _ = if x = "->" then () else raise ParseError ("grammar " ^ nn ^ " expected a -> somewhere");
              fun parseParseToken parseTokenString =
                  let val (name, x, nont) = String.breakOn ":" parseTokenString;
                  in
                    if x <> "" then Grammar.NonTerminal(name, nont) else Grammar.Terminal(parseTokenString)
                  end
              val from = Parser.splitLevelWithSeparatorApply' parseParseToken (fn x => x = #",") (String.explode parseTokens);
              val to =  
                case String.breakOn "[" reductionString of
                    (x, "", _) => (
                        case String.breakOn ":" x of
                            (tn, "", _) => Grammar.BaseRep(find_type tn)
                          | (tn, _, tt) => raise ParseError ("OOPS, I need to ask about this one") (*TODO: Ask about this one*)
                    )
                  | (constructorName, _, x) => (
                        case String.breakOn "]" x of
                            (_, "", _) => raise ParseError ("grammar " ^ nn ^ " expected a ] somewhere")
                          | (construtionTokens, _, _) => 
                              let val toConstructorOption = CSpace.findConstructorWithName constructorName cspec;
                                  val toConstructor = case toConstructorOption of SOME(x) => x | NONE => raise ParseError ("Unknown constructor " ^ constructorName);
                                  fun parseParsedToken parseTokenString =
                                      let val (name, x, nont) = String.breakOn ":" parseTokenString;
                                      in
                                        if x <> "" then Grammar.DNonTerminal(name, nont) else Grammar.DTerminal(parseTokenString)
                                      end
                                  val toTokens = Parser.splitLevelWithSeparatorApply' parseParsedToken (fn x => x = #",") (String.explode construtionTokens);
                              in
                                  Grammar.ConRep(toConstructor, toTokens)
                              end
                    );
          in
              {from=from, to=to}
          end
      fun parseReductionSet str = 
          let val (nonterminal, x, str) = String.breakOn ":" str;
              val _ = if x = ":" then () else raise ParseError ("grammar " ^ nn ^ " expected a : somewhere");
              val reductions = Parser.splitLevelWithSeparatorApply' parseReduction (fn x => x = #"|") (String.explode str);
          in 
              (nonterminal, reductions)
          end
      val reductions = Parser.splitLevelWithSeparatorApply' parseReductionSet (fn x => x = #",") chars;
      val newGrammar = {
        name = grammarName,
        conSpec = cspec,
        reductions = reductions
      };
  in {typeSystems = #typeSystems dc,
      conSpecs = #conSpecs dc,
      knowledge = #knowledge dc,
      constructions = #constructions dc,
      transferRequests = #transferRequests dc,
      strengths = #strengths dc,
      grammars = newGrammar :: (#grammars dc)}
  end
  
  fun addTransferRequests ws dc =
     {typeSystems = #typeSystems dc,
      conSpecs = #conSpecs dc,
      knowledge = #knowledge dc,
      constructions = #constructions dc,
      transferRequests = #transferRequests dc @ [ws],
      strengths = #strengths dc,
      grammars = #grammars dc}

  fun parseTransferRequests DC ws =
  let fun stringifyC ((x,c)::L) = "("^(valOf x)^","^ (String.stringOfList (fn x => x) c)^") : "^(stringifyC L)
        | stringifyC [] = ""
      val C = contentForKeywords transferKeywords ws

      fun getConstruction [] = raise ParseError "no construction to transfer"
        | getConstruction ((x,c)::L) =
            if x = SOME sourceConstructionKW
            then findConstructionWithName DC (String.concat c)
            else getConstruction L
      val constructionRecord = getConstruction C
      val construction = #construction constructionRecord
      val sourceConSpecN = #conSpec constructionRecord
      val sourceConSpec = findConSpecWithName DC sourceConSpecN
      val sourceTypeSystem = findTypeSystemWithName DC (#typeSystem sourceConSpec)

      fun getTargetConSpec [] = sourceConSpec
        | getTargetConSpec ((x,c)::L) =
            if x = SOME targetConSpecKW
            then findConSpecWithName DC (String.concat c)
            else getTargetConSpec L
      fun getTargetTySys [] = sourceTypeSystem
        | getTargetTySys ((x,c)::L) =
            if x = SOME targetTypeSystemKW
            then findTypeSystemWithName DC (String.concat c)
            else getTargetTySys L
      val targetTypeSystem = getTargetTySys C
      fun getPostprocessing [] = NONE
        | getPostprocessing ((x,[])::L) = raise ParseError "no limit for postprocessing"
        | getPostprocessing ((x,c::cs)::L) =
            if x = SOME postprocessKW
            then Int.fromString c
            else getPostprocessing L
      fun getGoal [] = raise ParseError "no goal for transfer"
        | getGoal ((x,c)::L) =
            if x = SOME goalKW
            then Parser.relationship (String.concat c)
            else getGoal L
      fun getOutput [] = raise ParseError "no output file name for transfer"
        | getOutput ((x,c)::L) =
            if x = SOME outputKW
            then "output/latex/"^(String.concat c)^".tex"
            else getOutput L
      fun getLimit [] = raise ParseError "no limit for transfer output file"
        | getLimit ((x,c)::L) =
            if x = SOME limitKW
            then valOf (Int.fromString (String.concat c)) handle Option => raise ParseError "limit needs an integer!"
            else getLimit L
      fun getMatchTarget [] = NONE
        | getMatchTarget ((x,c)::L) =
            if x = SOME matchTargetKW
            then (let val mtct = parseConstruction (String.concat c) (getTargetConSpec C)
                      (*val _ = if Construction.wellFormed targetTypeSystem mtct
                              then Logging.write "\n  pattern for matching is well formed"
                              else Logging.write "\n  WARNING: pattern for matching is not well formed"*)
                  in SOME mtct
                  end)
            else getMatchTarget L
      fun getIterative [] = false
        | getIterative ((x,_)::L) =
            if x = SOME iterativeKW
            then (case getMatchTarget C of NONE => true | _ => raise ParseError "iterative and matchTarget are incompatible")
            else getIterative L
      fun getUnistructured [] = false
        | getUnistructured ((x,_)::L) =
            if x = SOME unistructuredKW
            then true
            else getUnistructured L
      val goal = getGoal C
      val outputFilePath = getOutput C
      val limit = getLimit C
      val iterative = getIterative C
      val KB = knowledgeOf DC
      val unistructured = getUnistructured C
      val targetPattern = getMatchTarget C
      fun getCompsAndGoals [] = []
        | getCompsAndGoals (h::t) = (State.patternCompOf h, State.transferProofOf h, State.originalGoalOf h, State.goalsOf h) :: getCompsAndGoals t
      fun mkLatexGoals (goal,goals,tproof) =
        let val goalsS = if List.null goals then "NO\\ OPEN\\ GOALS!" else String.concatWith "\\\\ \n " (map Latex.relationship goals)
            val originalGoalS = Latex.relationship goal ^ "\\\\ \n"
            val IS = Heuristic.multiplicativeScore (strengthsOf DC) tproof
            val alignedGoals = "\n " ^ (Latex.environment "align*" "" ("\\mathbf{Original\\ goal}\\\\\n"
                                                                      ^ originalGoalS
                                                                      ^ "\\\\ \\mathbf{Open\\ goals}\\\\\n"
                                                                      ^ goalsS ^ "\\\\"
                                                                      ^ "\\\\ \\mathbf{transfer\\ score}\\\\\n"
                                                                      ^ Real.toString IS))
        in alignedGoals
        end
      fun mkLatexProof tproof =
        let val ct = TransferProof.toConstruction tproof;
        in Latex.construction (0.0,0.0) ct
        end
      fun mkLatexConstructions comp =
        let val constructions = Composition.resultingConstructions comp;
        in map (Latex.construction (0.0,0.0)) constructions
        end
      fun mkLatexConstructionsAndGoals (comp,tproof,goal,goals) =
        let val latexConstructions = mkLatexConstructions comp
            val _ = if Composition.wellFormedComposition targetTypeSystem comp
                    then ()
                    else print ("\nWARNING! some decomposition is not well formed!")
            val latexLeft = Latex.environment "minipage" "[t]{0.45\\linewidth}" (Latex.printWithHSpace 0.2 latexConstructions)
            val latexGoals = mkLatexGoals (goal,goals,tproof)
            val latexRight = Latex.environment "minipage" "[t]{0.35\\linewidth}" (latexGoals)
            val latexProof = ""(*mkLatexProof tproof*)
            val CSize = Composition.size comp
        in Latex.environment "center" "" (Latex.printWithHSpace 0.0 ([latexLeft,latexRight,Int.toString CSize, latexProof]))
        end
      val _ = print ("\nApplying structure transfer to "^ #name constructionRecord ^ "...");
      val startTime = Time.now();
      val results = Transfer.masterTransfer iterative unistructured targetPattern KB sourceTypeSystem targetTypeSystem construction goal;
      fun pp_output x = (print (GeometryProver.print_proof_answer x); PolyML.print "----------------------------------------------------------------"; ());
      val _ = case getPostprocessing C of
                NONE => ()
              | (SOME n) =>  
                  let val _ = PolyML.print "================================================================";
                      val full_transfers = Seq.filter (fn x => Postprocessing.is_fully_transfered x handle Postprocessing.UnresolvableGeometryTypes => false) results;
                      val (ideas, _) = Seq.chop limit full_transfers;
                      val _ = print (PolyML.makestring (List.length ideas) ^ " full transfers.\n")
                      val _ = List.map (Postprocessing.postprocess (limit, 0) pp_output) ideas;
                  in
                      ()
                  end
      val nres = length (Seq.list_of results);
      val (listOfResults,_) = Seq.chop limit results;
      val endTime = Time.now();
      val runtime = Time.toMilliseconds endTime - Time.toMilliseconds startTime;
      val _ = print ("done\n" ^ "  runtime: "^ LargeInt.toString runtime ^ " ms \n");
      val _ = print ("  number of results: " ^ Int.toString nres ^ "\n");
      val compsAndGoals = getCompsAndGoals listOfResults;
      val transferProofs = map State.transferProofOf listOfResults
      val tproofConstruction = map (TransferProof.toConstruction o #2) compsAndGoals
      fun readCorrStrengths c = (strengthsOf DC) (CSpace.nameOfConstructor c)
      val E = Propagation.mkMultiplicativeISEvaluator readCorrStrengths
      val is = (Propagation.evaluate E) (hd tproofConstruction) handle Empty => (SOME 0.0)
      val is' = SOME (Heuristic.multiplicativeScore (strengthsOf DC) (hd transferProofs)) handle Empty => (SOME 0.0)
    (*  val _ = print (Construction.toString  (hd tproofConstruction))*)
      val _ = print ("  transfer score: " ^ Real.toString (valOf is') ^ "\n")
      val _ = print "\nComposing patterns and creating tikz figures...";
      val latexCompsAndGoals = Latex.printSubSections 1 (map mkLatexConstructionsAndGoals compsAndGoals);
      val latexCT = Latex.construction (0.0,0.0) construction;
      val _ = print "done\n";
      val _ = print "\nGenerating LaTeX document...";
      val latexOriginalConsAndGoals = Latex.environment "center" "" (latexCT);
      val outputFile = TextIO.openOut outputFilePath
      val opening = (Latex.sectionTitle false "Original construction") ^ "\n"
      val resultText = (Latex.sectionTitle false "Structure transfer results") ^ "\n"
      val _ = Latex.outputDocument outputFile (opening ^ latexOriginalConsAndGoals ^ "\n\n " ^ resultText ^ latexCompsAndGoals);
      val _ = TextIO.closeOut outputFile;
      val _ = print ("done!\n" ^ "  output file: "^outputFilePath^"\n\n");
  in ()
  end

  fun joinDocumentContents ({typeSystems = ts, conSpecs = sp, knowledge = kb, constructions = cs, transferRequests = tr, strengths = st, grammars = gms} :: L) =
  (case joinDocumentContents L of {typeSystems = ts', conSpecs = sp', knowledge = kb', constructions = cs', transferRequests = tr', strengths = st', grammars = gms'} =>
      {typeSystems = ts @ ts',
       conSpecs = sp @ sp',
       knowledge = Knowledge.join kb kb',
       constructions = cs @ cs',
       transferRequests = tr @ tr',
       grammars = gms @ gms',
       strengths = (fn c => case st c of SOME f => SOME f | NONE => st' c)})
  | joinDocumentContents [] = emptyDocContent

  fun read filename =
  let val file = TextIO.openIn ("input/"^filename)
      val s = TextIO.inputAll file
      val _ = TextIO.closeIn file
      val words = String.tokens (fn x => x = #"\n" orelse x = #" ") s
      val blocks = contentForKeywords bigKeywords words

      val importFilenames = List.filter (fn (x,_) => x = SOME importKW) blocks
      val importedContents = map (read o String.concat o #2) importFilenames
      val importedContent = joinDocumentContents importedContents

      fun distribute [] = importedContent
        | distribute ((x,c)::L) =
          let val dc = distribute L
              val (n,eq,ws) = breakOn "=" c
              (*val _ = if eq = "=" then () else raise ParseError (String.concat n)*)
          in if x = SOME typeSystemKW then addTypeSystem (hd n,ws) dc else
             if x = SOME conSpecKW then addConSpec (hd n, ws) dc else
             if x = SOME correspondenceKW then addCorrespondence (hd n,ws) dc else
             if x = SOME constructionKW then addConstruction (hd n,String.concat ws) dc else
             if x = SOME transferKW then addTransferRequests c dc else
             if x = SOME commentKW then dc else
             if x = SOME grammarKW then addGrammar (hd n, ws) dc else
             if x = SOME inputKW then addInput (hd n, ws) dc else
             raise ParseError "error: this shouldn't have happened"
          end handle Bind => raise ParseError "expected name = content, found multiple words before ="

      val nonImported = List.filter (fn (x,_) => x <> SOME importKW) blocks
      val allContent = distribute (rev nonImported)
      val _ = map (parseTransferRequests allContent) (#transferRequests allContent)
  in allContent
  end


(* TODO: a parser for propagator functions! figure out if you can export ML code from string! *)
end
