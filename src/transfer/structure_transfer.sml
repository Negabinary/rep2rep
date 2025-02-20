import "transfer.search";
import "transfer.heuristic";
import "util.logging";

signature TRANSFER =
sig
  val applyCorrespondenceForGoal : State.T -> Correspondence.corr -> Relation.relationship -> State.T
  val applyCorrespondence : State.T -> Correspondence.corr -> State.T Seq.seq
  val singleStepTransfer : State.T -> State.T Seq.seq
  val structureTransfer : Knowledge.base
                            -> Type.typeSystem
                            -> Type.typeSystem
                            -> Construction.construction
                            -> bool
                            -> Relation.relationship
                            -> State.T Seq.seq
  val iterativeStructureTransfer : Knowledge.base
                                    -> Type.typeSystem
                                    -> Construction.construction
                                    -> bool
                                    -> Pattern.pattern option
                                    -> Relation.relationship
                                    -> State.T Seq.seq
  val targetedTransfer : Knowledge.base
                            -> Type.typeSystem
                            -> Type.typeSystem
                            -> Construction.construction
                            -> Pattern.pattern
                            -> Relation.relationship
                            -> State.T Seq.seq
  val masterTransfer : bool -> bool
                            -> Pattern.pattern option
                            -> Knowledge.base
                            -> Type.typeSystem
                            -> Type.typeSystem
                            -> Construction.construction
                            -> Relation.relationship
                            -> State.T Seq.seq

end;

structure Transfer : TRANSFER =
struct

  exception CorrespondenceNotApplicable
  (*  *)
  fun refreshNamesOfConstruction ct D =
    let
      fun firstUnusedName Ns =
        let fun f n =
              let val vcandidate = "v_{"^(Int.toString n)^"}"
              in if List.exists (fn x => x = vcandidate) Ns then f (n+1) else "v_{"^(Int.toString n)^"}"
              end
        in f 0
        end
      val tokensInConstruction = (Construction.fullTokenSequence ct)
      val tokensInComposition = Composition.tokensOfComposition D
      val names = map CSpace.nameOfToken (tokensInComposition @ tokensInConstruction)
      fun mkRenameFunction _ [] = (fn _ => NONE)
        | mkRenameFunction Ns (y::ys) =
            let
              fun f x = if CSpace.sameTokens x y then SOME (CSpace.makeToken (firstUnusedName Ns) (CSpace.typeOfToken x))
                        else mkRenameFunction (CSpace.nameOfToken (Option.valOf (f y)) :: Ns) ys x
            in f
            end
      fun renameFunction x = mkRenameFunction names tokensInConstruction x
      val updatedConstruction = Pattern.applyMorphism renameFunction ct
    in (renameFunction, updatedConstruction)
    end

  exception Undefined
  (* The following function takes a correspondence, corr, with construct relation Rc,
     and a goal assumed to have a superRelation Rg of Rc.
     The function will try to find a generator in the given source construction that matches
     the source pattern of corr. If found, it will use the isomorphic map (from pattern to generator)
     to rename the relationships between the vertices of the source specified by the correspondence.
     It will also rename the vertices of the target pattern so that they don't clash with the
     vertices in the composition.  *)
  fun instantiateCorrForStateAndGoal corr st goal targetType =
    let
      val (sourceToken,targetToken) = (case Relation.tupleOfRelationship goal of
                                          ([x],[y],_) => (x,y)
                                        | _ => raise CorrespondenceNotApplicable) (* assumes Rc is subrelation of Rg*)
      val (rfs,rc) = Correspondence.relationshipsOf corr
      val ct = State.constructionOf st
      val T = #sourceTypeSystem st
      val patternComp = State.patternCompOf st
      val (sourcePattern,targetPattern) = Correspondence.patternsOf corr
      val targetConstructWithUpdatedType =
            CSpace.makeToken (CSpace.nameOfToken (Pattern.constructOf targetPattern)) targetType
      fun partialMorphism x = if CSpace.sameTokens x (Pattern.constructOf targetPattern)
                              then SOME targetConstructWithUpdatedType
                              else NONE
      val targetPattern' = Pattern.applyPartialMorphism partialMorphism targetPattern
      val (targetRenamingFunction, updatedTargetPattern) =
            refreshNamesOfConstruction targetPattern' patternComp
      val (sourceRenamingFunction, matchingGenerator) =
            (case Pattern.findMapAndGeneratorMatchingForToken T ct sourcePattern sourceToken of
                ((f,SOME x) ) => (f, x)
              | _ => raise CorrespondenceNotApplicable)
      fun partialFunComp f g x = (case g x of NONE => f x | SOME y => f y)
      fun srFun x = (Option.valOf o sourceRenamingFunction) x
          handle Option => (Logging.write ("\nERROR: source renaming function\n"); raise Option)
      fun trFun x = (Option.valOf o (partialFunComp targetRenamingFunction partialMorphism)) x
          handle Option => (Logging.write ("\nERROR: target renaming function\n"); raise Option)
      fun updateR (sfs,tfs,R) = (map srFun sfs, map trFun tfs, R)
      (*****)
      fun funUnion (f::L) x =
        (case (f x, funUnion L x) of
            (NONE,SOME y) => SOME y
          | (SOME y,NONE) => SOME y
          | (NONE,NONE) => NONE
          | (SOME y, SOME z) => if CSpace.sameTokens y z then SOME y else raise Undefined)
        | funUnion [] _ = NONE
      val f = Pattern.funUnion [sourceRenamingFunction,targetRenamingFunction]
      (*****)
      val updatedFoundationRelationships = map updateR rfs
      val updatedConstructRelationship = updateR rc
      val updatedPullList = map (fn (R,R',tL) => (R,R',map (valOf o targetRenamingFunction) tL handle Option => (map (print o (fn x => CSpace.stringOfToken x ^ "\n")) tL;raise Option))) (#pullList corr)
    in (fn x => if CSpace.sameTokens x targetToken then SOME (Construction.constructOf updatedTargetPattern) else NONE,
        Correspondence.declareCorrespondence {name = #name corr,
                                              sourcePattern=matchingGenerator,
                                              targetPattern=updatedTargetPattern,
                                              tokenRels=updatedFoundationRelationships,
                                              constructRel=updatedConstructRelationship,
                                              pullList = updatedPullList})
    end

  fun applyPullItem [] _ _ = []
    | applyPullItem ((x,y,R)::gs) t (R',R'',tL) =
    if Relation.same R R'
    then map (fn t' => (x,map (fn s => if CSpace.sameTokens s t then t' else s) y,R'')) tL @
        applyPullItem gs t (R',R'',tL)
    else (x,y,R)::applyPullItem gs t (R',R'',tL)

  exception Error
  fun applyCorrespondenceForGoal st corr goal =
    let val (sourceToken,targetToken,Rg) = (case Relation.tupleOfRelationship goal of
                                              ([x],[y],R) => (x,y,R)
                                            | _ => raise CorrespondenceNotApplicable)
        val (stcs,ttcs,Rc) = (case Correspondence.relationshipsOf corr of
                                (_,([x],[y],R)) => (x,y,R)
                              | _ => (print "oh no!";raise Error))
        val sT = #sourceTypeSystem st
        val tT = #targetTypeSystem st
        val typeOfTargetTokenInGoal = CSpace.typeOfToken targetToken
        val typeOfTargetConstructInCorr = CSpace.typeOfToken ttcs
        fun minType typSys (ty1,ty2) =
              if (#subType typSys) (ty1,ty2) then ty1
              else if (#subType typSys) (ty2,ty1) then ty2
              else raise CorrespondenceNotApplicable
        val (f,instantiatedCorr) =
              if Knowledge.subRelation (State.knowledgeOf st) Rc Rg
                 andalso Pattern.tokenMatches sT sourceToken stcs
              then instantiateCorrForStateAndGoal corr st goal (minType tT (typeOfTargetTokenInGoal, typeOfTargetConstructInCorr))
              else raise CorrespondenceNotApplicable
        val (_,targetPattern) = Correspondence.patternsOf instantiatedCorr
      (*  val _ = print ((CSpace.nameOfToken targetToken) ^ CSpace.nameOfToken(Pattern.constructOf targetPattern) ^ "\n")*)
        val (rfs,rc) = Correspondence.relationshipsOf instantiatedCorr
        val patternComp = State.patternCompOf st
        val updatedPatternComp = if Composition.isPlaceholder patternComp
                                 then Composition.initFromConstruction targetPattern
                                 else Composition.attachConstructionAt patternComp targetPattern targetToken
        val transferProof = State.transferProofOf st
        val updatedTransferProof' = TransferProof.attachCorrAt instantiatedCorr goal transferProof
        val updatedTransferProof = TransferProof.attachCorrPulls instantiatedCorr targetToken updatedTransferProof'
        val gs' = State.goalsOf (State.replaceGoal st goal rfs)
        fun applyPullList [] = gs'
          | applyPullList (pi::pL) = applyPullItem (applyPullList pL) targetToken pi
        val updatedGoals = applyPullList (#pullList instantiatedCorr)
        (*
        val _ = if not (null (#pullList instantiatedCorr)) andalso List.allZip Relation.sameRelationship gs' updatedGoals
                then raise CorrespondenceNotApplicable else ()*)
        val stateWithUpdatedGoals = State.updateGoals st updatedGoals
        val stateWithUpdatedProof = State.updateTransferProof stateWithUpdatedGoals updatedTransferProof
    in State.applyPartialMorphismToCompAndGoals f (State.updatePatternComp stateWithUpdatedProof updatedPatternComp)
    end

  (* The function idempotencyOnGoals assumes that the relations being dumped are type-deterministic *)
  fun idempotencyOnGoals st =
    let fun isomorphic (x,y,R) (x',y',R') = List.allZip CSpace.sameTokens y y' andalso
                                            List.allZip CSpace.tokensHaveSameType x x' andalso
                                            Relation.same R R'
        fun rg (g::gs) =
            let val (keep,dump) = rg gs
            in if List.exists (isomorphic g) keep
               then (keep,g::dump)
               else (g::keep,dump)
            end
          | rg [] = ([],[])
        fun updateTransferProof (g::gs) = TransferProof.dump "idempotency" g (updateTransferProof gs)
          | updateTransferProof [] = State.transferProofOf st
        val (keep,dump) = rg (State.goalsOf st)
        val stateWithUpdatedGoals = State.updateGoals st keep
    in State.updateTransferProof stateWithUpdatedGoals (updateTransferProof dump)
    end

  fun applyCorrespondence st corr =
    let val newSt = idempotencyOnGoals st
        fun ac [] = Seq.empty
          | ac (g::gs) = (Seq.cons (applyCorrespondenceForGoal newSt corr g) (ac gs)
                            handle CorrespondenceNotApplicable => ac gs)
    in ac (State.goalsOf newSt)
    end

  fun singleStepTransfer st =
    let val corrs = #correspondences (State.knowledgeOf st)
    in Seq.maps (applyCorrespondence st) corrs
    end

  exception BadGoal

  fun structureTransferTac h ign forget state =
      (*Search.breadthFirstSortAndIgnore singleStepTransfer h ign forget state*)
      (*Search.breadthFirstSortIgnoreForget singleStepTransfer h ign forget state*)
      (*Search.depthFirstSortAndIgnore singleStepTransfer h ign forget state*)
      (*Search.depthFirstSortIgnoreForget singleStepTransfer h ign forget state*)
      (*Search.bestFirstSortAndIgnore singleStepTransfer h ign forget state*)
      Search.bestFirstSortIgnoreForget singleStepTransfer h ign forget state

(* every element of goals should be of the form ([vi1,...,vin],[vj1,...,vjm],R)*)
fun structureTransfer KB sourceT targetT ct unistructured goal =
  let
    val t = (case Relation.tupleOfRelationship goal of
                (_,[x],_) => x
              | _ => raise BadGoal)
    val initialState = State.make {sourceTypeSystem = sourceT,
                                    targetTypeSystem = targetT,
                                    transferProof = TransferProof.ofRelationship goal,
                                    construction = ct,
                                    originalGoal = goal,
                                    goals = [goal],
                                    composition = Composition.makePlaceholderComposition t,
                                    knowledge = KB}
    val ign = Heuristic.ignore 500 4999 100 unistructured
  in structureTransferTac Heuristic.transferProofMultStrengths ign Heuristic.forgetRelaxed initialState
  end

  fun v2t t =
    let val tok = CSpace.nameOfToken t
        val typ = CSpace.typeOfToken t
        fun vt (x::xs) = if x = #"v" then #"t"::xs else x::xs
          | vt [] = []
    in SOME (CSpace.makeToken (String.implode (vt (String.explode tok))) typ)
    end

  exception Nope

  fun constructionOfComp st =
    (case Composition.resultingConstructions (State.patternCompOf st) of
        [c] => c
      | _ => raise Nope)
  fun withinTarget targetTypeSystem targetPattern st =
    Pattern.hasUnifiableGenerator targetTypeSystem targetPattern (constructionOfComp st) handle Nope => false
  fun matchesTarget targetTypeSystem targetPattern st =
    Pattern.matches targetTypeSystem (constructionOfComp st) targetPattern handle Nope => false

  fun iterativeStructureTransfer KB typeSystem ct unistructured targetPatternOption goal =
    let
      val t = (case Relation.tupleOfRelationship goal of
                  (_,[x],_) => x
                | _ => raise BadGoal)
      val initialState = State.make {sourceTypeSystem = typeSystem,
                                      targetTypeSystem = typeSystem,
                                      transferProof = TransferProof.ofRelationship goal,
                                      construction = ct,
                                      originalGoal = goal,
                                      goals = [goal],
                                      composition = Composition.makePlaceholderComposition t,
                                      knowledge = KB}
      val (x,y,R) = Relation.tupleOfRelationship goal
      fun updateState (C as {composition,goals,...}) =
        let val newConstruction = (case Composition.resultingConstructions composition of
                                      [c] => Pattern.applyMorphism v2t c
                                    | _ => raise Nope)
            val newConstruct = Construction.constructOf newConstruction
            val newGoal = Relation.makeRelationship ([newConstruct],y,R)
            val _ = if length goals > 0 then raise Nope else ()
        in State.make {sourceTypeSystem = typeSystem,
                      targetTypeSystem = typeSystem,
                      transferProof = TransferProof.ofRelationship newGoal,
                      construction = newConstruction,
                      originalGoal = newGoal,
                      goals = [newGoal],
                      composition = Composition.makePlaceholderComposition newConstruct,
                      knowledge = KB} handle Nope => (print "nope!\n";C)
        end
      fun ign (st,L) = List.exists (fn x => Heuristic.similarGoalsAndComps (x, st)) L
      val ignST = Heuristic.ignore 15 1999 45 unistructured
      fun forget (st,L) = (case targetPatternOption of
                              SOME targetPattern => not (matchesTarget typeSystem targetPattern st)
                            | NONE => false)
      fun forgetST (st,L) = Heuristic.forgetStrict (st,L)
      fun orderResults s =
        case Seq.pull s of
          SOME (x,xq) => Seq.insertManyNoRepetition x (orderResults xq) Heuristic.transferProofMultStrengths Heuristic.similarGoalsAndComps
        | NONE => Seq.empty
      val ST = Seq.take 10 o (structureTransferTac Heuristic.transferProofMultStrengths ignST forgetST)
      val results = Seq.map (Search.bestFirstSortIgnoreForget (ST o updateState) Heuristic.transferProofMultStrengths ign forget) (ST initialState)
    in orderResults results
    end

  fun targetedTransferTac h ign forget targetPattern state =
    let val targetTypeSystem = State.targetTypeSystemOf state
        fun forget' (st,L) = forget (st,L) orelse not (matchesTarget targetTypeSystem targetPattern st)
        fun ign' (st,L) = ign (st,L) orelse not (withinTarget targetTypeSystem targetPattern st)
    in Search.bestFirstSortIgnoreForget singleStepTransfer h ign' forget' state
    end

  fun targetedTransfer KB sourceT targetT ct targetPattern goal =
    let
      val t = (case Relation.tupleOfRelationship goal of
                  (_,[x],_) => x
                | _ => raise BadGoal)
      val initialState = State.make {sourceTypeSystem = sourceT,
                                      targetTypeSystem = targetT,
                                      transferProof = TransferProof.ofRelationship goal,
                                      construction = ct,
                                      originalGoal = goal,
                                      goals = [goal],
                                      composition = Composition.makePlaceholderComposition t,
                                      knowledge = KB}
      val ign = Heuristic.ignoreRelaxed 15 4999
    in targetedTransferTac Heuristic.transferProofMultStrengths ign Heuristic.forgetStrict targetPattern initialState
    end

  fun masterTransfer iterative unistructured targetPattOption KB sourceT targetT ct goal =
      if iterative then iterativeStructureTransfer KB sourceT ct unistructured targetPattOption goal
      else (case targetPattOption of
              NONE => structureTransfer KB sourceT targetT ct unistructured goal
            | SOME targetPattern => targetedTransfer KB sourceT targetT ct targetPattern goal)

end;
