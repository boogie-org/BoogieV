include "../lang/Cfg.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"
include "../dafny-libraries/src/Collections/Maps/Maps.dfy"
include "../dafny-libraries/src/Math.dfy"
include "../util/Naming.dfy"

module SSA 
{

  import opened BoogieLang
  import opened BoogieCfg
  import Sequences = Seq
  import Math
  import opened Naming
  import Maps

  type Incarnation<T> = map<var_name, T> 

  function method ComputeConflicts<T(==)>(inc1: Incarnation<T>, inc2: Incarnation<T>, existingConflicts: set<var_name>) : set<var_name>
    ensures forall x | x in ComputeConflicts(inc1, inc2, existingConflicts) :: x in inc1.Keys || x in inc2.Keys
  {
    var conflictSet1 := set x | x in inc1.Keys && x !in existingConflicts && Maps.Get(inc1, x) != Maps.Get(inc2, x);
    var conflictSet2 := set x | x in inc2.Keys && x !in inc1.Keys && x !in existingConflicts && Maps.Get(inc1, x) != Maps.Get(inc2, x);

    conflictSet1 + conflictSet2
  }

  /** 
  Computes all conflicting variable mappings between incarnations. We only need to compare all incarnations with one of the incarnations I0.
  Since if two incarnations are in conflict, then at least one of them must also be in conflict with I0.
  */
  function method AllConflictsAux<T(==)>(predIncs: seq<Incarnation<T>>, baseInc: Incarnation<T>, existingConflicts: set<var_name>) : set<var_name>
    decreases predIncs
  {
    if |predIncs| == 0 then
     existingConflicts
    else
      var inc := predIncs[0];
      var conflicts := ComputeConflicts(baseInc, inc, existingConflicts);
      AllConflictsAux(predIncs[1..], baseInc, conflicts+existingConflicts)
  }
  
  function method AllConflicts<T(==)>(predIncs: seq<Incarnation<T>>) : set<var_name>
    decreases predIncs
  {
    if |predIncs| <= 1 then 
      {}
    else
      AllConflictsAux(predIncs[1..], predIncs[0], {})
  }

  lemma AllConflictsAuxSubset<T>(predIncs: seq<Incarnation<T>>, baseInc: Incarnation<T>, existingConflicts: set<var_name>, M: set<var_name>)
    requires forall i | 0 <= i < |predIncs| :: predIncs[i].Keys <= M
    requires baseInc.Keys <= M
    ensures AllConflictsAux(predIncs, baseInc, existingConflicts) <= M+existingConflicts
  { }

  lemma AllConflictsSubset<T>(predIncs: seq<Incarnation<T>>, M: set<var_name>)
    requires forall i | 0 <= i < |predIncs| :: predIncs[i].Keys <= M
    ensures AllConflicts(predIncs) <= M  
  { 
    if |predIncs| > 1 {
      AllConflictsAuxSubset(predIncs[1..], predIncs[0], {}, M);
    }
  }

  datatype IncarnationResult = IncarnationResult_(localIncMap: Incarnation<var_name>, globalIncMap: Incarnation<nat>, updatedInc: Incarnation<nat>) 

  function method InputIncarnation(globalIncMap: map<var_name, nat>, predIncs: seq<Incarnation<var_name>>) : IncarnationResult
    requires forall i | 0 <= i < |predIncs| :: predIncs[i].Keys <= globalIncMap.Keys
  {
    if |predIncs| == 0 then
      IncarnationResult_(map[], globalIncMap, map[])
    else if |predIncs| == 1 then
      IncarnationResult_(predIncs[0], globalIncMap, map[])
    else 
      var conflictVars := AllConflicts(predIncs);

      /* to get the new incarnation, we can take any incarnation and update all conflicts,
         since the variables with no conflicts are the same in all predecessors */
      AllConflictsSubset(predIncs, globalIncMap.Keys);
      var updatedInc := (map x | x in conflictVars :: globalIncMap[x]+1);
      var inputIncMap := predIncs[0] + (map x | x in updatedInc.Keys :: VersionedName(x, updatedInc[x]));
      var globalIncMap' := globalIncMap + updatedInc;
      IncarnationResult_(inputIncMap, globalIncMap', updatedInc)
  }

  function method OutputIncarnation(globalIncMap: Incarnation<nat>, input: Incarnation<var_name>, b: BasicBlock) : (map<var_name, nat>, Incarnation<var_name>, BasicBlock)
  decreases b
  {
    match b
    case Skip => (globalIncMap, input, b)
    case Assert(e) => 
      var e' := e.MultiSubstExpr(input); 
      (globalIncMap, input, Assert(e'))
    case Assume(e) => 
      var e' := e.MultiSubstExpr(input); 
      (globalIncMap, input, Assume(e'))
    case Assign(x, t, e) => 
      var e' := e.MultiSubstExpr(input); 
      var counter := if x in globalIncMap.Keys then globalIncMap[x]+1 else 1;
      var x' := VersionedName(x, counter);

      //TODO proper output incarnation
      (globalIncMap[x := counter], input[x := x'], Assign(x', t, e'))

    case Havoc(varDecls) => 
      var delta := map x | x in GetVarNames(varDecls) :: if x in globalIncMap.Keys then globalIncMap[x]+1 else 1;
      var globalIncMap' := globalIncMap + delta;
      var output := input + map x | x in delta.Keys :: VersionedName(x, delta[x]);

      assert forall i :: 0 <= i < |varDecls| ==> varDecls[i].0 in GetVarNames(varDecls);

      var varDecls' := Sequences.Map( (vd : VarDecl) requires vd.0 in delta.Keys => (VersionedName(vd.0, delta[vd.0]), vd.1), varDecls);
      
      (globalIncMap', output, Havoc(varDecls'))
    case SeqSimple(sc1, sc2) => 
      var (globalIncMap1, inc1, b1) := OutputIncarnation(globalIncMap, input, sc1);
      OutputIncarnation(globalIncMap1, inc1, sc2)
  }

  datatype SSAResult = 
    SSAResult_(blocks: map<BlockId, BasicBlock>, incMaps: map<BlockId, Incarnation<var_name>>, globalIncMap: Incarnation<nat>)

  function method SSAAux(cfg: Cfg, topo: seq<BlockId>, pred: map<BlockId, seq<BlockId>>, prevResult: SSAResult) : SSAResult
    requires forall id | id in topo :: id in cfg.blocks.Keys
  {
    if |topo| == 0 then 
      prevResult
    else
      var curId := topo[0];

      /** compute input incarnation by consolidating incarnation of predecessors */
      var preds := if curId in pred.Keys then pred[curId] else [];
      var predIncs := seq(|preds|, i requires 0 <= i < |preds| => if preds[i] in prevResult.incMaps.Keys then prevResult.incMaps[preds[i]] else map[]);
      var incRes := InputIncarnation(prevResult.globalIncMap, predIncs);

      /* for each conflict add synchronization assignments */
      /* Problem: Need order on blocks
      var blocks' := 
        prevResult.blocks + 
        map predId | predId in pred[curId] :: 
          SeqSimple(
            cfg.blocks[predId],
            SeqToSimpleCmd(
              seq(|incRes.updatedInc.Keys|, 
                i requires 0 <= i < |incRes.updatedInc.Keys| => 
                  Assign(
                    incRes.updatedInc[i], 
                    Var( prevResult.incMaps[predId]  ))   )
            )
          );
      */
      //TODO 
      var blocks' := prevResult.blocks;
      
      /* compute output incarnation of block */
      var (globalIncMap'', outputIncarnation, b') := OutputIncarnation(incRes.globalIncMap, incRes.localIncMap, cfg.blocks[curId]);

      /* recurse, TODO: modify ssaResult param */
      var ssaResult' := SSAResult_(prevResult.blocks[curId := b'], prevResult.incMaps[curId := outputIncarnation], globalIncMap'');
      SSAAux(cfg, topo[1..], pred, prevResult)
  }


  function method SSA(g: Cfg, topo: seq<BlockId>, pred: map<BlockId, seq<BlockId>>) : Cfg
    requires 
      && pred.Keys <= g.blocks.Keys
      && forall id | id in topo :: id in g.blocks.Keys
         /** successors contained in blocks */
      && (forall blockId | blockId in g.successors.Keys ::
          (forall i :: 0 <= i < |g.successors[blockId]| ==> g.successors[blockId][i] in g.blocks.Keys))
          /** predecessors contained in blocks */
      && (forall blockId | blockId in pred.Keys ::
          (forall i | 0 <= i < |pred[blockId]| :: pred[blockId][i] in g.blocks.Keys))
    
  {
    var ssaResult := SSAAux(g, topo, pred, SSAResult_(map[], map[], map[]));

    Cfg(g.entry, ssaResult.blocks, g.successors)
  }

  /*
  function method InputIncarnationAux(incRes: IncarnationResult, curInc: map<var_name, nat>, xs: seq<var_name>) : IncarnationResult
    requires (set x | x in xs) <= curInc.Keys
    requires incRes.conflicts <= incRes.localIncMap.Keys
    requires incRes.localIncMap.Keys <= incRes.globalIncMap.Keys
    decreases xs
  {
    if |xs| == 0 then
      incRes
    else 
      var x := xs[0];

      if x in incRes.conflicts then
        //handle conflicts elsewhere
        InputIncarnationAux(incRes, curInc, xs[1..])
      else
        if x in incRes.localIncMap.Keys then
          var xPrevInc := incRes.localIncMap[x];
          var xCurInc := curInc[x];

          if xPrevInc == xCurInc then
            //incarnations match, can keep the same incarnation
            InputIncarnationAux(incRes, curInc, xs[1..])
          else
            //incarnations do not match, need to record a conflict and create a new incarnation
            var xNewInc := incRes.globalIncMap[x]+1;
            var globalIncMap' := incRes.globalIncMap[x := xNewInc];
            var localIncMap' := incRes.localIncMap[x := xNewInc];
            var conflicts' := incRes.conflicts + {x};

            var incRes' := IncarnationResult_(localIncMap', globalIncMap', conflicts', incRes.newVars);

            InputIncarnationAux(incRes', curInc, xs[1..])
        else
          //variable was not recorded
          var xNewInc := curInc[x];
          var localIncMap' := incRes.localIncMap[x := xNewInc];
          var newVars' := incRes.newVars + [x];
          var incRes' := IncarnationResult_(localIncMap', incRes.globalIncMap, incRes.conflicts, newVars');
          InputIncarnationAux(incRes', curInc, xs[1..])
  }
  */

}