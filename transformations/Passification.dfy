include "../lang/Cfg.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"
include "../dafny-libraries/src/Collections/Maps/Maps.dfy"
include "../dafny-libraries/src/Math.dfy"
include "../util/Naming.dfy"
include "../util/AstSubsetPredicates.dfy"

module Passification
{

  import opened BoogieLang
  import opened BoogieCfg
  import Sequences = Seq
  import Math
  import opened Naming
  import Maps
  import opened AstSubsetPredicates

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
  requires input.Keys <= globalIncMap.Keys
  ensures
    var (globalIncMap', outputInc, b') := OutputIncarnation(globalIncMap, input, b);
    && outputInc.Keys <= globalIncMap'.Keys
    && globalIncMap.Keys <= globalIncMap'.Keys
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
  
  function method SynchronizationBlocks(
    predInc: Incarnation<var_name>,
    conflictInc: Incarnation<nat>,
    conflictSeq: seq<var_name>
  ) : SimpleCmd
    requires |conflictSeq| > 0
    requires conflictInc.Keys == (set x | x in conflictSeq) 
  {
    var assignmentsSeq := 
      seq(|conflictSeq|, i requires 0 <= i < |conflictSeq| => 
        var x := conflictSeq[i];
        var newX := VersionedName(x, conflictInc[x]);
        var oldX := if x in predInc.Keys then predInc[x] else x;
        Assign(newX, TPrim(TInt), Var(oldX)));
    
    SeqToSimpleCmd(assignmentsSeq)
  }
  
  function method AddSynchronizationBlocks(
    blocks: map<BlockId, BasicBlock>, 
    incs: map<BlockId, Incarnation<var_name>>,
    predIds: seq<BlockId>,
    conflictInc: Incarnation<nat>
  ) : map<BlockId, BasicBlock>
    requires forall p | p in predIds :: p in blocks.Keys 
    requires forall id | id in predIds :: id in incs.Keys
  {
    if |conflictInc.Keys| == 0 then
      blocks
    else
      var conflictVarsSeq := Util.SetToSequenceStr(conflictInc.Keys);

      var update := map predId | predId in predIds :: 
        SeqSimple(blocks[predId], SynchronizationBlocks(incs[predId], conflictInc, conflictVarsSeq));

      blocks+update
  }

  function method SSAAux(cfg: Cfg, idTopo: nat, topo: seq<BlockId>, pred: map<BlockId, seq<BlockId>>, prevResult: SSAResult) : SSAResult
    requires 0 <= idTopo <= |topo|
    requires forall i | 0 <= i < |topo| :: topo[i] in pred.Keys ==> (set x | x in pred[topo[i]]) <= (set j | 0 <= j < i :: topo[j])
    requires forall id | id in topo :: id in cfg.blocks.Keys
    requires forall id | id in pred.Keys :: forall p | p in pred[id] :: p in cfg.blocks.Keys 
    requires forall block | block in prevResult.incMaps.Keys :: prevResult.incMaps[block].Keys <= prevResult.globalIncMap.Keys
    requires prevResult.incMaps.Keys == set i | 0 <= i < idTopo :: topo[i]
    decreases |topo|-idTopo
  {
    if idTopo == |topo| then 
      prevResult
    else
      var curId := topo[idTopo];

      /** compute input incarnation by consolidating incarnation of predecessors */
      var preds := if curId in pred.Keys then pred[curId] else [];
      var predIncs := seq(|preds|, i requires 0 <= i < |preds| => if preds[i] in prevResult.incMaps.Keys then prevResult.incMaps[preds[i]] else map[]);
      var incRes := InputIncarnation(prevResult.globalIncMap, predIncs);

      /* for each conflict add synchronization assignments */
      var blocks' := if curId in pred.Keys then AddSynchronizationBlocks(cfg.blocks, prevResult.incMaps, preds, incRes.updatedInc) else cfg.blocks;
      
      /* compute output incarnation of block */
      var (globalIncMap'', outputIncarnation, b') := OutputIncarnation(incRes.globalIncMap, incRes.localIncMap, cfg.blocks[curId]);

      var ssaResult' := SSAResult_(prevResult.blocks[curId := b'], prevResult.incMaps[curId := outputIncarnation], globalIncMap'');
      assert ssaResult'.incMaps.Keys == prevResult.incMaps.Keys + {topo[idTopo]};
      assert (set i | 0 <= i < idTopo :: topo[i]) + {topo[idTopo]} == (set i | 0 <= i < idTopo+1 :: topo[i]);

      SSAAux(cfg, idTopo+1, topo, pred, ssaResult')
  }

  function method SSA(g: Cfg, topo: seq<BlockId>, pred: map<BlockId, seq<BlockId>>) : Cfg
    requires 
      && pred.Keys <= g.blocks.Keys
      && (forall id | id in topo :: id in g.blocks.Keys)
         /** topo is a topological order w.r.t. pred */
      && (forall i | 0 <= i < |topo| :: topo[i] in pred.Keys ==> (set x | x in pred[topo[i]]) <= (set j | 0 <= j < i :: topo[j]))
         /** successors contained in blocks */
      && (forall blockId | blockId in g.successors.Keys ::
          (forall i :: 0 <= i < |g.successors[blockId]| ==> g.successors[blockId][i] in g.blocks.Keys))
          /** predecessors contained in blocks */
      && (forall blockId | blockId in pred.Keys ::
          (forall i | 0 <= i < |pred[blockId]| :: pred[blockId][i] in g.blocks.Keys))

      && (forall id | id in pred.Keys :: forall p | p in pred[id] :: p in g.blocks.Keys )
    
  {
    var ssaResult := SSAAux(g, 0, topo, pred, SSAResult_(map[], map[], map[]));

    Cfg(g.entry, ssaResult.blocks, g.successors)
  }

  function method PassifySimpleCmd(sc: SimpleCmd) : SimpleCmd
  ensures IsPassive(PassifySimpleCmd(sc))
  {
    match sc
    case Skip => sc
    case Assert(e) => sc
    case Assume(e) => sc    
    case Assign(x, t, e) => Assume(BinOp(Var(x), Eq, e))
    case Havoc(varDecls) => Skip
    case SeqSimple(sc1, sc2) => SeqSimple(PassifySimpleCmd(sc1), PassifySimpleCmd(sc2))
  }

  function method PassifyCfg(g: Cfg, topo: seq<BlockId>, pred: map<BlockId, seq<BlockId>>) : Cfg
    requires 
      && pred.Keys <= g.blocks.Keys
      && (forall id | id in topo :: id in g.blocks.Keys)
         /** topo is a topological order w.r.t. pred */
      && (forall i | 0 <= i < |topo| :: topo[i] in pred.Keys ==> (set x | x in pred[topo[i]]) <= (set j | 0 <= j < i :: topo[j]))
         /** successors contained in blocks */
      && (forall blockId | blockId in g.successors.Keys ::
          (forall i :: 0 <= i < |g.successors[blockId]| ==> g.successors[blockId][i] in g.blocks.Keys))
          /** predecessors contained in blocks */
      && (forall blockId | blockId in pred.Keys ::
          (forall i | 0 <= i < |pred[blockId]| :: pred[blockId][i] in g.blocks.Keys))
    ensures 
      var g := PassifyCfg(g, topo, pred);
      forall blockId | blockId in g.blocks :: IsPassive(g.blocks[blockId])
  {
    var cfgSSA := SSA(g, topo, pred);
    var blocks' := map blockId | blockId in cfgSSA.blocks.Keys :: PassifySimpleCmd(cfgSSA.blocks[blockId]);

    Cfg(g.entry, blocks', g.successors) 
  }

}