include "../lang/Cfg.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"
include "../dafny-libraries/src/Math.dfy"
include "../util/Naming.dfy"

module SSA 
{

  import opened BoogieLang
  import opened BoogieCfg
  import Sequences = Seq
  import Math
  import opened Naming

  // we track the domain of the incarnation in a sequence to allow one to easily iterate over the map
  type Incarnation = inc:(map<var_name, nat>, seq<var_name>) | 
    var xs := (set x | x in inc.1); xs == inc.0.Keys && |inc.0.Keys| == |inc.1|
    witness (map[], [])

  datatype IncarnationResult = IncarnationResult_(localIncMap: map<var_name, nat>, globalIncMap: map<var_name, nat>, conflicts: set<var_name>, newVars: seq<var_name>) 

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

  function method InputIncarnation(incRes: IncarnationResult, predIncs: seq<Incarnation>) : IncarnationResult
    decreases predIncs
  {
    if |predIncs| == 0 then
      incRes
    else
      var inc := predIncs[0];
      var incRes' := InputIncarnationAux(incRes, inc.0, inc.1);
      InputIncarnation(incRes', predIncs[1..])
  }

  function method OutputIncarnation(globalIncMap: map<var_name, nat>, input: Incarnation, b: BasicBlock) : (map<var_name, nat>, Incarnation, BasicBlock)
  decreases b
  {
    match b
    case Skip => (globalIncMap, input, b)
    case Assert(e) => 
      var e' := e; //TODO substitution
      (globalIncMap, input, Assert(e'))
    case Assume(e) => 
      var e' := e; //TODO substitution
      (globalIncMap, input, Assume(e'))
    case Assign(x, t, e) => 
      var e' := e; //TODO substitution
      var counter := if x in globalIncMap.Keys then globalIncMap[x]+1 else 1;
      var x' := VersionedName(x, counter);

      //TODO proper output incarnation
      (globalIncMap[x := counter], input, Assign(x', t, e'))

    case Havoc(varDecls) => 
      var f := (a: (map<var_name, nat>, seq<VarDecl>), d: VarDecl) => 
                var (globalMap, vs) := a;
                var (x,t) := d;
                var counter := if x in globalMap.Keys then globalMap[x]+1 else 1;
                var x' := VersionedName(x, counter);
                (globalMap[x := counter], vs+[(x',t)]);

      var (globalIncMap', varDecls') := Sequences.FoldLeft(f, (globalIncMap, []), varDecls);
      
      //TODO proper output incarnation
      (globalIncMap', input, Havoc(varDecls'))
    case SeqSimple(sc1, sc2) => 
      var (globalIncMap1, inc1, b1) := OutputIncarnation(globalIncMap, input, sc1);
      OutputIncarnation(globalIncMap1, inc1, sc2)
  }

  datatype SSAResult = 
    SSAResult_(blocks: map<BlockId, BasicBlock>, incMaps: map<BlockId, Incarnation>, globalIncMap: map<var_name, nat>)

  function method SSAAux(cfg: Cfg, topo: seq<BlockId>, pred: map<BlockId, seq<BlockId>>, prevResult: SSAResult) : SSAResult
  {
    if |topo| == 0 then 
      prevResult
    else
      var curId := topo[0];

      /** compute input incarnation by consolidating incarnation of predecessors */
      var preds := if curId in pred.Keys then pred[curId] else [];
      var predIncs := seq(|preds|, i requires 0 <= i < |preds| => if preds[i] in prevResult.incMaps.Keys then prevResult.incMaps[preds[i]] else (map[], []));
      var (inputIncarnation, globalIncMap'):= 
        if |preds| == 0 then
          ((map[], []), prevResult.globalIncMap)
        else if |preds| == 1 then
          (predIncs[0], prevResult.globalIncMap)
        else
          var incRes := InputIncarnation(IncarnationResult_(predIncs[0].0, prevResult.globalIncMap, {}, predIncs[0].1), predIncs);
          ((incRes.localIncMap, incRes.newVars), incRes.globalIncMap);

      /* for each conflict add synchronization assignments */
      //TODO
      
      /* compute output incarnation of block */
      //TODO
      var (globalIncMap'', outputIncarnation, b') := OutputIncarnation(globalIncMap', inputIncarnation, cfg.blocks[curId]);

      /* recurse, TODO: modify ssaResult param */
      var ssaResult' := SSAResult_(prevResult.blocks[curId := b'], prevResult.incMaps[curId := outputIncarnation], globalIncMap'');
      SSAAux(cfg, topo[1..], pred, prevResult)
  }


  function method SSA(g: Cfg, topo: seq<BlockId>, pred: map<BlockId, seq<BlockId>>) : Cfg
    requires 
      && pred.Keys <= g.blocks.Keys
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

}