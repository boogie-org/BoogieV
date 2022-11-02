include "../Passification.dfy"
include "../MakeScopedVarsUniqueProof.dfy" //for RelPred (TODO move to a better place)
include "../../util/Naming.dfy"
include "../../util/SemanticsUtil.dfy"
include "../../util/AstSubsetPredicates.dfy"


module SSAProof {
    import opened Passification
    import opened BoogieLang
    import opened BoogieCfg
    import opened BoogieSemantics
    import opened MakeScopedVarsUniqueProof
    import opened Naming
    import opened SemanticsUtil
    import opened AstSubsetPredicates
    import Sequences = Seq

    lemma SSACorrect<A>(
        a: absval_interp<A>,
        g: Cfg, 
        topo: seq<BlockId>, 
        predecessors: map<BlockId, seq<BlockId>>, 
        prevResult: SSAResult,
        cover: set<BlockId>) 
    requires 
      && g.successors.Keys <= g.blocks.Keys
      && predecessors.Keys <= g.blocks.Keys
      && (forall id | id in topo :: id in g.blocks.Keys)
         /** topo is a topological order w.r.t. predecessors */
      && (forall i | 0 <= i < |topo| :: topo[i] in predecessors.Keys ==> (set x | x in predecessors[topo[i]]) <= (set j | 0 <= j < i :: topo[j]))
         /** successors contained in blocks */
      && (forall blockId | blockId in g.successors.Keys ::
          (forall i :: 0 <= i < |g.successors[blockId]| ==> g.successors[blockId][i] in g.blocks.Keys))
          /** predecessors contained in blocks */
      && (forall blockId | blockId in predecessors.Keys ::
          (forall i | 0 <= i < |predecessors[blockId]| :: predecessors[blockId][i] in g.blocks.Keys))
      && (forall id | id in predecessors.Keys :: forall p | p in predecessors[id] :: p in g.blocks.Keys )
      && var g' := SSA(g, topo, predecessors); g'.successors.Keys <= g'.blocks.Keys
    ensures
      var g' := SSA(g, topo, predecessors);
      WpCfg(a, g, g.entry, TruePred(), cover) == WpCfg(a, g', g'.entry, TruePred(), cover)

  lemma SSAAuxCorrect<A>(
    a: absval_interp<A>, 
    cfg: Cfg, 
    idTopo: nat, 
    topo: seq<BlockId>, 
    pred: map<BlockId, seq<BlockId>>, 
    prevResult: SSAResult)
    requires 0 <= idTopo < |topo|
    requires forall i | 0 <= i < |topo| :: topo[i] in pred.Keys ==> (set x | x in pred[topo[i]]) <= (set j | 0 <= j < i :: topo[j])
    requires forall id | id in topo :: id in cfg.blocks.Keys
    requires forall id | id in pred.Keys :: forall p | p in pred[id] :: p in cfg.blocks.Keys 
    requires forall block | block in prevResult.incMaps.Keys :: prevResult.incMaps[block].Keys <= prevResult.globalIncMap.Keys
    requires prevResult.incMaps.Keys == set i | 0 <= i < idTopo :: topo[i]
    requires prevResult.blocks.Keys == set i | 0 <= i < idTopo :: topo[i]
    requires cfg.successors.Keys <= cfg.blocks.Keys 
    requires cfg.blocks.Keys == set i | i in topo
    ensures   
      var res := SSAAux(cfg, idTopo, topo, pred, prevResult);
      var curId := topo[idTopo];
      var preds := if curId in pred.Keys then pred[curId] else [];
      var predIncs := seq(|preds|, i requires 0 <= i < |preds| => if preds[i] in prevResult.incMaps.Keys then prevResult.incMaps[preds[i]] else map[]);
      var incRes := InputIncarnation(prevResult.globalIncMap, predIncs).localIncMap;
      forall i, cover | idTopo <= i < |topo| :: 
        IsAcyclic(cfg.successors, topo[idTopo], cover) ==>
          var cfg' := Cfg(cfg.entry, res.blocks, cfg.successors); //entry block irrelevant here
          var modVars := ModifiedVarsCfg(cfg.successors, res.blocks, topo[idTopo], cover);
          RelPred(incRes,
                  WpCfg(a, cfg, topo[idTopo], TruePred(), cover), 
                  ForallVarDecls(a, modVars, WpCfg(a, cfg', topo[idTopo], TruePred(), cover)),
                  map[])

  /*
  function ComputeCoverSetsSeq(r: SuccessorRel, ns: seq<BlockId>, cover: set<BlockId>) : (res: map<BlockId, set<BlockId>>)
    requires IsAcyclicSeq(r, ns, cover)
    decreases cover, 1, ns
    ensures (forall n2 | n2 in res.Keys :: IsAcyclic(r, n2, res[n2]))
  {
    if |ns| != 0 then
        ComputeCoverSets(r, ns[0], cover) + ComputeCoverSetsSeq(r, ns[1..], cover)
    else
        map[]
  }

  function ComputeCoverSets(r: SuccessorRel, n: BlockId, cover: set<BlockId>) : (res: map<BlockId, set<BlockId>>)
    requires IsAcyclic(r, n, cover)
    decreases cover, 0
    ensures (forall n2 | n2 in res.Keys :: IsAcyclic(r, n2, res[n2]))
  {
    if n in r.Keys then
        ComputeCoverSetsSeq(r, r[n], cover - {n})
    else 
        map[]
  }
  */

  function ModifiedVarsSeqCfg(r: SuccessorRel, blocks: map<BlockId, BasicBlock>, ns: seq<BlockId>, cover: set<BlockId>) : (res: seq<(var_name, Ty)>)
    requires IsAcyclicSeq(r, ns, cover)
    decreases cover, 1, ns

  function ModifiedVarsCfg(r: SuccessorRel, blocks: map<BlockId, BasicBlock>, n: BlockId, cover: set<BlockId>) : (res: seq<(var_name, Ty)>)
    requires IsAcyclic(r, n, cover) && r.Keys <= blocks.Keys
    decreases cover, 0
  {
    if n in r.Keys then
      ModifiedVars(SimpleCmd(blocks[n])) + ModifiedVarsSeqCfg(r, blocks, r[n], cover - {n})
    else
      []
  }
  
  lemma PassifyCfgSeqCorrect<A>(a: absval_interp<A>, g: Cfg, ns: seq<BlockId>, pred: map<BlockId, seq<BlockId>>, cover: set<BlockId>)
    requires IsAcyclicSeq(g.successors, ns, cover)
    ensures 
      var blocks' := map blockId | blockId in g.blocks.Keys :: PassifySimpleCmd(g.blocks[blockId]);
      var g' := Cfg(g.entry, blocks', g.successors);

      var modVars := set n | n in ns && n in ModifiedVarsCfg(g.successors, g.blocks, n, cover);
      WpCfgConjunction(a, g, ns, TruePred(), cover) == 
      ForallVarDecls(a, modVars, WpCfgConjunction(a, g', ns, TruePred(), cover))

  lemma PassifyCfgCorrect<A>(a: absval_interp<A>, g: Cfg, n: BlockId, pred: map<BlockId, seq<BlockId>>, cover: set<BlockId>)
    requires 
      /*
      && pred.Keys <= g.blocks.Keys
         /** successors contained in blocks */
      && (forall blockId | blockId in g.successors.Keys ::
          (forall i :: 0 <= i < |g.successors[blockId]| ==> g.successors[blockId][i] in g.blocks.Keys))
          /** predecessors contained in blocks */
      && (forall blockId | blockId in pred.Keys ::
          (forall i | 0 <= i < |pred[blockId]| :: pred[blockId][i] in g.blocks.Keys))
      && g.successors.Keys <= g.blocks.Keys
      */
      && IsAcyclic(g.successors, n, cover)
    ensures 
      var blocks' := map blockId | blockId in g.blocks.Keys :: PassifySimpleCmd(g.blocks[blockId]);
      var g' := Cfg(g.entry, blocks', g.successors);

      var modVars := ModifiedVarsCfg(g.successors, g.blocks, n, cover);
      WpCfg(a, g, n, TruePred(), cover) == 
      ForallVarDecls(a, modVars, WpCfg(a, g', n, TruePred(), cover))
    {

    }
 
}