include "../lang/Cfg.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"

module SSA 
{

  import opened BoogieLang
  import opened BoogieCfg
  import Sequences = Seq

  type Incarnation = map<var_name, nat>

  datatype SSAResult = 
    SSAResult_(blocks: map<BlockId, BasicBlock>, incMaps: map<BlockId, Incarnation>)

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
    var f := 
      (ssaResult: SSAResult, id: BlockId) => 
      (
        var preds := if id in pred.Keys then pred[id] else [];
        var predIncs := seq(|preds|, i requires 0 <= i < |preds| => if preds[i] in ssaResult.incMaps.Keys then ssaResult.incMaps[preds[i]] else map[]);
        var ssaResult' := ComputeIncarnation(ssaResult, preds, predIncs);
        ssaResult'
      );
    
    g
  }

  function method ComputeIncarnation(prevResult: SSAResult, preds: seq<BlockId>, predIncs: seq<Incarnation>) : SSAResult



}