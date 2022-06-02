
include "BoogieSemantics.dfy"

module BoogieCfg {

  import opened BoogieLang
  import opened BoogieSemantics
  import opened Wrappers

  type BasicBlock = seq<SimpleCmd>
  type BlockId = nat 

  datatype Cfg = Cfg(entry: BlockId, blocks: map<BlockId, BasicBlock>, successors: map<BlockId, seq<BlockId>>)

  function CfgWf(g: Cfg) : bool
  {
    g.blocks.Keys == g.successors.Keys &&
    g.entry in g.blocks.Keys &&
    (forall blockId :: blockId in g.successors.Keys ==> 
      (forall i :: 0 <= i < |g.successors[blockId]| ==> g.successors[blockId][i] in g.blocks.Keys))
  }

  function IsAcyclicSeq(g: Cfg, ns: seq<BlockId>, cover: set<BlockId>) : bool
    requires CfgWf(g)
    requires (forall i :: 0 <= i < |ns| ==> ns[i] in g.blocks.Keys)
    decreases cover, 1, ns
  {
    if |ns| == 0 then true
    else
      IsAcyclic(g, ns[0], cover) && IsAcyclicSeq(g, ns[1..], cover)
  }

  function IsAcyclic(g: Cfg, n: BlockId, cover: set<BlockId>) : bool
    requires CfgWf(g)
    requires n in g.blocks.Keys
    decreases cover, 0
  {
    (n in cover) && IsAcyclicSeq(g, g.successors[n], cover - {n})
  }

  function WpCfgConjunction<A(!new)>(a: absval_interp<A>, g: Cfg, ns: seq<BlockId>, post: Predicate<A>, cover: set<BlockId>) : Predicate<A>
    requires CfgWf(g)
    requires (forall i :: 0 <= i < |ns| ==> ns[i] in g.blocks.Keys)
    requires IsAcyclicSeq(g, ns, cover)
    decreases cover, 1, ns
  { s =>
      if |ns| == 0 then Some(true)
      else 
        assert ns[0] in g.blocks.Keys;
        var res1 :- WpCfg(a, g, ns[0], post, cover)(s);
        var res2 :- WpCfgConjunction(a, g, ns[1..], post, cover)(s);
        Some(res1 && res2)
  }

  function WpCfg<A(!new)>(a: absval_interp<A>, g: Cfg, n: BlockId, post: Predicate<A>, cover: set<BlockId>) : Predicate<A>
    requires CfgWf(g)
    requires n in g.blocks.Keys
    requires IsAcyclic(g, n, cover)
    decreases cover, 0
  {
    var successors := g.successors[n];

    if |successors| == 0 then 
      WpShallowSimpleCmdConj(a, g.blocks[n], post)
    else 
      WpShallowSimpleCmdConj(a, g.blocks[n], WpCfgConjunction(a, g, successors, post, cover - {n}))
  }

}