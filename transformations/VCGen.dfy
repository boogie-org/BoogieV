
include "../lang/Cfg.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"
include "../dafny-libraries/src/Collections/Maps/Maps.dfy"
include "../util/AstSubsetPredicates.dfy"
include "../util/CfgHelper.dfy"
include "../util/Util.dfy"

module VCGen
{

  import opened BoogieLang
  import opened BoogieCfg
  import opened AstSubsetPredicates
  import opened CfgHelper
  import Util

  function method VCBlockName(n: BlockId) : string
  {
    "B"+Util.NatToString(n)
  }

  function method ConjOfSuccessorVCs(bs: seq<BlockId>): Expr
    requires |bs| >= 1
  {
    var vcBlock := VCBlockName(bs[0]);
    if |bs| == 1 then
      Var(vcBlock)
    else
      var expr' := ConjOfSuccessorVCs(bs[1..]);
      BinOp(Var(vcBlock), And, expr')
  }

  function method WpSimpleCmdDeep(sc: SimpleCmd, post: Expr) : Expr
    requires IsPassive(sc)
  {
    match sc
    case Skip => post
    case Assert(e) => BinOp(e, And, post)
    case Assume(e) => BinOp(e, Imp, post)
    case SeqSimple(sc1, sc2) => WpSimpleCmdDeep(sc1, WpSimpleCmdDeep(sc2, post))
  }


  function method BlockToVC(g: Cfg,  blocks: seq<BlockId>) : map<BlockId, Expr>
    requires forall blockId | blockId in g.blocks.Keys :: IsPassive(g.blocks[blockId])
    requires forall blockId | blockId in blocks :: blockId in g.blocks.Keys
    ensures BlockToVC(g, blocks).Keys == (set block | block in blocks)
  {
    map blockId | blockId in blocks :: 
      var successorVC :=  
        if blockId in g.successors.Keys && |g.successors[blockId]| >= 1 then 
          ConjOfSuccessorVCs(g.successors[blockId])
        else
          Expr.TrueExpr;
      
      WpSimpleCmdDeep(g.blocks[blockId], successorVC)
  }

  function method GenerateVCAux(idTopo: nat, topo: seq<BlockId>, blockMapping: map<BlockId, Expr>, result: Expr) : Expr
    requires 0 <= idTopo <= |topo|
    requires forall b | b in topo :: b in blockMapping.Keys
  {
    if idTopo == |topo| then
      result
    else
      var blockId := topo[idTopo];
      var blockVCId := VCBlockName(blockId);
      var blockVC := blockMapping[blockId];
      Let(blockVCId, blockVC, result)
  }

  function method GenerateVC(g: Cfg, topo: seq<BlockId>) : Expr
    requires |topo| > 0
    requires forall blockId | blockId in g.blocks.Keys :: IsPassive(g.blocks[blockId])
    requires forall blockId | blockId in topo :: blockId in g.blocks.Keys
  {
    var blockToVC := BlockToVC(g, topo);

    //TODO: is topo[0] the entry block?
    GenerateVCAux(1, topo, blockToVC, blockToVC[topo[0]])
  }

}
