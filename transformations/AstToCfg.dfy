include "../lang/BoogieLang.dfy"
include "../lang/BoogieSemantics.dfy"
include "../dafny-libraries/src/Wrappers.dfy"
include "../dafny-libraries/src/Math.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"

import opened BoogieLang
import opened Wrappers
import opened BoogieSemantics
import Sequences = Seq

/** 
  Transforms the Ast `c` into a Cfg.
  `precedingBlock`: The current basic block that is being processed
  `currentScope`: Basic block id for current block
  `labelToBlock`: Basic block ids for all labels in scope
  `nextVersion`: basic block id that is not reserved (including all ids larger than this one)

  returns:
    a Cfg if more than one block was completely processed
    next free version
    Exit block still under construction (if there is such a block)
 */
function method AstToCfgAux(
  c: Cmd, 
  precedingBlock: (BlockId, BasicBlock), 
  currentScope: BlockId, 
  labelToBlock: map<lbl_name, BlockId>,
  nextVersion: BlockId) : (Option<Cfg>, BlockId, Option<(BlockId, BasicBlock)>)
  requires LabelsWellDefAux(c, labelToBlock.Keys)
  ensures (var res := AstToCfgAux(c, precedingBlock, currentScope, labelToBlock, nextVersion); 
           var nextVersion' := nextVersion;
               && (res.0 != None || res.2 != None))
{
  match c
  case SimpleCmd(simpleC) => (None, nextVersion, Some((precedingBlock.0, precedingBlock.1+[simpleC])))
  case Break(optLbl) =>
    var succ := if optLbl.Some? then labelToBlock[optLbl.value] else currentScope;
    var (blockId, block) := precedingBlock;
    var cfg := Cfg(blockId, map[blockId := block], map[blockId := [succ]]);

    (Some(cfg), nextVersion, None)
  case Seq(c1, c2) =>
    var (optCfg1, nextVersion1, optExit1) := AstToCfgAux(c1, precedingBlock, currentScope, labelToBlock, nextVersion);

    if optExit1.None? then
      //c2 will never be reached
      (optCfg1, nextVersion1, optExit1)
    else
      var (optCfg2, nextVersion2, optExit2) := AstToCfgAux(c2, optExit1.value, currentScope, labelToBlock, nextVersion1);

      if optCfg1.None? then
        //since the exit block for c1 becomes the preceding block for c2, we can take the result for c2
        (optCfg2, nextVersion2, optExit2)
      else if optCfg2.None? then
        (optCfg1, nextVersion2, optExit2)
      else
        //merge cfgs
        var cfg1 := optCfg1.value;
        var cfg2 := optCfg2.value;
        (Some(Cfg(cfg1.entry, cfg1.blocks + cfg2.blocks, cfg1.successors + cfg2.successors)), nextVersion2, optExit2)
  case If(optCond, c1, c2) => 
    var (c1StartId, c1StartBlock) := if optCond.Some? then (nextVersion, [Assume(optCond.value)]) else (nextVersion, []);
    var (c2StartId, c2StartBlock) := if optCond.Some? then (nextVersion+1, [Assume(UnOp(Not, optCond.value))]) else (nextVersion+1, []);

    var (optCfg1, nextVersion1, optExit1) := AstToCfgAux(c1, (c1StartId, c1StartBlock), currentScope, labelToBlock, nextVersion);

    var (optCfg2, nextVersion2, optExit2) := AstToCfgAux(c2, (c2StartId, c2StartBlock), currentScope, labelToBlock, nextVersion1);

    var (entryBlockId, entryBlock) := precedingBlock;

    /** 
      * precedingBlock is the entry block 
      * connect precedingBlock to c1StartId and c2StartId
      * if then/else branch have active exit blocks, then connect those to a fresh basic block, which will became the active basic block
    */

    var successors1 := if optCfg1.Some? then optCfg1.value.successors else map[];
    var successors2 := if optCfg2.Some? then successors1 + optCfg2.value.successors else successors1;
    var successors3 := successors2[entryBlockId := [c1StartId, c2StartId]];

    var blocks1 := if optCfg1.Some? then optCfg1.value.blocks else map[];
    var blocks2 := if optCfg2.Some? then blocks1 + optCfg2.value.blocks else blocks1;
    var blocks3 := blocks2[entryBlockId := entryBlock];

    if optExit1.Some? && optExit2.Some? then
      //connect the end of both branches to a new block
      var (joinId, joinBlock) := (nextVersion2, []);
      var (thenExitId, thenExitBlock) := optExit1.value;
      var (elseExitId, elseExitBlock) := optExit2.value;
      var successors4 := successors3[thenExitId := [joinId]][elseExitId := [joinId]];
      var cfg := Cfg(entryBlockId, blocks3, successors3[thenExitId := [joinId]][elseExitId := [joinId]]);
      (Some(cfg), nextVersion2+1, Some((joinId, joinBlock)))
    else 
      var cfg := Cfg(entryBlockId, blocks3, successors3);
      var optExitResult := if optExit1.Some? then optExit1 else optExit2;
      (Some(cfg), nextVersion2, optExitResult)
  case Scope(optLbl, xs, body) => 
    var (entryBlockId, entryBlock) := precedingBlock;
    var (lblId, lblBlock) := (nextVersion, []) ;

    var labelToBlockUpd := if optLbl.Some? then labelToBlock[optLbl.value := lblId] else labelToBlock;

    assert labelToBlockUpd.Keys == if optLbl.Some? then {optLbl.value} + labelToBlock.Keys else labelToBlock.Keys;
    var (optCfg, nextVersion', optExit) := AstToCfgAux(body, (entryBlockId, entryBlock), lblId, labelToBlockUpd, nextVersion+2);

    if optCfg.Some? then
      var cfg := optCfg.value;
      if optExit.Some? then
        var (exitId, exitBlock) := optExit.value;
        (Some(Cfg(cfg.entry, cfg.blocks[exitId := exitBlock], cfg.successors[exitId := [lblId]])), nextVersion', Some( (lblId, lblBlock) ))
      else
        (Some(cfg), nextVersion', Some((lblId, lblBlock)))
    else
      var (exitId, exitBlock) := optExit.value;

      (Some(Cfg(entryBlockId, map[lblId := lblBlock, exitId := exitBlock], map[exitId := [lblId]])), nextVersion', Some( (lblId, lblBlock) ))
  case _ => assume false; (None, nextVersion, None) //TODO
}

/*
function ValidCfgAcyclic(g: Cfg, n: BlockId, notVisited: set<BlockId>) : bool
  requires (n in notVisited)
  requires CfgWf(g)
{
  var successors := g.successors[n];
  forall i :: 0 <= i < |successors| ==> 
    ( successors[i] != n && 
      (successors[i] in notVisited ==> ValidCfgAcyclic(g, n, notVisited - {n}))
    )
}

function AcyclicCfg2(g: Cfg, s: set<BlockId>) : bool
{
  m.Keys == g.blocks.Keys && 
  m.Keys == g.successors.Keys &&
  (forall blockId :: blockId in g.blocks.Keys ==> Sequences.ToSet(g.successors[blockId]) <= m.Keys) &&
  (forall blockId :: blockId in g.blocks.Keys ==>
    (forall s :: s in Sequences.ToSet(g.successors[blockId]) ==> m[blockId] < m[s]))
}
*/
 
/** termination via topological ordering */

function MaxOfSet(s: set<nat>) : nat
  ensures (forall i :: i in s ==> MaxOfSet(s) >= i)
{
  if s == {} then 0
  else 
    var x :| x in s;
    var subRes := MaxOfSet(s - {x});
    assert (s - {x}) + {x} == s;
    Math.Max(subRes, x)
}

method ForwardTraverse(g: Cfg, n: BlockId, ghost m: map<BlockId, nat>) returns (r: Cfg)
  requires CfgWf(g)
  requires n in g.blocks.Keys
  requires AcyclicCfg(g, m)
  decreases MaxOfSet(m.Values) - m[n]
{
  assert m[n] in m.Values;
  var i := 0;
  while (i < |g.successors[n]|)
  { 
    var suc := g.successors[n][i];
    reveal Sequences.ToSet();
    r := ForwardTraverse(g, g.successors[n][i], m);
    i := i+1;
  }
}

function AcyclicCfg(g: Cfg, m: map<BlockId, nat>) : bool
{
  m.Keys == g.blocks.Keys && 
  m.Keys == g.successors.Keys &&
  (forall blockId :: blockId in g.blocks.Keys ==> Sequences.ToSet(g.successors[blockId]) <= m.Keys) &&
  (forall blockId :: blockId in g.blocks.Keys ==>
    (forall s :: s in Sequences.ToSet(g.successors[blockId]) ==> m[blockId] < m[s]))
}

