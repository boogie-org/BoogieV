include "Cfg.dfy"
include "dafny-libraries/src/Wrappers.dfy"
include "dafny-libraries/src/Math.dfy"
include "dafny-libraries/src/Collections/Sequences/Seq.dfy"

module AstToCfg {

  import opened BoogieLang
  import opened Wrappers
  import opened BoogieSemantics
  import Sequences = Seq
  import opened BoogieCfg
  import Math

  predicate NoBreaksScopesLoops(c: Cmd)
  {
    match c
    case SimpleCmd(_) => true
    case Break(optLbl) => false
    case Seq(c1, c2) => NoBreaksScopesLoops(c1) && NoBreaksScopesLoops(c2)
    case Loop(_,_) => false
    case Scope(_,_,_) => false
    case If(_, thn, els) => NoBreaksScopesLoops(thn) && NoBreaksScopesLoops(els)
  }

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
    nextVersion: BlockId) : (Option<Cfg>, BlockId, Option<(BlockId, BasicBlock)>) //Option for exit block needed once break statements are taken into account
    requires NoBreaksScopesLoops(c)
    ensures (var res := AstToCfgAux(c, precedingBlock, nextVersion); 
             res.2 != None && (if res.0 == None then nextVersion == res.1 else nextVersion <= res.1))
  {
    match c
    case SimpleCmd(simpleC) => (None, nextVersion, Some((precedingBlock.0, precedingBlock.1+[simpleC])))
    case Seq(c1, c2) =>
      var (optCfg1, nextVersion1, optExit1) := AstToCfgAux(c1, precedingBlock, nextVersion);

      if optExit1.None? then
        //c2 will never be reached
        (optCfg1, nextVersion1, optExit1)
      else
        var (optCfg2, nextVersion2, optExit2) := AstToCfgAux(c2, optExit1.value, nextVersion1);

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

      var (optCfg1, nextVersion1, optExit1) := AstToCfgAux(c1, (c1StartId, c1StartBlock), nextVersion);

      var (optCfg2, nextVersion2, optExit2) := AstToCfgAux(c2, (c2StartId, c2StartBlock), nextVersion1);

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
  }

  lemma AstToCfgAcyclic(
    c: Cmd, 
    precedingBlock: (BlockId, BasicBlock), 
    nextVersion: BlockId)
    requires NoBreaksScopesLoops(c)
    ensures  
      var res := AstToCfgAux(c, precedingBlock, nextVersion); 
      var nextVersion' := res.1;
      var (exitBlockId, exitBlock) := res.2.value;

      if res.0.Some? then  
        var cfg := res.0.value;
        //TODO: 
        /*
        cfg.entry in cfg.blocks.Keys &&
        cfg.blocks.Keys == cfg.successors.Keys &&
        */
        cfg.entry == precedingBlock.0 &&
        IsAcyclicAlt(cfg, cfg.entry, set x : nat | nextVersion <= x < nextVersion')
      else  
        precedingBlock.0 == exitBlockId 
        //TODO: && precedingBlock.1 <= exitBlock
  {
    match c {
      case SimpleCmd(_) => 
      case Seq(c1, c2) =>
        var (optCfg1, nextVersion1, optExit1) := AstToCfgAux(c1, precedingBlock, nextVersion);

        if optExit1.None? {
          //c2 will never be reached
          //this case cannot occur in the simplified setting
          assert false;
        } else {
          var (optCfg2, nextVersion2, optExit2) := AstToCfgAux(c2, optExit1.value, nextVersion1);
          AstToCfgAcyclic(c2, optExit1.value, nextVersion2);

          var (exitBlockId2, exitBlock2) := optExit2.value;

          if optCfg1.None? {
            //since the exit block for c1 becomes the preceding block for c2, we can take the result for c2
            //(optCfg2, nextVersion2, optExit2)
            if optCfg2.Some? {
              var cfg2 := optCfg2.value;
              
              IsAcyclicLargerCover(cfg2, cfg2.entry, set x : nat | nextVersion1 <= x < nextVersion2, set x : nat | nextVersion <= x < nextVersion2);
            }
          } else if optCfg2.None? {
            //(optCfg1, nextVersion2, optExit2)
          } else {

            /** precondition of merge lemma  
                requires cover1 !! cover2
                requires r1.Keys !! r2.Keys
                requires IsAcyclicAlt(r1, n1Entry, cover1)
                requires IsAcyclicAlt(r2, n2Entry, cover2)

                requires n1Entry in r1.Keys || n1Entry == n2Entry
                requires !(n2Entry in r1.Keys)
            */

            assume false;
            //merge cfgs
            var cfg1 := optCfg1.value;
            var cfg2 := optCfg2.value;

            assume false;
            //assert cfg1.successors.Keys !! cfg2.successors.Keys;
            //(Some(Cfg(cfg1.entry, cfg1.blocks + cfg2.blocks, cfg1.successors + cfg2.successors)), nextVersion2, optExit2)
          }
        }
      case _ => assume false;
    }
  }           

  /*
  lemma AstToCfgSimpleCorrect<A>(
    a: absval_interp<A>,
    c: Cmd, 
    precedingBlock: (BlockId, BasicBlock), 
    nextVersion: BlockId,
    post: Predicate<Cmd>,
    s: state<A>) 
    requires NoBreaksScopesLoops(c)
    ensures  var res := AstToCfgAux(c, precedingBlock, nextVersion); 
             if res.0.Some? then  
              var cfg := res.0.value;
              WpShallow(a, c, WpPostShallow(post, post, map[]))(s) == WpCfg(a, cfg, cfg.entry, post)(s)
             else 
              //res.1.Some?
              true
  */


}