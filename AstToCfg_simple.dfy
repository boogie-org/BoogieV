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
    case Seq(thn, els) => NoBreaksScopesLoops(thn) && NoBreaksScopesLoops(els)
    case Loop(_,_) => false
    case Scope(_,_,_) => false
    case If(_, thn, els) => NoBreaksScopesLoops(thn) && NoBreaksScopesLoops(els)
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
    requires precedingBlock.0 < nextVersion
    ensures  var res := AstToCfgAux(c, precedingBlock, nextVersion); 
             var exitBlockOpt := res.2;
             var nextVersion' := res.1;
             && (exitBlockOpt != None)
             && (if res.0 == None then 
                    && nextVersion == nextVersion' 
                    && precedingBlock.0 == exitBlockOpt.value.0 
                 else 
                  && nextVersion < nextVersion' 
                  && (nextVersion <= exitBlockOpt.value.0 < nextVersion')
                  && res.0.value.successors.Keys <= CoveringSet(nextVersion, nextVersion', {precedingBlock.0}, {exitBlockOpt.value.0})
                )
  {
    match c
    case SimpleCmd(simpleC) => (None, nextVersion, Some((precedingBlock.0, precedingBlock.1+[simpleC])))
    case Seq(thn, els) =>
      var (optCfg1, nextVersion1, optExit1) := AstToCfgAux(thn, precedingBlock, nextVersion);

      if optExit1.None? then
        //els will never be reached
        (optCfg1, nextVersion1, optExit1)
      else
        var (optCfg2, nextVersion2, optExit2) := AstToCfgAux(els, optExit1.value, nextVersion1);

        if optCfg1.None? then
          //since the exit block for thn becomes the preceding block for els, we can take the result for els
          assert optCfg2.Some? ==> nextVersion == nextVersion1 && optExit1.value.0 == precedingBlock.0;
          (optCfg2, nextVersion2, optExit2)
        else if optCfg2.None? then
          var cfg1 := optCfg1.value;
          assert optExit2.value.0 == optExit1.value.0;
          assert nextVersion1 == nextVersion2;
          (optCfg1, nextVersion2, optExit2)
        else
          //merge cfgs
          var cfg1 := optCfg1.value;
          var cfg2 := optCfg2.value;

          var cover1 := CoveringSet(nextVersion, nextVersion1, {precedingBlock.0}, {optExit1.value.0});
          var cover2 := CoveringSet(nextVersion1, nextVersion2, {optExit1.value.0}, {optExit2.value.0});
          var cover3 := CoveringSet(nextVersion, nextVersion2, {precedingBlock.0}, {optExit2.value.0});
          assert cover1 + cover2 <= cover3;

          (Some(Cfg(cfg1.entry, cfg1.blocks + cfg2.blocks, cfg1.successors + cfg2.successors)), nextVersion2, optExit2)
    case If(optCond, thn, els) => 
      /** CFG thn branch */
      var (thnStartId, thnStartBlock) := if optCond.Some? then (nextVersion, [Assume(optCond.value)]) else (nextVersion, []);
      var (optCfg1, nextVersion1, optExit1) := AstToCfgAux(thn, (thnStartId, thnStartBlock), nextVersion+1);

      /** CFG els branch */
      var (elsStartId, elsStartBlock) := if optCond.Some? then (nextVersion1, [Assume(UnOp(Not, optCond.value))]) else (nextVersion1, []);
      var (optCfg2, nextVersion2, optExit2) := AstToCfgAux(els, (elsStartId, elsStartBlock), nextVersion1+1);

      /** 
        * precedingBlock is the entry block 
        * connect precedingBlock to thnStartId and elsStartId
        * if then/else branch have active exit blocks, then connect those to a fresh basic block, which will became the active basic block
      */
      var (entryBlockId, entryBlock) := precedingBlock;

      /** new successor relation */
      var (blocksThnEls, successorsThnEls) := 
        if optCfg1.Some? && optCfg2.Some? then
          (optCfg1.value.blocks + optCfg2.value.blocks, optCfg1.value.successors + optCfg2.value.successors)
        else if optCfg1.Some? then
          (optCfg1.value.blocks, optCfg1.value.successors)
        else if optCfg2.Some? then
          (optCfg2.value.blocks, optCfg2.value.successors)
        else
          (map[], map[]);

      var blocksBeforeJoin := blocksThnEls[entryBlockId := entryBlock]; 
      var successorsBeforeJoin := successorsThnEls[entryBlockId := [thnStartId, elsStartId]];

      if optExit1.Some? && optExit2.Some? then
        //connect the end of both branches to a new block
        var (joinId, joinBlock) := (nextVersion2, []);
        var (thnExitId, thenExitBlock) := optExit1.value;
        var (elsExitId, elseExitBlock) := optExit2.value;

        var blocks := blocksBeforeJoin[thnExitId := thenExitBlock];
        var successors := successorsBeforeJoin[thnExitId := [joinId]][elsExitId := [joinId]];
        var cfg := Cfg(entryBlockId, blocks, successors);

        (Some(cfg), nextVersion2+1, Some((joinId, joinBlock)))
      else 
        var cfg := Cfg(entryBlockId, blocksBeforeJoin, successorsBeforeJoin);
        var optExitResult := if optExit1.Some? then optExit1 else optExit2;
        (Some(cfg), nextVersion2, optExitResult)
  }

  function CoveringSet(oldVersion: nat, newVersion: nat, including: set<nat>, excluding: set<nat>) : set<nat>
  {
    ((set x : nat | oldVersion <= x < newVersion) + including) - excluding
  }

  lemma AstToCfgAcyclic(
    c: Cmd, 
    precedingBlock: (BlockId, BasicBlock), 
    nextVersion: BlockId)
    requires NoBreaksScopesLoops(c)
    requires precedingBlock.0 < nextVersion
    ensures  
      var res := AstToCfgAux(c, precedingBlock, nextVersion); 
      var nextVersion' := res.1;
      var (exitBlockId, exitBlock) := res.2.value;

      if res.0.Some? then  
        var cfg := res.0.value;
        var s := cfg.successors;
        
        && cfg.entry == precedingBlock.0
        && (forall n :: n in s.Keys ==>   
            (forall i :: 0 <= i < |s[n]| ==> (s[n][i] == exitBlockId || s[n][i] in s.Keys))) 
        && cfg.entry in s.Keys 
        && IsAcyclicAlt(cfg.successors, cfg.entry, CoveringSet(nextVersion, nextVersion', {precedingBlock.0}, {exitBlockId}))

      else  
        precedingBlock.0 == exitBlockId 
        //TODO: && precedingBlock.1 <= exitBlock
  {
    match c {
      case SimpleCmd(_) => 
      case Seq(thn, els) =>
        var (optCfg1, nextVersion1, optExit1) := AstToCfgAux(thn, precedingBlock, nextVersion);

        if optExit1.None? {
          //els will never be reached
          //this case cannot occur in the simplified setting
          assert false;
        } else {
          var (optCfg2, nextVersion2, optExit2) := AstToCfgAux(els, optExit1.value, nextVersion1);
          AstToCfgAcyclic(els, optExit1.value, nextVersion2);

          var (exitBlockId2, exitBlock2) := optExit2.value;

          if optCfg1.None? {
            //since the exit block for thn becomes the preceding block for els, we can take the result for els
            //(optCfg2, nextVersion2, optExit2)
            if optCfg2.Some? {
              var cfg2 := optCfg2.value;
              
              IsAcyclicLargerCover(
                cfg2.successors, 
                cfg2.entry, 
                CoveringSet(nextVersion1, nextVersion2, {optExit1.value.0}, {exitBlockId2}), 
                CoveringSet(nextVersion, nextVersion2, {optExit1.value.0}, {exitBlockId2})
              );
            }
          } else if optCfg2.None? {
            //(optCfg1, nextVersion2, optExit2)
          } else {
            //merge cfgs
            var cfg1 := optCfg1.value;
            var cfg2 := optCfg2.value;

            var cover1 := CoveringSet(nextVersion, nextVersion1, {precedingBlock.0}, {cfg2.entry});
            var cover2 := CoveringSet(nextVersion1, nextVersion2, {cfg2.entry}, {exitBlockId2});
            var cover3 := CoveringSet(nextVersion, nextVersion2, {precedingBlock.0}, {exitBlockId2});

            assert cover1 !! cover2;
            assert cfg1.successors.Keys !! cfg2.successors.Keys;

            IsAcyclicMerge(
              cfg1.successors, cfg2.successors, cfg1.entry, cfg2.entry, 
              cover1,
              cover2
              );

            IsAcyclicLargerCover(cfg1.successors + cfg2.successors, cfg1.entry, cover1 + cover2, cover3);
          }
        }
      case If(optCond, thn, els) => 
        var (thnStartId, thnStartBlock) := if optCond.Some? then (nextVersion, [Assume(optCond.value)]) else (nextVersion, []);
        var (optCfg1, nextVersion1, optExit1) := AstToCfgAux(thn, (thnStartId, thnStartBlock), nextVersion+1);

        var (elsStartId, elsStartBlock) := if optCond.Some? then (nextVersion1, [Assume(UnOp(Not, optCond.value))]) else (nextVersion1, []);
        var (optCfg2, nextVersion2, optExit2) := AstToCfgAux(els, (elsStartId, elsStartBlock), nextVersion1+1);

        var exit1 := optExit1.value;
        var exit2 := optExit2.value;

        var (entry1, s1) := if optCfg1.Some? then (optCfg1.value.entry, optCfg1.value.successors) else (exit1.0, map[]);
        var (entry2, s2) := if optCfg2.Some? then (optCfg2.value.entry, optCfg2.value.successors) else (exit2.0, map[]);

        var cover1 := CoveringSet(nextVersion+1, nextVersion1, {nextVersion}, {exit1.0});
        assert IsAcyclicAlt(s1, entry1, cover1);

        var cover2 := CoveringSet(nextVersion1+1, nextVersion2, {nextVersion1}, {exit2.0});
        assert IsAcyclicAlt(s2, entry2, cover2);

        IsAcyclicExtend2(s1, s2, entry1, cover1);
        IsAcyclicLargerCover(s1 + s2, entry1, cover1, cover1+cover2);
        assert IsAcyclicAlt(s1 + s2, entry1, cover1+cover2);

        IsAcyclicExtend(s1, s2, entry2, cover2);
        IsAcyclicLargerCover(s1 + s2, entry2, cover2, cover1+cover2);
        assert IsAcyclicAlt(s1 + s2, entry2, cover1+cover2);

        var (entryBlockId, entryBlock) := precedingBlock;

        var successorsBeforeJoin := (s1 + s2)[entryBlockId := [thnStartId, elsStartId]];

        assert IsAcyclicAlt(successorsBeforeJoin, entryBlockId, cover1+cover2+{entryBlockId}) by {
          calc {
            IsAcyclicAlt(successorsBeforeJoin, entryBlockId, cover1+cover2+{entryBlockId});
            IsAcyclicSeqAlt(successorsBeforeJoin, [thnStartId, elsStartId], cover1+cover2);
            IsAcyclicAlt(successorsBeforeJoin, thnStartId, cover1+cover2) &&
            IsAcyclicSeqAlt(successorsBeforeJoin, [elsStartId], cover1+cover2);
            IsAcyclicAlt(successorsBeforeJoin, thnStartId, cover1+cover2) &&
            IsAcyclicAlt(successorsBeforeJoin, elsStartId, cover1+cover2);
            { IsAcyclicUpdate(s1+s2, entry1, entryBlockId, [thnStartId, elsStartId], cover1+cover2);
              IsAcyclicUpdate(s1+s2, entry2, entryBlockId, [thnStartId, elsStartId], cover1+cover2);
            }
            IsAcyclicAlt(s1+s2, thnStartId, cover1+cover2) &&
            IsAcyclicAlt(s1+s2, elsStartId, cover1+cover2);
          }
        }

        var (thnExitId, thenExitBlock) := optExit1.value;
        var (elsExitId, elseExitBlock) := optExit2.value;

        IsAcyclicUpdate2(successorsBeforeJoin, entryBlockId, thnExitId, [nextVersion2], cover1+cover2+{entryBlockId});
        IsAcyclicUpdate2(successorsBeforeJoin[thnExitId := [nextVersion2]], entryBlockId, elsExitId, [nextVersion2], cover1+cover2+{entryBlockId}+{thnExitId});


        var successorsBeforeJoinImpl := 
          if optCfg1.Some? && optCfg2.Some? then
            (s1+s2)[entryBlockId := [thnStartId, elsStartId]]
          else if optCfg1.Some? then
            s1[entryBlockId := [thnStartId, elsStartId]]
          else if optCfg2.Some? then
            s2[entryBlockId := [thnStartId, elsStartId]]
          else 
            (map[])[entryBlockId := [thnStartId, elsStartId]];

        var successors := successorsBeforeJoinImpl[thnExitId := [nextVersion2]][elsExitId := [nextVersion2]];
        var cover3 := cover1+cover2+{entryBlockId}+{thnExitId}+{elsExitId};

        assert IsAcyclicAlt(successors, entryBlockId, cover3) by {
          assert successors == successorsBeforeJoin[thnExitId := [nextVersion2]][elsExitId := [nextVersion2]];
        }
        
        assert IsAcyclicAlt(successors, entryBlockId, CoveringSet(nextVersion, nextVersion2+1, {precedingBlock.0}, {nextVersion2})) by {
          assert cover3 == CoveringSet(nextVersion, nextVersion2+1, {precedingBlock.0}, {nextVersion2});
        }
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