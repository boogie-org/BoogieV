include "../lang/Cfg.dfy"
include "../dafny-libraries/src/Wrappers.dfy"
include "../dafny-libraries/src/Math.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"

module AstToCfg {

  import opened BoogieLang
  import opened Wrappers
  import opened BoogieSemantics
  import Sequences = Seq
  import opened BoogieCfg
  import Math

  predicate NoBreaksScopedVarsLoops(c: Cmd)
  {
    match c
    case SimpleCmd(_) => true
    case Break(optLbl) => false
    case Seq(thn, els) => NoBreaksScopedVarsLoops(thn) && NoBreaksScopedVarsLoops(els)
    case Loop(_,_) => false
    case Scope(_, varDecls, body) => varDecls == [] && NoBreaksScopedVarsLoops(body)
    case If(_, thn, els) => NoBreaksScopedVarsLoops(thn) && NoBreaksScopedVarsLoops(els)
  }

  function {:opaque} CoveringSet(oldVersion: nat, newVersion: nat, exclude: nat) : set<nat>
  {
    (set x : nat | oldVersion <= x < newVersion) - {exclude}
  }

  /** 
    Transforms the Ast `c` into a Cfg.
    `nextVersion`: basic block id that is not reserved (including all ids larger than this one)

    returns:
      a cfg 
      next free version
      exit block of returned cfg 
  */
  function method AstToCfgAux(c: Cmd, nextVersion: BlockId) : (Cfg, BlockId, Option<BlockId>) 
    //Option for exit block needed once break statements are taken into account
    requires NoBreaksScopedVarsLoops(c)
    ensures  var (cfg, nextVersion', exitOpt):= AstToCfgAux(c, nextVersion); 
                exitOpt != None  &&
                var exit := exitOpt.value;
                && cfg.successors.Keys == cfg.blocks.Keys - {exit}
                && nextVersion < nextVersion' 
                && (nextVersion <= exit < nextVersion')
                && (forall n :: n in cfg.blocks.Keys ==> nextVersion <= n < nextVersion')
                && (forall n | nextVersion <= n < nextVersion' :: n in cfg.blocks.Keys)
                && cfg.entry in cfg.blocks.Keys
                && exit in cfg.blocks.Keys
                   //exit block is the only sink block (note that exit block is not in successors.Keys)
                && (forall n :: n in cfg.successors.Keys ==> cfg.successors[n] != []) 
  {
    match c
    case SimpleCmd(simpleC) =>
      (Cfg(nextVersion, map[nextVersion := simpleC], map[]), nextVersion+1, Some(nextVersion))
    case Seq(c1, c2) =>
      var (cfg1, nextVersion1, exitOpt1) := AstToCfgAux(c1, nextVersion);
      if exitOpt1.None? then
        //c2 will never be reached
        (cfg1, nextVersion1, exitOpt1)
      else 
        var (cfg2, nextVersion2, exitOpt2) := AstToCfgAux(c2, nextVersion1);

        var blocks := cfg1.blocks + cfg2.blocks;
        var successors := (cfg1.successors + cfg2.successors)[exitOpt1.value := [cfg2.entry]];
  
        (Cfg(cfg1.entry, cfg1.blocks + cfg2.blocks, successors), nextVersion2, exitOpt2)
    case Scope(_, varDecls, body) =>
      // scoped variable declarations have been compiled away
      assert varDecls == [];

      /* since our precondition ensures that there are no breaks, we need not 
      worry about jumps out of this scope and can just return the result for the 
      body (TODO: lift the precondition) */

      AstToCfgAux(body, nextVersion)

    case If(optCond, thn, els) => 
      /** CFG thn branch */
      var (entryId, entryBlock) := (nextVersion, Skip);
      var (cfgThn, nextVersion1, exitOpt1) := AstToCfgAux(thn, entryId+1);

      var cfgThn' := 
        if optCond.Some? then
          Cfg(cfgThn.entry, cfgThn.blocks[cfgThn.entry := SeqSimple(Assume(optCond.value), cfgThn.blocks[cfgThn.entry])], cfgThn.successors)
        else
          cfgThn;

      /** CFG els branch */
      var (cfgEls, nextVersion2, exitOpt2) := AstToCfgAux(els, nextVersion1);

      var cfgEls' := 
        if optCond.Some? then
          Cfg(cfgEls.entry, cfgEls.blocks[cfgEls.entry := SeqSimple(Assume(UnOp(Not, optCond.value)), cfgEls.blocks[cfgEls.entry])], cfgEls.successors)
        else
          cfgEls;

      /** 
        * connect entry block to thnStartId and elsStartId
        * if then/else branch have active exit blocks, then connect those to a fresh basic block, which will became the active basic block
      */

      /** new successor relation */
      var (blocksThnEls, successorsThnEls) := 
        (cfgThn'.blocks + cfgEls'.blocks, cfgThn'.successors + cfgEls'.successors);

      var blocksBeforeJoin := blocksThnEls[entryId := entryBlock]; 
      var successorsBeforeJoin := successorsThnEls[entryId := [cfgThn'.entry, cfgEls'.entry]];

      if exitOpt1.Some? && exitOpt2.Some? then
        //connect the end of both branches to a new block
        var (joinId, joinBlock) := (nextVersion2, Skip);
        var thnExit := exitOpt1.value;
        var elsExit := exitOpt2.value;

        var blocks := blocksBeforeJoin[joinId := joinBlock];
        var successors := successorsBeforeJoin[thnExit := [joinId]][elsExit := [joinId]];
        var cfg := Cfg(entryId, blocks, successors);

        (cfg, nextVersion2+1, Some(joinId))
      else 
        var cfg := Cfg(entryId, blocksBeforeJoin, successorsBeforeJoin);
        var exitOptResult := if exitOpt1.Some? then exitOpt1 else exitOpt2;
        (cfg, nextVersion2, exitOptResult)
  }

  function method AstToCfg(c: Cmd) : Cfg
    requires NoBreaksScopedVarsLoops(c)
  {
    var (g, _, exit) := AstToCfgAux(c, 0);
    Cfg(g.entry, g.blocks, g.successors[exit.value := []])
  }

  lemma AstToCfgAcyclic(
    c: Cmd, 
    nextVersion: BlockId)
    requires NoBreaksScopedVarsLoops(c)
    ensures  
      var (cfg, nextVersion', exitOpt):= AstToCfgAux(c, nextVersion); 

      var exit := exitOpt.value;
      var s := cfg.successors;
      
      && (forall n :: n in s.Keys ==>   
          (forall i :: 0 <= i < |s[n]| ==> (s[n][i] == exit || s[n][i] in s.Keys))) 
      && cfg.entry in cfg.blocks.Keys 
      && IsAcyclic(cfg.successors, cfg.entry, CoveringSet(nextVersion, nextVersion', exit))
  {
    match c {
      case SimpleCmd(sc) =>  
      case Seq(c1, c2) =>
        var (cfg1, nextVersion1, exitOpt1) := AstToCfgAux(c1, nextVersion);
        var exit1 := exitOpt1.value;
        assert IsAcyclic(cfg1.successors, cfg1.entry, CoveringSet(nextVersion, nextVersion1, exit1));

        var (cfg2, nextVersion2, exitOpt2) := AstToCfgAux(c2, nextVersion1);
        AstToCfgAcyclic(c2, nextVersion2);

        var exit2 := exitOpt2.value;

        //merge cfgs

        var cover1 := CoveringSet(nextVersion, nextVersion1, exit1);
        var cover2 := CoveringSet(nextVersion1, nextVersion2, exit2);
        var cover3 := CoveringSet(nextVersion, nextVersion2, exit2);


        var successors := (cfg1.successors + cfg2.successors)[exitOpt1.value := [cfg2.entry]];
        assert successors == (cfg1.successors[exitOpt1.value := [cfg2.entry]] + cfg2.successors);

        assert cover1 !! cover2 by {
          reveal CoveringSet();
        }
        assert cfg1.successors.Keys !! cfg2.successors.Keys;

        IsAcyclicUpdate2(cfg1.successors, cfg1.entry, exit1, [cfg2.entry], cover1);

        assert IsAcyclic(cfg1.successors[exit1 := [cfg2.entry]], cfg1.entry, cover1+{exit1});

        assert (cover1+{exit1} !! cover2) by {
          reveal CoveringSet();
        }

        IsAcyclicMerge(
          cfg1.successors[exit1 := [cfg2.entry]], cfg2.successors, cfg1.entry, cfg2.entry, 
          cover1+{exit1},
          cover2
          );

        assert (cover1 + {exit1}) + cover2 <= cover3 by {
          reveal CoveringSet();
        }
        IsAcyclicLargerCover(successors, cfg1.entry, (cover1 + {exit1}) + cover2, cover3);
      case Scope(_, varDecls, body) => 
      case If(optCond, thn, els) => 
        /** CFG thn branch */
        var (entryId, entryBlock) := (nextVersion, Skip);
        var (cfgThn, nextVersion1, exitOpt1) := AstToCfgAux(thn, entryId+1);

        var cfgThn' := 
          if optCond.Some? then
            Cfg(cfgThn.entry, cfgThn.blocks[cfgThn.entry := SeqSimple(Assume(optCond.value), cfgThn.blocks[cfgThn.entry])], cfgThn.successors)
          else
            cfgThn;

        /** CFG els branch */
        var (cfgEls, nextVersion2, exitOpt2) := AstToCfgAux(els, nextVersion1);

        var cfgEls' := 
          if optCond.Some? then
            Cfg(cfgEls.entry, cfgEls.blocks[cfgEls.entry := SeqSimple(Assume(UnOp(Not, optCond.value)), cfgEls.blocks[cfgEls.entry])], cfgEls.successors)
          else
            cfgEls;

        var (entry1, s1) := (cfgThn.entry, cfgThn.successors);
        var thnExit := exitOpt1.value;

        var cover1 := CoveringSet(nextVersion+1, nextVersion1, thnExit);
        assert IsAcyclic(s1, entry1, cover1);

        var (entry2, s2) := (cfgEls.entry, cfgEls.successors);
        var elsExit := exitOpt2.value;

        var cover2 := CoveringSet(nextVersion1, nextVersion2, elsExit);
        assert IsAcyclic(s2, entry2, cover2);

        IsAcyclicExtend2(s1, s2, entry1, cover1);
        IsAcyclicLargerCover(s1 + s2, entry1, cover1, cover1+cover2);
        assert IsAcyclic(s1 + s2, entry1, cover1+cover2);

        IsAcyclicExtend(s1, s2, entry2, cover2);
        IsAcyclicLargerCover(s1 + s2, entry2, cover2, cover1+cover2);
        assert IsAcyclic(s1 + s2, entry2, cover1+cover2);

        var successorsBeforeJoin := (s1 + s2)[entryId := [cfgThn'.entry, cfgEls'.entry]];

        assert IsAcyclic(successorsBeforeJoin, entryId, cover1+cover2+{entryId}) by {
          calc {
            IsAcyclic(successorsBeforeJoin, entryId, cover1+cover2+{entryId});
            { reveal CoveringSet(); }
            IsAcyclicSeq(successorsBeforeJoin, [cfgThn'.entry, cfgEls'.entry], cover1+cover2);
            IsAcyclic(successorsBeforeJoin, cfgThn'.entry, cover1+cover2) &&
            IsAcyclicSeq(successorsBeforeJoin, [cfgEls'.entry], cover1+cover2);
            IsAcyclic(successorsBeforeJoin, cfgThn'.entry, cover1+cover2) &&
            IsAcyclic(successorsBeforeJoin, cfgEls'.entry, cover1+cover2);
            { IsAcyclicUpdate(s1+s2, entry1, entryId, [cfgThn'.entry, cfgEls'.entry], cover1+cover2);
              IsAcyclicUpdate(s1+s2, entry2, entryId, [cfgThn'.entry, cfgEls'.entry], cover1+cover2);
            }
            IsAcyclic(s1+s2, cfgThn'.entry, cover1+cover2) &&
            IsAcyclic(s1+s2, cfgEls'.entry, cover1+cover2);
          }
        }

        IsAcyclicUpdate2(successorsBeforeJoin, entryId, thnExit, [nextVersion2], cover1+cover2+{entryId});
        IsAcyclicUpdate2(successorsBeforeJoin[thnExit := [nextVersion2]], entryId, elsExit, [nextVersion2], cover1+cover2+{entryId}+{thnExit});

        var successorsBeforeJoinImpl := (s1+s2)[entryId := [cfgThn'.entry, cfgEls'.entry]];

        var successors := successorsBeforeJoinImpl[thnExit := [nextVersion2]][elsExit := [nextVersion2]];
        var cover3 := cover1+cover2+{entryId}+{thnExit}+{elsExit};

        assert IsAcyclic(successors, entryId, cover3) by {
          assert successors == successorsBeforeJoin[thnExit := [nextVersion2]][elsExit := [nextVersion2]];
        }
        
        assert IsAcyclic(successors, entryId, CoveringSet(nextVersion, nextVersion2+1, nextVersion2)) by {
          reveal CoveringSet();
          assert cover3 == CoveringSet(nextVersion, nextVersion2+1, nextVersion2);
        }
    }
  }           
}