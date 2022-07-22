include "AstToCfg_simple.dfy"
include "../util/Util.dfy"
include "../util/SemanticsUtil.dfy"
include "../util/AstSubsetPredicates.dfy"


module AstToCfgCorrectness
{
  import opened AstToCfg
  import opened BoogieLang
  import opened BoogieSemantics
  import opened BoogieCfg
  import opened Wrappers
  import opened SemanticsUtil
  import opened AstSubsetPredicates

  lemma AstToCfgAcyclic2(
    c: Cmd, 
    nextVersion: BlockId)
    requires NoLoopsNoIfGuardNoScopedVars(c) && NoBreaks(c)
    ensures 
      var AstCfgResult(cfg, nextVersion', exitOpt) := AstToCfgAux(c, nextVersion); 
      var exit := exitOpt.value; //DISCUSS: does not work if replace {exit} by {exitOpt.value}
      IsAcyclic(cfg.successors, cfg.entry, CoveringSet(nextVersion, nextVersion', exit))
  {
    AstToCfgAcyclic(c, nextVersion);
  }

  lemma  LiftWpFromBranchToFull<A(!new)>(a: absval_interp<A>, entry: BlockId, branchTarget: seq<BlockId>, cfgThn: Cfg, cfgEls: Cfg, thnExit: BlockId, elsExit: BlockId, joinId: BlockId, post: Predicate<A>, cover: set<BlockId>, cover': set<BlockId>)
  requires IsAcyclic(cfgThn.successors, cfgThn.entry, cover)
  requires cover + {thnExit} + {elsExit} <= cover'
  requires cfgThn.successors.Keys <= cfgThn.blocks.Keys
  requires cfgEls.successors.Keys <= cfgEls.blocks.Keys
  requires cfgThn.entry in cfgThn.blocks && cfgEls.entry in cfgEls.blocks
  requires joinId !in cfgThn.blocks + cfgEls.blocks
  requires entry !in cfgThn.blocks + cfgEls.blocks
  requires thnExit !in cfgThn.successors + cfgEls.successors
  requires elsExit !in cfgThn.successors + cfgEls.successors
  requires entry != joinId
  requires thnExit in cfgThn.blocks
  requires elsExit in cfgEls.blocks
  requires cfgThn.blocks.Keys !! cfgEls.blocks.Keys
 
  /** Note that the following quantified preconditions are not the most general for this lemma, but they reflect more accurately
      what the intended caller of this lemma knows (using more general preconditions may lead to a significant performance loss).*/
  requires 
      forall n1 :: n1 in cfgThn.successors.Keys ==>   
        (forall i :: 0 <= i < |cfgThn.successors[n1]| ==> cfgThn.successors[n1][i] in cfgThn.successors.Keys || cfgThn.successors[n1][i] == thnExit)
  requires 
      forall n1 :: n1 in cfgEls.successors.Keys ==>   
        (forall i :: 0 <= i < |cfgEls.successors[n1]| ==> cfgEls.successors[n1][i] in cfgEls.successors.Keys || cfgEls.successors[n1][i] == elsExit)
  ensures   var blocksBeforeJoin := (cfgThn.blocks + cfgEls.blocks)[entry := Skip];
            var successorsBeforeJoin := (cfgThn.successors + cfgEls.successors)[entry := branchTarget];
            var blocks := blocksBeforeJoin[joinId := Skip];
            var successors := successorsBeforeJoin[thnExit := [joinId]][elsExit := [joinId]];
            var cfg' := Cfg(entry, blocks, successors);
            WpCfg(a, cfgThn, cfgThn.entry, post, cover) ==
            WpCfg(a, cfg', cfgThn.entry, post, cover'); 
            /* This lemma handles the switch from cover to cover' because to do the swtich one must prove acyclicity of intermediate
               CFG constructions. The goal is that only this lemma needs to do these acyclicity proofs (removing the need for users of the lemma to do so)
               */
  {
    var blocksBeforeJoin := (cfgThn.blocks + cfgEls.blocks)[entry := Skip];
    var successorsBeforeJoin := (cfgThn.successors + cfgEls.successors)[entry := branchTarget];
    var blocks := blocksBeforeJoin[joinId := Skip];
    var successors := successorsBeforeJoin[thnExit := [joinId]][elsExit := [joinId]];
    var cfg' := Cfg(entry, blocks, successors);

    //Obtain IsAcyclic(cfgThn.successors + cfgEls.successors, cfgThn.entry, cover1)
    IsAcyclicExtend2(cfgThn.successors, cfgEls.successors, cfgThn.entry, cover);
    //Obtain IsAcyclic(successorsBeforeJoin, cfgThn.entry, cover)
    IsAcyclicUpdate(cfgThn.successors + cfgEls.successors, cfgThn.entry, entry, branchTarget, cover);
    //Obtain IsAcyclic(successorsBeforeJoin[thnExit := [joinId]], cfgThn.entry, cover + {thnExit}) 
    IsAcyclicUpdate2(successorsBeforeJoin, cfgThn.entry, thnExit, [joinId], cover);
    //Obtain IsAcyclic(successorsBeforeJoin[thnExit := [joinId]][elsExit := [joinId]], cfgThn.entry, cover + {thnExit} + {elsExit}) 
    IsAcyclicUpdate2(successorsBeforeJoin[thnExit := [joinId]], cfgThn.entry, elsExit, [joinId], cover + {thnExit});

    calc {
      WpCfg(a, cfgThn, cfgThn.entry, post, cover);
        { WpCfgEntryIndep(a, cfgThn, entry, cfgThn.entry, post, cover); }
      WpCfg(a, Cfg(entry, cfgThn.blocks, cfgThn.successors), cfgThn.entry, post, cover);
        { var cfg1 := Cfg(entry, cfgThn.blocks, cfgThn.successors);
          var cfgMerged := Cfg(entry, cfgThn.blocks + cfgEls.blocks, cfgThn.successors + cfgEls.successors);
          WpCfgExtend2(a, cfgMerged, cfg1, cfgEls.blocks, cfgEls.successors, cfgThn.entry, post, cover);
        }
      WpCfg(a, Cfg(entry, cfgThn.blocks + cfgEls.blocks, cfgThn.successors + cfgEls.successors), cfgThn.entry, post, cover);
        { 
          var cfg1 := Cfg(entry, cfgThn.blocks + cfgEls.blocks, cfgThn.successors + cfgEls.successors);
          WpCfgUpdate(a, cfg1, cfgThn.entry, (entry, Skip), branchTarget, post, cover); 
        }
      WpCfg(a, Cfg(entry, blocksBeforeJoin, successorsBeforeJoin), cfgThn.entry, post, cover);
        { 
          var cfg := Cfg(entry, blocksBeforeJoin, successorsBeforeJoin);
          WpCfgUpdate2(a, cfg, cfgThn.entry, thnExit, joinId, post, cover); 
        }
      WpCfg(a, Cfg(entry, blocks, successorsBeforeJoin[thnExit := [joinId]]), cfgThn.entry, post, cover + {thnExit});
        { 
          var cfg := Cfg(entry, blocks, successorsBeforeJoin[thnExit := [joinId]]);
          WpCfgUpdate2(a, cfg, cfgThn.entry, elsExit, joinId, post, cover + {thnExit});
          assert blocks[joinId := Skip] == blocks; 
        }
      WpCfg(a, cfg', cfgThn.entry, post, cover + {thnExit} + {elsExit});
        {
          WpCfgLargerCover(a, cfg', cfgThn.entry, post, cover + {thnExit} + {elsExit}, cover');
        }
      WpCfg(a, cfg', cfgThn.entry, post, cover');
    }
  }

  lemma  CoveringSetAux(nextVersion0: nat, nextVersion1: nat, nextVersion2: nat, nextVersion3: nat, exclude1: nat, exclude2: nat, exclude3: nat)
    requires nextVersion0 < nextVersion1 < nextVersion2 <= nextVersion3;
    requires nextVersion0 < exclude1 < nextVersion3
    requires nextVersion0 < exclude2 < nextVersion3
    requires exclude3 < nextVersion1 || exclude3 >= nextVersion2
    requires exclude1 != exclude3
    requires exclude2 != exclude3
    ensures 
          var cover12 := CoveringSet(nextVersion1, nextVersion2, exclude1);
          var cover03 := CoveringSet(nextVersion0, nextVersion3, exclude3);
          cover12 + {exclude1} + {exclude2} <= cover03 - {nextVersion0}
  {
    reveal CoveringSet();
  }

  function CfgForIf(entryId: BlockId, cfgThn: Cfg, thnExit: BlockId, cfgEls: Cfg, elsExit: BlockId, joinId: BlockId) : Cfg
  {
    var blocksBeforeJoin := (cfgThn.blocks + cfgEls.blocks)[entryId := Skip];
    var successorsBeforeJoin := (cfgThn.successors + cfgEls.successors)[entryId := [cfgThn.entry, cfgEls.entry]];
    var blocks := blocksBeforeJoin[joinId := Skip];
    var successors := successorsBeforeJoin[thnExit := [joinId]][elsExit := [joinId]];
    Cfg(entryId, blocks, successors)
  }
  
  
  lemma {:induction false} AstToCfgSemanticsPreservation<A(!new)>(
    a: absval_interp<A>,
    c: Cmd, 
    nextVersion: BlockId,
    post: WpPost<A>,
    s: state<A>)
    requires NoLoopsNoIfGuardNoScopedVars(c) && NoBreaks(c)
    requires LabelsWellDefAux(c, post.scopes.Keys)
    ensures 
      var AstCfgResult(cfg, nextVersion', exitOpt):= AstToCfgAux(c, nextVersion); 
      var exit := exitOpt.value;
      var cover' := CoveringSet(nextVersion, nextVersion', exitOpt.value);

      IsAcyclic(cfg.successors, cfg.entry, CoveringSet(nextVersion, nextVersion', exitOpt.value)) ==> 
        WpCmd(a, c, post)(s) == WpCfg(a, cfg, cfg.entry, post.normal, cover')(s);
  {
    match c {
      case SimpleCmd(sc) => reveal WpCmd();
      case Seq(c1, c2) =>
        var AstCfgResult(cfg1, nextVersion1, exitOpt1) := AstToCfgAux(c1, nextVersion);
        var exit1 := exitOpt1.value;
        
        var AstCfgResult(cfg2, nextVersion2, exitOpt2) := AstToCfgAux(c2, nextVersion1);
        var exit2 := exitOpt2.value; 

        var cover1 := CoveringSet(nextVersion, nextVersion1, exitOpt1.value);
        var cover2 := CoveringSet(nextVersion1, nextVersion2, exitOpt2.value);
        var cover3 := CoveringSet(nextVersion, nextVersion2, exitOpt2.value);
        assert cover1 + cover2 <= cover3 by {
          reveal CoveringSet();
        }

        var successors := (cfg1.successors + cfg2.successors)[exitOpt1.value := [cfg2.entry]];

        assert successors == (cfg1.successors[exitOpt1.value := [cfg2.entry]] + cfg2.successors);

        var cfg1' := Cfg(cfg1.entry, cfg1.blocks, cfg1.successors[exitOpt1.value := [cfg2.entry]]);

        var cfg' := Cfg(cfg1.entry, cfg1.blocks + cfg2.blocks, successors);
        
        AstToCfgAcyclic(c1, nextVersion);
        AstToCfgAcyclic(c2, nextVersion1);

        if IsAcyclic(cfg'.successors, cfg1.entry, cover3)
        {
          calc {
            WpCmd(a, c, post)(s);
            { reveal WpCmd(); }
            WpCmd(a, Seq(c1,c2), post)(s); //normal definition
            { reveal WpCmd(); }
            WpCmd(a, c1, WpPost(WpCmd(a, c2, post), post.currentScope, post.scopes))(s); //IH
            {
              AstToCfgSemanticsPreservation(a, c1, nextVersion, WpPost(WpCmd(a, c2, post), post.currentScope, post.scopes), s);
            }
            WpCfg(a, cfg1, cfg1.entry, WpCmd(a, c2, post), cover1)(s); //IH + pointwise
            {
              forall s' | true
              ensures WpCmd(a, c2, post)(s') == WpCfg(a, cfg2, cfg2.entry, post.normal, cover2)(s')
              { 
                AstToCfgSemanticsPreservation(a, c2, nextVersion1, post, s');
              }
              WpCfgPointwise(a, cfg1, cfg1.entry, WpCmd(a, c2, post), WpCfg(a, cfg2, cfg2.entry, post.normal, cover2), cover1, s);
            }
            WpCfg(a, cfg1, cfg1.entry, WpCfg(a, cfg2, cfg2.entry, post.normal, cover2), cover1)(s); 
              { 
                reveal CoveringSet();

                assert cfg1.blocks.Keys == cfg1.successors.Keys + {exitOpt1.value};
                assert cfg2.blocks.Keys == cfg2.successors.Keys + {exitOpt2.value};
                assert cfg1.successors.Keys <= CoveringSet(nextVersion, nextVersion1, exit1); 
                assert cfg2.successors.Keys <= CoveringSet(nextVersion1, nextVersion2, exit1); 
                //assert CoveringSet(nextVersion, nextVersion1, {}) !! CoveringSet(nextVersion1, nextVersion2, {}); 
                assert cover3 == cover1+cover2+{exit1};
                
                assert cfg1.blocks.Keys !! cover2;

                WpCfgMerge(a, cfg1, cfg2, cfg1.entry, exit1, post.normal, cover1, cover2);
              }
            WpCfg(a, cfg', cfg1.entry, post.normal, cover3)(s);
          }
        }         
      case Scope(optLabel, varDecls, body) =>
        assert varDecls == []; 
        var AstCfgResult(bodyCfg, nextVersion', exitOpt) := AstToCfgAux(body, nextVersion);
        var exit := exitOpt.value;
        var cover := CoveringSet(nextVersion, nextVersion', exit);

        /** In this simplified setting without breaks, adjusting the scope postconditions 
        is not required. However, if one does not adjust the scope postconditions, then one
        needs to prove that this results in the same semantics as with breaks. Here 
        we just update the scopes to match the reference semantics. */

        var updatedScopes := 
          if optLabel.Some? then 
            post.scopes[optLabel.value := post.normal]
          else post.scopes;

        assert updatedScopes.Keys == if optLabel.Some? then {optLabel.value} + post.scopes.Keys else post.scopes.Keys;
        var post' := WpPost(post.normal, post.normal, updatedScopes);
        var unquantifiedBody := 
          WpCmd(a, body, ResetVarsPost(varDecls, post', s));

        calc {
          WpCmd(a, c, post)(s);
          { reveal WpCmd(); }
          ForallVarDecls(a, varDecls, unquantifiedBody)(s);
          { //scoped variable declarations have been compiled away
            reveal ForallVarDecls();
            assert varDecls == []; 
          }
          unquantifiedBody(s);
          WpCmd(a, body, ResetVarsPost([], post', s))(s);
          { 
            WpCmdPointwise(a, body, ResetVarsPost([], post', s), post', s);
          }
          WpCmd(a, body, post')(s);
          { AstToCfgAcyclic2(body, nextVersion);
            AstToCfgSemanticsPreservation(a, body, nextVersion, post', s); }
          WpCfg(a, bodyCfg, bodyCfg.entry, post.normal, cover)(s);
        }
      case If(optCond, thn, els) =>
        /** CFG thn branch */
        var (entry, entryBlock) := (nextVersion, Skip);
        var AstCfgResult(cfgThn, nextVersion1, exitOpt1) := AstToCfgAux(thn, entry+1);


        /** CFG els branch */
        var AstCfgResult(cfgEls, nextVersion2, exitOpt2) := AstToCfgAux(els, nextVersion1);

        var (thnEntry, thnS) := (cfgThn.entry, cfgThn.successors);
        var thnExit := exitOpt1.value;

        var cover1 := CoveringSet(nextVersion+1, nextVersion1, thnExit);
        AstToCfgAcyclic(thn, entry+1);
        assert IsAcyclic(thnS, thnEntry, cover1);

        var (elsEntry, elsS) := (cfgEls.entry, cfgEls.successors);
        var elsExit := exitOpt2.value;

        var cover2 := CoveringSet(nextVersion1, nextVersion2, elsExit);
        AstToCfgAcyclic(els, nextVersion1);
        assert IsAcyclic(elsS, elsEntry, cover2);

        var (joinId, joinBlock) := (nextVersion2, Skip);

        /** result cfg */
        var successorsBeforeJoin := (cfgThn.successors + cfgEls.successors)[entry := [cfgThn.entry, cfgEls.entry]];
        var blocksBeforeJoin := (cfgThn.blocks + cfgEls.blocks)[entry := Skip];
        var blocks := blocksBeforeJoin[joinId := joinBlock];
        var successors := successorsBeforeJoin[thnExit := [joinId]][elsExit := [joinId]];
        //var cfg' := Cfg(entry, blocks, successors);

        var cfgThn' := 
          if optCond.Some? then
            Cfg(cfgThn.entry, cfgThn.blocks[cfgThn.entry := SeqSimple(Assume(optCond.value), cfgThn.blocks[cfgThn.entry])], cfgThn.successors)
          else
            cfgThn;

        var cfgEls' := 
          if optCond.Some? then
            Cfg(cfgEls.entry, cfgEls.blocks[cfgEls.entry := SeqSimple(Assume(UnOp(Not, optCond.value)), cfgEls.blocks[cfgEls.entry])], cfgEls.successors)
          else
            cfgEls;

        var cfg' := CfgForIf(entry, cfgThn', thnExit, cfgEls', elsExit, joinId);
        var cover3 := CoveringSet(nextVersion, nextVersion2+1, joinId);
        
        /* we lift the WP of the then-branch-CFG (resp. else-branch-CFG) to the entire Cfg 
          without the guard condition in the then "else-branch-CFG" (resp then-branch-CFG).
          This way we can apply the induction hypothesis to relate the then-AST-command 
          (resp. else-AST-command) with the then-branch-CFG (resp. else-branch-CFG) */

        var cfgThnInter := CfgForIf(entry, cfgThn, thnExit, cfgEls', elsExit, joinId);
        var cfgElsInter := CfgForIf(entry, cfgThn', thnExit, cfgEls, elsExit, joinId);

        /** Lift then-branch-CFG WP */

        forall s' | true 
          ensures WpCmd(a, thn, post)(s') == WpCfg(a, cfgThnInter, cfgThn.entry, post.normal, cover3-{entry})(s');
        {           
          calc {
            WpCmd(a, thn, post)(s');
              {
                AstToCfgSemanticsPreservation(a, thn, entry+1, post, s'); //TODO: very slow, speed up
              }
            WpCfg(a, cfgThn, cfgThn.entry, post.normal, cover1)(s');
              { 
                assert cover1 + {thnExit} + {elsExit} <= cover3-{entry} by {
                  CoveringSetAux(nextVersion, nextVersion+1, nextVersion1, nextVersion2+1, thnExit, elsExit, joinId);
                }
                LiftWpFromBranchToFull(a, entry, [cfgThn.entry, cfgEls.entry], cfgThn, cfgEls', thnExit, elsExit, joinId, post.normal, cover1, cover3-{entry}); 
              }
            WpCfg(a, cfgThnInter, cfgThn.entry, post.normal, cover3-{entry})(s');
          } 
        }

        /** Lift els-branch-CFG WP */
        forall s' | true
          ensures WpCmd(a, els, post)(s') == WpCfg(a, cfgElsInter, cfgEls.entry, post.normal, cover3-{entry})(s');
        {
          calc {
            WpCmd(a, els, post)(s');
              { AstToCfgSemanticsPreservation(a, els, nextVersion1, post, s'); }
            WpCfg(a, cfgEls, cfgEls.entry, post.normal, cover2)(s');
              { 
                assert cover2 + {elsExit} + {thnExit} <= cover3-{entry} by {
                  CoveringSetAux(nextVersion, nextVersion1, nextVersion2, nextVersion2+1, elsExit, thnExit, joinId);
                }
                
                LiftWpFromBranchToFull(a, entry, [cfgThn'.entry, cfgEls.entry], cfgEls, cfgThn', elsExit, thnExit, joinId, post.normal, cover2, cover3-{entry}); 
                assert cfgEls.blocks + cfgThn'.blocks == cfgThn'.blocks + cfgEls.blocks;
                assert cfgEls.successors + cfgThn'.successors == cfgThn'.successors + cfgEls.successors;
                assert successors == successorsBeforeJoin[elsExit := [joinId]][thnExit := [joinId]];
                /** to speed up the proof */
                var blocksBeforeJoin'' := (cfgEls.blocks + cfgThn'.blocks)[entry := Skip];
                var successorsBeforeJoin'' := (cfgEls.successors + cfgThn'.successors)[entry := [cfgThn'.entry, cfgEls.entry]];
                var blocks'' := blocksBeforeJoin''[joinId := Skip];
                var successors'' := successorsBeforeJoin''[elsExit := [joinId]][thnExit := [joinId]];
                var cfg'' := Cfg(entry, blocks'', successors'');
                assert
                  WpCfg(a, cfgEls, cfgEls.entry, post.normal, cover2) ==
                  WpCfg(a, cfg'', cfgEls.entry, post.normal, cover3-{entry}); 
              }
            WpCfg(a, cfgElsInter, cfgEls.entry, post.normal, cover3-{entry})(s');
          }
        }

        if IsAcyclic(cfg'.successors, cfg'.entry, cover3) {
          calc {
            WpCfg(a, cfg', cfg'.entry, post.normal, cover3)(s);
              { assert cfg'.blocks[entry] == Skip;
                assert cfg'.successors[entry] ==  [cfgThn.entry, cfgEls.entry];
              }
            WpSimpleCmd(a, Skip, WpCfgConjunction(a, cfg', [cfgThn.entry, cfgEls.entry], post.normal, cover3-{entry}))(s);
            WpCfgConjunction(a, cfg', [cfgThn.entry, cfgEls.entry], post.normal, cover3-{entry})(s);
            Util.AndOpt(WpCfg(a, cfg', cfgThn.entry, post.normal, cover3-{entry})(s), WpCfg(a, cfg', cfgEls.entry, post.normal, cover3-{entry})(s));
          }

          if(optCond == None) {
            calc {
              Util.AndOpt(WpCfg(a, cfg', cfgThn.entry, post.normal, cover3-{entry})(s), WpCfg(a, cfg', cfgEls.entry, post.normal, cover3-{entry})(s));
              Util.AndOpt(WpCfg(a, cfg', cfgThn.entry, post.normal, cover3-{entry})(s), WpCfg(a, cfg', cfgEls.entry, post.normal, cover3-{entry})(s));
              Util.AndOpt(WpCmd(a, thn, post)(s), WpCmd(a, els, post)(s));
              { reveal WpCmd(); }
              WpCmd(a, c, post)(s);
            }
          } else {
            var guard := optCond.value;

            assert IsAcyclicSeq(cfg'.successors, [cfgThn.entry, cfgEls.entry], cover3-{entry});
            assert && IsAcyclic(cfg'.successors, cfgThn.entry, cover3-{entry})
                    && IsAcyclicSeq(cfg'.successors, [cfgEls.entry], cover3-{entry});
            assert IsAcyclic(cfg'.successors, cfgEls.entry, cover3-{entry});

            //relate then-branch-CFG with then-branch AST
            calc {
              WpCfg(a, cfg', cfgThn.entry, post.normal, cover3-{entry})(s);
              { 
                var thnOrigBlock := cfgThn.blocks[cfgThn.entry];
                var cfgTemp := Cfg(cfg'.entry, cfg'.blocks[cfgThn.entry := thnOrigBlock], cfg'.successors);
                WpCfgEntrySplit(a, cfg', cfgThn.entry, Assume(guard), thnOrigBlock, post.normal, cover3-{entry});
                assert cfgTemp == cfgThnInter;
              }
              WpSimpleCmd(a, Assume(guard), WpCfg(a, cfgThnInter, cfgThn.entry, post.normal, cover3-{entry}))(s);
              { 
                WpSimpleCmdPointwise(a, Assume(guard), WpCfg(a, cfgThnInter, cfgThn.entry, post.normal, cover3-{entry}), WpCmd(a, thn, post), s);
              } 
              WpSimpleCmd(a, Assume(guard), WpCmd(a, thn, post))(s);
            }

            //relate else-branch-CFG with else-branch AST
            calc {
              WpCfg(a, cfg', cfgEls.entry, post.normal, cover3-{entry})(s);
              {  /** This proof step relies on acyclicity currently (since WpCfgEntrySplit relies on acyclicity).
                      It should be possible to not have to rely on acyclicity here. */
                var elsOrigBlock := cfgEls.blocks[cfgEls.entry];
                var cfgTemp := Cfg(cfg'.entry, cfg'.blocks[cfgEls.entry := elsOrigBlock], cfg'.successors);
                WpCfgEntrySplit(a, cfg', cfgEls.entry, Assume(UnOp(Not, guard)), elsOrigBlock, post.normal, cover3-{entry});
                assert cfgTemp == cfgElsInter;
              }
              WpSimpleCmd(a, Assume(UnOp(Not, guard)), WpCfg(a, cfgElsInter, cfgEls.entry, post.normal, cover3-{entry}))(s);
              { 
                WpSimpleCmdPointwise(a, Assume(guard), WpCfg(a, cfgElsInter, cfgEls.entry, post.normal, cover3-{entry}), WpCmd(a, els, post), s);
              }
              WpSimpleCmd(a, Assume(UnOp(Not, guard)), WpCmd(a, els, post))(s);
            }

            //final result
            calc {
              WpCmd(a, c, post)(s);
              { WpShallowIfEquiv2(a, guard, thn, els, post, s); }
              Util.AndOpt(
                WpSimpleCmd(a, Assume(guard), WpCmd(a, thn, post))(s),
                WpSimpleCmd(a, Assume(UnOp(Not, guard)), WpCmd(a, els, post))(s)
              );
              Util.AndOpt(
                WpCfg(a, cfg', cfgThn.entry, post.normal, cover3-{entry})(s), 
                WpCfg(a, cfg', cfgEls.entry, post.normal, cover3-{entry})(s)
              );
            }
          } 
        
        //TODO: proving postcondition takes long, find way to reduce time
        } 
    }
  }
}