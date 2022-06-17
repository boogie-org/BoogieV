include "AstToCfg_simple.dfy"
include "Util.dfy"


module AstToCfgCorrectness
{
  import opened AstToCfg
  import opened BoogieLang
  import opened BoogieSemantics
  import opened BoogieCfg
  import opened Wrappers

  lemma AstToCfgAcyclic2(
    c: Cmd, 
    nextVersion: BlockId)
    requires NoBreaksScopesLoops(c)
    ensures 
      var (cfg, nextVersion', exitOpt) := AstToCfgAux(c, nextVersion); 
      var exit := exitOpt.value; //DISCUSS: does not work if replace {exit} by {exitOpt.value}
      IsAcyclic(cfg.successors, cfg.entry, CoveringSet(nextVersion, nextVersion', {exit}))
  {
    AstToCfgAcyclic(c, nextVersion);
  }

  lemma WpCfgCoverIndep<A(!new)>(a: absval_interp<A>, cfg: Cfg, n: BlockId, post: Predicate<A>, cover1: set<BlockId>, cover2: set<BlockId>)
    requires cfg.successors.Keys <= cfg.blocks.Keys
    requires IsAcyclic(cfg.successors, n, cover1)
    requires IsAcyclic(cfg.successors, n, cover2)
    ensures WpCfg(a, cfg, n, post, cover1) == WpCfg(a, cfg, n, post, cover2)
 
  lemma AstToCfgSemanticsPreservation<A(!new)>(
    a: absval_interp<A>,
    c: Cmd, 
    nextVersion: BlockId,
    post: WpPostShallow<A>,
    s: state<A>)
    requires NoBreaksScopesLoops(c)
    requires LabelsWellDefAux(c, post.scopes.Keys)
    ensures 
      var (cfg, nextVersion', exitOpt):= AstToCfgAux(c, nextVersion); 
      var exit := exitOpt.value;
      var cover' := CoveringSet(nextVersion, nextVersion', {exitOpt.value});

      IsAcyclic(cfg.successors, cfg.entry, CoveringSet(nextVersion, nextVersion', {exitOpt.value})) ==> 
        WpShallow(a, c, post)(s) == WpCfg(a, cfg, cfg.entry, post.normal, cover')(s);
    {
      match c {
        case SimpleCmd(sc) => 
        case Seq(c1, c2) =>
          assume false; //TODO: remove (just used to speed up verification of if-proof development)
          var (cfg1, nextVersion1, exitOpt1) := AstToCfgAux(c1, nextVersion);
          var exit1 := exitOpt1.value;
          
          var (cfg2, nextVersion2, exitOpt2) := AstToCfgAux(c2, nextVersion1);
          var exit2 := exitOpt2.value; 

          var cover1 := CoveringSet(nextVersion, nextVersion1, {exitOpt1.value});
          var cover2 := CoveringSet(nextVersion1, nextVersion2, {exitOpt2.value});
          var cover3 := CoveringSet(nextVersion, nextVersion2, {exitOpt2.value});
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
              WpShallow(a, c, post)(s);
              WpShallow(a, Seq(c1,c2), post)(s); //normal definition
              WpShallow(a, c1, WpPostShallow(WpShallow(a, c2, post), post.currentScope, post.scopes))(s); //IH
              WpCfg(a, cfg1, cfg1.entry, WpShallow(a, c2, post), cover1)(s); //IH + pointwise
              {
                forall s' | true
                ensures WpShallow(a, c2, post)(s') == WpCfg(a, cfg2, cfg2.entry, post.normal, cover2)(s')
                { 
                  AstToCfgSemanticsPreservation(a, c2, nextVersion1, post, s');
                }
                WpCfgPointwise(a, cfg1, cfg1.entry, WpShallow(a, c2, post), WpCfg(a, cfg2, cfg2.entry, post.normal, cover2), cover1, s);
              }
              WpCfg(a, cfg1, cfg1.entry, WpCfg(a, cfg2, cfg2.entry, post.normal, cover2), cover1)(s); 
                { 
                  reveal CoveringSet();

                  assert cfg1.blocks.Keys == cfg1.successors.Keys + {exitOpt1.value};
                  assert cfg2.blocks.Keys == cfg2.successors.Keys + {exitOpt2.value};
                  assert cfg1.successors.Keys <= CoveringSet(nextVersion, nextVersion1, {exit1}); 
                  assert cfg2.successors.Keys <= CoveringSet(nextVersion1, nextVersion2, {exit1}); 
                  assert CoveringSet(nextVersion, nextVersion1, {}) !! CoveringSet(nextVersion1, nextVersion2, {}); 
                  assert cover3 == cover1+cover2+{exit1};
                  
                  assert cfg1.blocks.Keys !! cover2;

                  WpCfgMerge(a, cfg1, cfg2, cfg1.entry, exit1, post.normal, cover1, cover2);
                }
              WpCfg(a, cfg', cfg1.entry, post.normal, cover3)(s);
            }
          }         
        case If(optCond, thn, els) =>
          //assume false;
          assume optCond == None; //TODO: simple case first, then handle other case

          /** CFG thn branch */
          var (entry, entryBlock) := (nextVersion, Skip);
          var (cfgThn, nextVersion1, exitOpt1) := AstToCfgAux(thn, entry+1);

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

          var (thnEntry, thnS) := (cfgThn.entry, cfgThn.successors);
          var thnExit := exitOpt1.value;

          var cover1 := CoveringSet(nextVersion+1, nextVersion1, {thnExit});
          AstToCfgAcyclic(thn, entry+1);
          assert IsAcyclic(thnS, thnEntry, cover1);

          var (elsEntry, elsS) := (cfgEls.entry, cfgEls.successors);
          var elsExit := exitOpt2.value;

          var cover2 := CoveringSet(nextVersion1, nextVersion2, {elsExit});
          AstToCfgAcyclic(els, nextVersion1);
          assert IsAcyclic(elsS, elsEntry, cover2);

          var blocksBeforeJoin := (cfgThn'.blocks + cfgEls'.blocks)[entry := Skip];
          var successorsBeforeJoin := (cfgThn'.successors + cfgEls'.successors)[entry := [cfgThn'.entry, cfgEls'.entry]];

          var (joinId, joinBlock) := (nextVersion2, Skip);

          /** result data */
          var blocks := blocksBeforeJoin[joinId := joinBlock];
          var successors := successorsBeforeJoin[thnExit := [joinId]][elsExit := [joinId]];
          var cfg' := Cfg(entry, blocks, successors);
          var cover3 := CoveringSet(nextVersion, nextVersion2+1, {joinId});

          /** lift thn branch WP to entire CFG */
          calc {
            WpShallow(a, thn, post)(s);
            WpCfg(a, cfgThn', cfgThn'.entry, post.normal, cover1)(s);
              { WpCfgEntryIndep(a, cfgThn', entry, cfgThn'.entry, post.normal, cover1); }
            WpCfg(a, Cfg(entry, cfgThn'.blocks, cfgThn'.successors), cfgThn'.entry, post.normal, cover1)(s);
              { var cfg1 := Cfg(entry, cfgThn'.blocks, cfgThn'.successors);
                var cfgMerged := Cfg(entry, cfgThn'.blocks + cfgEls'.blocks, cfgThn'.successors + cfgEls'.successors);
                WpCfgExtend2(a, cfgMerged, cfg1, cfgEls'.blocks, cfgEls'.successors, cfgThn'.entry, post.normal, cover1);
              }
            WpCfg(a, Cfg(entry, cfgThn'.blocks + cfgEls'.blocks, cfgThn'.successors + cfgEls'.successors), cfgThn'.entry, post.normal, cover1)(s);
              {assume false;}
            WpCfg(a, Cfg(entry, blocksBeforeJoin, successorsBeforeJoin), cfgThn'.entry, post.normal, cover1)(s);
              {assume false;}
            WpCfg(a, Cfg(entry, blocks, successorsBeforeJoin[thnExit := [joinId]]), cfgThn'.entry, post.normal, cover1)(s);
              {assume false;}
            WpCfg(a, cfg', cfgThn'.entry, post.normal, cover1)(s);
              {assume false;}
            WpCfg(a, cfg', cfgThn'.entry, post.normal, cover3-{entry})(s);
          }

          assume false;

          /** lift els branch WP to entire CFG */
          calc {
            WpShallow(a, els, post)(s);
              {assume false;}
            WpCfg(a, cfg', cfgEls'.entry, post.normal, cover2)(s);
              {assume false;}
            WpCfg(a, cfg', cfgEls'.entry, post.normal, cover3-{entry})(s);
          }


          /*
          var (cfg, nextVersion', exitOpt) := AstToCfgAux(c, nextVersion); 

          assume cfg'.successors == cfg.successors; //TODO: switch to assert
          assume cfg == cfg'; //TODO: switch to assert
          */

          var (cfg, nextVersion', exitOpt):= AstToCfgAux(c, nextVersion); 
          var exit := exitOpt.value;
          var cover' := CoveringSet(nextVersion, nextVersion', {exitOpt.value});

          /*IsAcyclic(cfg.successors, cfg.entry, CoveringSet(nextVersion, nextVersion', {exitOpt.value})) ==> 
            WpShallow(a, c, post)(s) == WpCfg(a, cfg, cfg.entry, post.normal, cover')(s);*/
          
          assert nextVersion' == nextVersion2+1;
          assert cfg'.successors == cfg.successors; //TODO: switch to assert
          assert cfg == cfg'; //TODO: switch to assert

          if IsAcyclic(cfg'.successors, cfg'.entry, cover3) {
            calc {
              WpCfg(a, cfg', cfg'.entry, post.normal, cover3)(s);
                { assert cfg'.blocks[entry] == Skip;
                  assert cfg'.successors[entry] ==  [cfgThn'.entry, cfgEls'.entry];
                }
              WpShallowSimpleCmd(a, Skip, WpCfgConjunction(a, cfg', [cfgThn'.entry, cfgEls'.entry], post.normal, cover3-{entry}))(s);
              WpCfgConjunction(a, cfg', [cfgThn'.entry, cfgEls'.entry], post.normal, cover3-{entry})(s);
              Util.AndOpt(WpCfg(a, cfg', cfgThn'.entry, post.normal, cover3-{entry})(s), WpCfg(a, cfg', cfgEls'.entry, post.normal, cover3-{entry})(s));
              Util.AndOpt(WpShallow(a, thn, post)(s), WpShallow(a, els, post)(s));
              WpShallow(a, c, post)(s);
            }
          }
      }
    }

}

