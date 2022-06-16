include "AstToCfg_simple.dfy"


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
      IsAcyclic(cfg.successors, cfg.entry, CoveringSet2(nextVersion, nextVersion', {exit}))
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
      var cover' := CoveringSet2(nextVersion, nextVersion', {exitOpt.value});

      IsAcyclic(cfg.successors, cfg.entry, CoveringSet2(nextVersion, nextVersion', {exitOpt.value})) ==> 
        WpShallow(a, c, post)(s) == WpCfg(a, cfg, cfg.entry, post.normal, cover')(s);
    {
      match c {
        case SimpleCmd(sc) => 
        case Seq(c1, c2) =>
          var (cfg1, nextVersion1, exitOpt1) := AstToCfgAux(c1, nextVersion);
          var exit1 := exitOpt1.value;
          
          var (cfg2, nextVersion2, exitOpt2) := AstToCfgAux(c2, nextVersion1);
          var exit2 := exitOpt2.value; 

          var cover1 := CoveringSet2(nextVersion, nextVersion1, {exitOpt1.value});
          var cover2 := CoveringSet2(nextVersion1, nextVersion2, {exitOpt2.value});
          var cover3 := CoveringSet2(nextVersion, nextVersion2, {exitOpt2.value});
          assert cover1 + cover2 <= cover3;

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

                  assert cfg1.blocks.Keys == cfg1.successors.Keys + {exitOpt1.value};
                  assert cfg2.blocks.Keys == cfg2.successors.Keys + {exitOpt2.value};
                  assert cfg1.successors.Keys <= CoveringSet2(nextVersion, nextVersion1, {exit1});
                  assert cfg2.successors.Keys <= CoveringSet2(nextVersion1, nextVersion2, {exit1});
                  assert CoveringSet2(nextVersion, nextVersion1, {}) !! CoveringSet2(nextVersion1, nextVersion2, {});
                  assert cover3 == cover1+cover2+{exit1};
                  
                  WpCfgMerge(a, cfg1, cfg2, cfg1.entry, exit1, post.normal, cover1, cover2);
                }
              WpCfg(a, cfg', cfg1.entry, post.normal, cover3)(s);
            }
          }         
        case _ => assume false;
      }

    }

}

