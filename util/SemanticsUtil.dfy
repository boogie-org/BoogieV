include "../lang/BoogieSemantics.dfy"
include "../lang/Cfg.dfy"
include "Util.dfy"

module SemanticsUtil {
  import opened BoogieLang
	import opened BoogieSemantics
  import opened BoogieCfg
  import opened Wrappers

  lemma WpIfEquivAnd<A(!new)>(a: absval_interp<A>, thn: Cmd, els: Cmd, post: WpPost<A>)
    requires LabelsWellDefAux(If(None, thn, els), post.scopes.Keys)
    ensures forall s :: 
      WpCmd(a, If(None, thn, els), post)(s)
    == 
      Util.AndOpt(WpCmd(a, thn, post)(s), WpCmd(a, els, post)(s))
  {
    reveal WpCmd();
  }

  lemma WpShallowAssumeFalse<A(!new)>(a: absval_interp<A>, e: Expr, thn: Cmd, els: Cmd, post: Predicate<A>, s: state<A>)
  requires ExprEvalBoolOpt(a, e, s) == Some(false)
  ensures WpSimpleCmd(a, Assume(e), post)(s) == Some(true)
  { 
  }

  lemma WpShallowIfEquiv<A(!new)>(a: absval_interp<A>, guard: Expr, thn: Cmd, els: Cmd, post: WpPost<A>, s: state<A>)
  requires LabelsWellDefAux(thn, post.scopes.Keys) && LabelsWellDefAux(els, post.scopes.Keys)
  ensures WpCmd(a, If(Some(guard), thn, els), post)(s) ==
          WpCmd(a, If(None, Seq(SimpleCmd(Assume(guard)), thn), Seq(SimpleCmd(Assume(UnOp(Not, guard))), els)), post)(s)
  {  
    reveal WpCmd();
    calc {
      WpCmd(a, If(Some(guard), thn, els), post)(s);
      { WpShallowIfEquiv2(a, guard, thn, els, post, s); }
      Util.AndOpt(
        WpSimpleCmd(a, Assume(guard), WpCmd(a, thn, post))(s),
        WpSimpleCmd(a, Assume(UnOp(Not, guard)), WpCmd(a, els, post))(s)
      );
      Util.AndOpt(
        WpCmd(a, Seq(SimpleCmd(Assume(guard)), thn), post)(s),
        WpCmd(a, Seq(SimpleCmd(Assume(UnOp(Not, guard))), els), post)(s)
      );
      WpCmd(a, If(None, Seq(SimpleCmd(Assume(guard)), thn), Seq(SimpleCmd(Assume(UnOp(Not, guard))), els)), post)(s);
    }
  }

  lemma WpShallowIfEquiv2<A(!new)>(a: absval_interp<A>, guard: Expr, thn: Cmd, els: Cmd, post: WpPost, s: state<A>)
  requires LabelsWellDefAux(thn, post.scopes.Keys) && LabelsWellDefAux(els, post.scopes.Keys)
  ensures WpCmd(a, If(Some(guard), thn, els), post)(s) ==
          Util.AndOpt(
            WpSimpleCmd(a, Assume(guard), WpCmd(a, thn, post))(s),
            WpSimpleCmd(a, Assume(UnOp(Not, guard)), WpCmd(a, els, post))(s)
          )
          //TODO maybe use proof from above and then apply this lemma for above proof
  {
    reveal WpCmd();
    var guardOptVal := ExprEvalBoolOpt(a, guard, s);

    if(guardOptVal.Some?) {
      var guardVal := guardOptVal.value;

      var actualAssume := if guardVal then Assume(guard) else Assume(UnOp(Not, guard));
      var actualBranch := if guardVal then thn else els;

      var trivialAssume := if !guardVal then Assume(guard) else Assume(UnOp(Not, guard));
      var trivialBranch := if !guardVal then thn else els;

      calc {
        WpCmd(a, If(Some(guard), thn, els), post)(s);
        WpCmd(a, actualBranch, post)(s);
        WpSimpleCmd(a, actualAssume, WpCmd(a, actualBranch, post))(s);
      }

      calc {
        WpCmd(a, Seq(SimpleCmd(trivialAssume), trivialBranch), post)(s);
        WpSimpleCmd(a, trivialAssume, WpCmd(a, trivialBranch, post))(s);
        Some(true);
      }
    } else {
      calc {
        WpSimpleCmd(a, Assume(guard), WpCmd(a, thn, post))(s);
        None;
      }

      calc {
        Util.AndOpt(WpCmd(a, Seq(SimpleCmd(Assume(guard)), thn), post)(s), WpCmd(a, Seq(SimpleCmd(Assume(UnOp(Not, guard))), els), post)(s));
        None;
        WpCmd(a, If(Some(guard), thn, els), post)(s);
      }
    }
  } 

  lemma WpCfgConjunctionIndepOutsideCover<A(!new)>(a: absval_interp<A>, cfg: Cfg, updatedBlock: (BlockId, SimpleCmd), entries: seq<BlockId>, p: Predicate<A>, cover: set<BlockId>)
    requires |entries| > 0
    requires cfg.successors.Keys <= cfg.blocks.Keys
    requires updatedBlock.0 !in cover
    requires updatedBlock.0 in cfg.successors.Keys
    ensures 
      var cfg' := Cfg(cfg.entry, cfg.blocks[updatedBlock.0 := updatedBlock.1], cfg.successors);
      WpCfgConjunction(a, cfg, entries, p, cover) == WpCfgConjunction(a, cfg', entries, p, cover);
    decreases cover, 1, entries
  {
    WpCfgIndepOutsideCover(a, cfg, updatedBlock, entries[0], p, cover);
  }

  lemma WpCfgIndepOutsideCover<A(!new)>(a: absval_interp<A>, cfg: Cfg, updatedBlock: (BlockId, SimpleCmd), entry: BlockId, p: Predicate<A>, cover: set<BlockId>)
    requires cfg.successors.Keys <= cfg.blocks.Keys
    requires updatedBlock.0 !in cover
    requires updatedBlock.0 in cfg.successors.Keys
    ensures 
      var cfg' := Cfg(cfg.entry, cfg.blocks[updatedBlock.0 := updatedBlock.1], cfg.successors);
      WpCfg(a, cfg, entry, p, cover) == WpCfg(a, cfg', entry, p, cover);
  decreases cover, 0
  {
    var (updId, updCmd) := updatedBlock;
    var cfg' := Cfg(cfg.entry, cfg.blocks[updId := updCmd], cfg.successors);

    if IsAcyclic(cfg.successors, entry, cover) {
      var successors := if entry in cfg.successors.Keys then cfg.successors[entry] else [];
      if successors != [] {
        assert updId != entry; //since entry is in cover, but updId is not
        WpCfgConjunctionIndepOutsideCover(a, cfg, updatedBlock, successors, p, cover-{entry});
      } else {
        /* If entry in cfg.successors.Keys, then we get that updId != entry for the same
        reason as in the above branch. Otherwise, we get that updId != entry because
        updId in cfg.successors.Keys. */
      }
    }
  }

  lemma WpCfgEntrySplit<A(!new)>(a: absval_interp<A>, cfg: Cfg, entry: BlockId, prefix: SimpleCmd, suffix: SimpleCmd, p: Predicate<A>, cover: set<BlockId>)
  requires cfg.successors.Keys <= cfg.blocks.Keys
  requires entry in cfg.blocks
  requires cfg.blocks[entry] == SeqSimple(prefix, suffix)
  requires IsAcyclic(cfg.successors, entry, cover)
  ensures 
    var cfg' := Cfg(cfg.entry, cfg.blocks[entry := suffix], cfg.successors);
    WpCfg(a, cfg, entry, p, cover) == WpSimpleCmd(a, prefix, WpCfg(a, cfg', entry, p, cover))
  {
    if IsAcyclic(cfg.successors, entry, cover) {
      var cfg' := Cfg(cfg.entry, cfg.blocks[entry := suffix], cfg.successors);
      var successors := if entry in cfg.successors.Keys then cfg.successors[entry] else [];

      var block := cfg.blocks[entry];
      if successors == [] {
        calc {
          WpCfg(a, cfg, entry, p, cover);
          WpSimpleCmd(a, SeqSimple(prefix, suffix), p);
          WpSimpleCmd(a, prefix, WpSimpleCmd(a, suffix, p));
          WpSimpleCmd(a, prefix, WpCfg(a, cfg', entry, p, cover));
        }
      } else {
        calc {
          WpCfg(a, cfg, entry, p, cover);
          WpSimpleCmd(a, SeqSimple(prefix, suffix), WpCfgConjunction(a, cfg, successors, p, cover - {entry}));
          { WpCfgConjunctionIndepOutsideCover(a, cfg, (entry, suffix), successors, p, cover - {entry}); }
          WpSimpleCmd(a, SeqSimple(prefix, suffix), WpCfgConjunction(a, cfg', successors, p, cover - {entry}));
          WpSimpleCmd(a, prefix, WpSimpleCmd(a, suffix, WpCfgConjunction(a, cfg', successors, p, cover - {entry})));
          WpSimpleCmd(a, prefix, WpCfg(a, cfg', entry, p, cover));
        }
      }
    }
  }

  lemma ForallVarDeclsAnd<A(!new)>(a: absval_interp<A>, d: seq<VarDecl>, p: Predicate<A>, q: Predicate<A>, s: state<A>)
  ensures ForallVarDecls(a, d, s' => Util.AndOpt(p(s'), q(s')))(s) == Util.AndOpt(ForallVarDecls(a, d, p)(s), ForallVarDecls(a, d, q)(s))
  {
    var r := s' => Util.AndOpt(p(s'), q(s'));
    var res := ForallVarDecls(a, d, r)(s);

    if |d| == 0 {
      reveal ForallVarDecls();
    } else {
      if res == None {
        NoneForallVarDecls(a, d, r, s);
        var vs :| ValuesRespectDecls(a, vs, d) && Util.AndOpt(p(StateUpdVarDecls(s, d, vs)), q(StateUpdVarDecls(s, d, vs))) == None;
        var s' := StateUpdVarDecls(s, d, vs); 
        if p(s') == None {
          NoneForallVarDecls2(a, d, vs, p, s);
        } else {
          assert q(s') == None;
          NoneForallVarDecls2(a, d, vs, q, s);
        }
      } else if res == Some(true) {
        forall vs
        | ValuesRespectDecls(a, vs, d)
        ensures Util.AndOpt(p(StateUpdVarDecls(s, d, vs)), q(StateUpdVarDecls(s, d, vs))) == Some(true)
        {
          SomeTrueForallVarDecls2(a, d, r, s, vs);
        }

        SomeTrueForallVarDecls(a, d, p, s);
        SomeTrueForallVarDecls(a, d, q, s);
      } else {
        assert res == Some(false) by {
          reveal ForallVarDecls();
        }

        forall vs 
        | ValuesRespectDecls(a, vs, d)
        ensures p(StateUpdVarDecls(s, d, vs)).Some? && q(StateUpdVarDecls(s, d, vs)).Some?
        {
          SomeForallVarDecls2(a, d, r, s, vs);
        }

        SomeForallVarDecls3(a, d, p, s);
        SomeForallVarDecls3(a, d, q, s);

        SomeFalseForallVarDecls2(a, d, r, s);

        var vs :| ValuesRespectDecls(a, vs, d) && r(StateUpdVarDecls(s, d, vs)) == Some(false);
        var s' := StateUpdVarDecls(s, d, vs);
        var b1, b2 :| p(s') == Some(b1) && q(s') == Some(b2);

        if(!b1) {
          SomeFalseForallVarDecls(a, d, p, s, vs);
        } else {
          assert !b2;
          SomeFalseForallVarDecls(a, d, q, s, vs);
        }
      }
    }
  }
  
}