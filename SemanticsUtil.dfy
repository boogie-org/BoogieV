include "BoogieSemantics.dfy"
include "Cfg.dfy"
include "Util.dfy"

module SemanticsUtil {
  import opened BoogieLang
	import opened BoogieSemantics
  import opened BoogieCfg
  import opened Wrappers

  lemma WpShallowIfEquiv<A(!new)>(a: absval_interp<A>, guard: Expr, thn: Cmd, els: Cmd, post: WpPostShallow)
  requires LabelsWellDefAux(thn, post.scopes.Keys) && LabelsWellDefAux(els, post.scopes.Keys)
  ensures WpShallow(a, If(Some(guard), thn, els), post) ==
          WpShallow(a, If(None, Seq(SimpleCmd(Assume(guard)), thn), Seq(SimpleCmd(Assume(UnOp(Not, guard))), els)), post)

  lemma WpShallowIfEquiv2<A(!new)>(a: absval_interp<A>, guard: Expr, thn: Cmd, els: Cmd, post: WpPostShallow, s: state<A>)
  requires LabelsWellDefAux(thn, post.scopes.Keys) && LabelsWellDefAux(els, post.scopes.Keys)
  ensures WpShallow(a, If(Some(guard), thn, els), post)(s) ==
          Util.AndOpt(
            WpShallowSimpleCmd(a, Assume(guard), WpShallow(a, thn, post))(s),
            WpShallowSimpleCmd(a, Assume(UnOp(Not, guard)), WpShallow(a, els, post))(s)
          )
  
  lemma WpCfgEntrySplit<A(!new)>(a: absval_interp<A>, cfg: Cfg, entry: BlockId, prefix: SimpleCmd, suffix: SimpleCmd, p: Predicate<A>, cover: set<BlockId>)
  requires cfg.successors.Keys <= cfg.blocks.Keys
  requires entry in cfg.blocks
  requires cfg.blocks[entry] == SeqSimple(prefix, suffix)
  ensures 
    var cfg' := Cfg(cfg.entry, cfg.blocks[entry := suffix], cfg.successors);
    WpCfg(a, cfg, entry, p, cover) == WpShallowSimpleCmd(a, prefix, WpCfg(a, cfg', entry, p, cover))
  
}