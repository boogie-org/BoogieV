all: BoogieV

BoogieV:
	dafny /compile:0 BoogieLang.dfy BoogieOp.dfy BoogieSemantics.dfy Cfg.dfy LoopElim.dfy Util.dfy SemanticsUtil.dfy Naming.dfy DesugarScopedVarsImpl.dfy MakeScopedVarsUniqueProof.dfy NormalizeAst.dfy AstToCfg_simple.dfy AstToCfgCorrectness.dfy 
