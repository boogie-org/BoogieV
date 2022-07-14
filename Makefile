all: BoogieV

BoogieV:
	dafny /compile:0 lang/BoogieLang.dfy lang/BoogieOp.dfy lang/BoogieSemantics.dfy lang/Cfg.dfy util/Util.dfy util/SemanticsUtil.dfy util/Naming.dfy transformations/LoopElim.dfy transformations/DesugarScopedVarsImpl.dfy transformations/MakeScopedVarsUniqueProof.dfy transformations/NormalizeAst.dfy transformations/AstToCfg_simple.dfy transformations/AstToCfgCorrectness.dfy transformations/Passification.dfy
