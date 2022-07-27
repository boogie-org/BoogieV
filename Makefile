all: verify compile 

verify:
	dafny /compile:0 lang/BoogieLang.dfy lang/BoogieOp.dfy lang/BoogieSemantics.dfy lang/Cfg.dfy util/Util.dfy util/SemanticsUtil.dfy util/SortUtil.dfy util/RustanMergeSort.dfy util/Naming.dfy util/CfgHelper.dfy transformations/LoopElim.dfy transformations/DesugarScopedVarsImpl.dfy transformations/MakeScopedVarsUniqueProof.dfy transformations/NormalizeAst.dfy transformations/AstToCfg_simple.dfy transformations/AstToCfgCorrectness.dfy transformations/Passification.dfy transformations/VCGen.dfy transformations/AllTransformations.dfy

compile: 
	{ \
	dotnet build smt_interface/csharp_smt_interface ;\
	dafny /noVerify /out:smt_interface/csharp_smt_interface/bin/Debug/net6.0/AllTransformations.dll /compile:2 /spillTargetCode:3 /useRuntimeLib transformations/AllTransformations.dfy util/Shims.cs smt_interface/csharp_smt_interface/bin/Debug/net6.0/csharp_smt_interface.dll smt_interface/csharp_smt_interface/bin/Debug/net6.0/Boogie.VCExpr.dll ;\
	}