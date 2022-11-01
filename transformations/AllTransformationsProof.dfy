include "LoopElim.dfy"
include "IfGuardElim.dfy"
include "DesugarScopedVarsImpl.dfy"
include "NormalizeAst.dfy"
include "AstToCfg_simple.dfy"
include "Passification.dfy"
include "VCGen.dfy"
include "../lang/BoogieLang.dfy"
include "../lang/Cfg.dfy"
include "../util/AstSubsetPredicates.dfy"
include "../util/CfgHelper.dfy"
include "../util/SemanticsUtil.dfy"
include "../smt_interface/SMTInterface.dfy"

module AllTransformationsProof {

  import opened BoogieLang 
  import opened BoogieCfg
  import opened BoogieSemantics
  import opened SemanticsUtil
  import opened Wrappers
  import opened AstSubsetPredicates

  import LoopElim
  import IfGuardElim
  import DesugarScopedVarsImpl
  import NormalizeAst
  import AstToCfg
  import Passification
  import VCGen
  import CfgHelper

  function AllTransformationsUntilCFG(c: Cmd) : (Cfg, seq<BlockId>, set<BlockId>, seq<VarDecl>)
    requires NoBreaks(c) 
  {
    /** Eliminate loops */
    var c1 := LoopElim.EliminateLoops(c); 

    LoopElim.EliminateLoopsPreserveNoBreaks(c);

    /** Eliminate if guards */
    var c2 := IfGuardElim.EliminateIfGuards(c1); 
    
    IfGuardElim.EliminateIfGuardsNoLoops(c1);

    /** Remove scoped variables */
    var (c3, decls3) := DesugarScopedVarsImpl.RemoveScopedVars(c2);
    DesugarScopedVarsImpl.RemoveScopedVarsStructure(c2);
    
    /** Normalize AST */
    var (c4Opt, scExitOpt) := NormalizeAst.NormalizeAst(c3, None);
    var c4 := NormalizeAst.SeqCmdSimpleOpt(c4Opt, scExitOpt);

    NormalizeAst.NormalizeAstPreserveStructure(c3, None);

    assert NoBreaks(c4);
    assert NoLoopsNoIfGuardNoScopedVars(c4) && NoBreaks(c4);
    
    var (g1, blockSeq, cover) := AstToCfg.AstToCfg(c4);
    (g1, blockSeq, cover, decls3)
  }

  lemma AllTransformationsUntilCFGCorrect<A(!new)>(a: absval_interp<A>, c: Cmd, cover: set<BlockId>, s: state<A>)
    requires NoBreaks(c)
    requires LabelsWellDefAux(c, TruePost<A>().scopes.Keys)
    ensures 
        var (g1, blockSeq, cover, decls) := AllTransformationsUntilCFG(c);
        WpCmd(a, c, TruePost())(s) == 
        ForallVarDecls(a, decls, WpCfg(a, g1, g1.entry, TruePred(), cover))(s)
  {
    /** Eliminate loops */
    var c1 := LoopElim.EliminateLoops(c); 

    LoopElim.EliminateLoopsPreserveNoBreaks(c);

    LoopElim.EliminateLoopsCorrect(a, c, s, TruePost()); 
    assert WpCmd(a, c, TruePost())(s) == WpCmd(a, c1, TruePost())(s);

    /** Eliminate if guards */
    var c2 := IfGuardElim.EliminateIfGuards(c1); 

    IfGuardElim.EliminateIfGuardsCorrect(a, c1, s, TruePost());
    assert WpCmd(a, c1, TruePost())(s) == WpCmd(a, c2, TruePost())(s);
    
    IfGuardElim.EliminateIfGuardsNoLoops(c1);

    /** Remove scoped variables */
    var (c3, decls3) := DesugarScopedVarsImpl.RemoveScopedVars(c2);
    DesugarScopedVarsImpl.RemoveScopedVarsStructure(c2);
    
    /** Normalize AST */
    var (c4Opt, scExitOpt) := NormalizeAst.NormalizeAst(c3, None);
    var c4 := NormalizeAst.SeqCmdSimpleOpt(c4Opt, scExitOpt);

    NormalizeAst.NormalizeAstPreserveStructure(c3, None);

    assert NoBreaks(c4);
    assert NoLoopsNoIfGuardNoScopedVars(c4) && NoBreaks(c4);
    
    var (g1, blockSeq, cover) := AstToCfg.AstToCfg(c4);
  }

}