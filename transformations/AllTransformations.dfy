/** Top-level module that invokes all the Boogie transformations */

include "LoopElim.dfy"
include "IfGuardElim.dfy"
include "DesugarScopedVarsImpl.dfy"
include "NormalizeAst.dfy"
include "AstToCfg_simple.dfy"
include "Passification.dfy"
include "VCGen.dfy"
include "../lang/BoogieLang.dfy"
include "../util/AstSubsetPredicates.dfy"
include "../util/CfgHelper.dfy"

module AllTransformations
{

  import opened BoogieLang 
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

  function method AllTransformations(c: Cmd) : Expr
    requires NoBreaks(c) //TODO: lift
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
    
    assert NoBreaksScopedVarsLoops(c4);

    /** Ast-to-CFG */
    var (g1, blockSeq) := AstToCfg.AstToCfg(c4);

    /** Compute auxiliary CFG data */
    var pred := CfgHelper.PredecessorMap(g1.successors, blockSeq);

    CfgHelper.PredecessorMapCorrect(g1.successors, blockSeq);

    var topo := CfgHelper.TopologicalOrder(g1, blockSeq);

    Expr.TrueExpr

    /*
    assume (forall i | 0 <= i < |topo| :: topo[i] in pred.Keys ==> (set x | x in pred[topo[i]]) <= (set j | 0 <= j < i :: topo[j]));

    /** Passification */
    var g2 := Passification.PassifyCfg(g1, topo, pred);

    /** VCGen */

    var vc := 
      if |topo| == 0 then
        Expr.TrueExpr
      else 
        VCGen.GenerateVC(g2, topo);

    vc
    */
  }

  //TODO
  //lemma AllTransformationsCorrect(c: Cmd)

}