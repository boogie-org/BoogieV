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
include "../smt_interface/SMTInterface.dfy"

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

  method AllTransformations(c: Cmd) returns (e: Expr)
    requires NoBreaks(c) //TODO: lift
  {
    /** Eliminate loops */
    var c1 := LoopElim.EliminateLoops(c); 

    LoopElim.EliminateLoopsPreserveNoBreaks(c);

    print("=====After loop elimination=====\n");
    print(c1.ToString(0));

    /** Eliminate if guards */
    var c2 := IfGuardElim.EliminateIfGuards(c1); 
    print("=====After If guard elimination=====\n");
    print(c2.ToString(0));

    IfGuardElim.EliminateIfGuardsNoLoops(c1);

    /** Remove scoped variables */
    var (c3, decls3) := DesugarScopedVarsImpl.RemoveScopedVars(c2);
    DesugarScopedVarsImpl.RemoveScopedVarsStructure(c2);
    print("=====After removing scoped variables=====\n");
    print(c3.ToString(0));

    /** Normalize AST */
    var (c4Opt, scExitOpt) := NormalizeAst.NormalizeAst(c3, None);
    var c4 := NormalizeAst.SeqCmdSimpleOpt(c4Opt, scExitOpt);
    print("=====After AST normalization=====\n");
    print(c4.ToString(0));

    NormalizeAst.NormalizeAstPreserveStructure(c3, None);

    assert NoBreaks(c4);
    assert NoLoopsNoIfGuardNoScopedVars(c4) && NoBreaks(c4);
    
    /** Ast-to-CFG */
    var (g1, blockSeq, cover) := AstToCfg.AstToCfg(c4);

    /** Compute auxiliary CFG data */
    var pred := CfgHelper.PredecessorMap(g1.successors, blockSeq);

    CfgHelper.PredecessorMapCorrect(g1.successors, blockSeq);

    var topo := CfgHelper.TopologicalOrder(g1);

    //CfgHelper.TopologicalOrderCorrect(g1, cover);
    
    expect (forall i | 0 <= i < |topo| :: topo[i] in pred.Keys ==> 
    (set x | x in pred[topo[i]]) <= (set j | 0 <= j < i :: topo[j]));

    /** Passification */
    var g2 := Passification.PassifyCfg(g1, topo, pred);

    /** VCGen */
    expect g2.entry == topo[0];
    if |topo| == 0 {
      print("no blocks");
    } else {
      print("g1:\n");
      print(g1.blocks[topo[0]].ToString(0));
      print("\n g2:\n");
      print(g2.blocks[topo[0]].ToString(0));
    }

    var vc := 
      if |topo| == 0 then
        Expr.TrueExpr
      else 
        VCGen.GenerateVC(g2, topo);

    return vc;
  }
  
}

import opened BoogieLang
import opened Wrappers
import opened SMTInterface

method Main()
{
  var c := 
    Scope(
      None,
      [("x", TPrim(TInt))], 
      Seq(
        SimpleCmd(Assume(BinOp(Var("x"), Gt, ELit(LitInt(0))))),
        SimpleCmd(Assert(BinOp(Var("x"), Gt, ELit(LitInt(0)))))
      )
    );
  
  var vc := AllTransformations.AllTransformations(c);
  var vcString := vc.ToString();
  var vcExprInterface := VCExprInterface.Create();
  
  var vcExpr := VCExprAdapter.ExprToVCExpr(vcExprInterface, vc);
  var vcValid := vcExprInterface.IsVCValid(vcExpr);

  if vcValid {
    print("Input program is correct.");
  } else {
    print("Input program might not be correct.");
  }

  print(vcString);
}