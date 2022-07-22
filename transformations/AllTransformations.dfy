/** Top-level module that invokes all the Boogie transformations */

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
  import BoogieCfg

  method AllTransformations(c: Cmd) returns (e: Expr)
    requires NoBreaks(c) //TODO: lift
  {
    /** Eliminate loops */
    var c1 := LoopElim.EliminateLoops(c); 

    LoopElim.EliminateLoopsPreserveNoBreaks(c);

    print("\n=====After loop elimination=====\n");
    print(c1.ToString(0));

    /** Eliminate if guards */
    var c2 := IfGuardElim.EliminateIfGuards(c1); 
    print("\n=====After If guard elimination=====\n");
    print(c2.ToString(0));

    IfGuardElim.EliminateIfGuardsNoLoops(c1);

    /** Remove scoped variables */
    var (c3, decls3) := DesugarScopedVarsImpl.RemoveScopedVars(c2);
    DesugarScopedVarsImpl.RemoveScopedVarsStructure(c2);
    print("\n=====After removing scoped variables=====\n");
    print(c3.ToString(0));

    /** Normalize AST */
    var (c4Opt, scExitOpt) := NormalizeAst.NormalizeAst(c3, None);
    var c4 := NormalizeAst.SeqCmdSimpleOpt(c4Opt, scExitOpt);
    print("\n=====After AST normalization=====\n");
    print(c4.ToString(0));

    NormalizeAst.NormalizeAstPreserveStructure(c3, None);

    assert NoBreaks(c4);
    assert NoLoopsNoIfGuardNoScopedVars(c4) && NoBreaks(c4);
    
    /** Ast-to-CFG */
    var (g1, blockSeq, cover) := AstToCfg.AstToCfg(c4);
    print("\n=====After AST-to-CFG transformation=====\n");
    print(CfgHelper.PrintCfg(g1, blockSeq));

    /** Compute auxiliary CFG data */
    var pred := CfgHelper.PredecessorMap(g1.successors, blockSeq);

    CfgHelper.PredecessorMapCorrect(g1.successors, blockSeq);

    var topo := CfgHelper.TopologicalOrder(g1);

    //CfgHelper.TopologicalOrderCorrect(g1, cover);
    
    expect (forall i | 0 <= i < |topo| :: topo[i] in pred.Keys ==> 
    (set x | x in pred[topo[i]]) <= (set j | 0 <= j < i :: topo[j]));

    /** Passification */
    var g2 := Passification.PassifyCfg(g1, topo, pred);
    print("\n=====After Passification=====\n");
    expect BoogieCfg.CfgWf(g2);

    print(CfgHelper.PrintCfg(g2, topo));

    /** VCGen */
    expect g2.entry == topo[0];

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

module Environment {
  method {:extern "Shims", "GetCommandLineArguments"} GetCommandLineArguments() returns (args: seq<string>)
}

method Main()
{
  /*
  var c := 
    Scope(
      None,
      [("x", TPrim(TInt))], 
      Seq(
        SimpleCmd(Assume(BinOp(Var("x"), Gt, ELit(LitInt(0))))),
        SimpleCmd(Assert(BinOp(Var("x"), Gt, ELit(LitInt(1)))))
      )
    );
  */
  /*
  var c :=
    Scope(
      None,
      [("x", TPrim(TInt)), ("y", TPrim(TInt))], 
      If(Some(BinOp(Var("x"), Gt, ELit(LitInt(0)))),
        SimpleCmd(Assert(BinOp(Var("x"), Gt, ELit(LitInt(0))))),
        SimpleCmd(Assert(BinOp(Var("x"), Le, ELit(LitInt(0)))))
      )
    );
  */
  /*
  var c :=
    Scope(
      None,
      [("x", TPrim(TInt)), ("y", TPrim(TInt))], 
      Seq(
        SimpleCmd(Assign("x", TPrim(TInt), ELit(LitInt(0)))),
        Seq(
          SimpleCmd(Assign("x", TPrim(TInt), BinOp(Var("x"), Add, ELit(LitInt(1))))),
          SimpleCmd(Assert(BinOp(Var("x"), Gt, ELit(LitInt(0)))))
        )
      )
    );
  */

  var c :=
    Scope(
      None,
      [("x", TPrim(TInt)), ("y", TPrim(TInt))], 
      Seq(
        Seq(
          SimpleCmd(Assign("x", TPrim(TInt), ELit(LitInt(1234)))),
          If(Some(BinOp(Var("x"), Gt, ELit(LitInt(0)))),
            SimpleCmd(Assign("x", TPrim(TInt), BinOp(Var("x"), Add, ELit(LitInt(1))))),
            SimpleCmd(Assign("x", TPrim(TInt), BinOp(Var("x"), Add, ELit(LitInt(2)))))
          )
        ),
        SimpleCmd(Assert(BinOp(Var("x"), Gt, ELit(LitInt(0)))))
      )
    );
  
  var args := Environment.GetCommandLineArguments();
  if |args| != 2 {
    print "Expecting exactly two arguments [prover_path] [prover_log_output]";
    return;
  }

  var proverPath := args[0];
  var proverLogPath := args[1];
  
  var vc := AllTransformations.AllTransformations(c);
  var vcString := vc.ToString();

  print("\n=====VC Generation====\n");

  print(vcString+"\n");

  print("\n=====Result=====\n");

  var vcExprInterface := VCExprInterface.Create(proverPath, proverLogPath);
  
  var vcExpr := VCExprAdapter.ExprToVCExpr(vcExprInterface, vc);
  var vcValid := vcExprInterface.IsVCValid(vcExpr);

  if vcValid {
    print("Input program is correct.");
  } else {
    print("Input program might not be correct.");
  }

}