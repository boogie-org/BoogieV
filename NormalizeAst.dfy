include "BoogieLang.dfy"
include "BoogieSemantics.dfy"

module NormalizeAst {
  import opened BoogieLang
  import opened BoogieSemantics
  import opened Wrappers

  function SeqCmdOpt(c1Opt: Option<Cmd>, c2Opt: Option<Cmd>) : Option<Cmd>
  {
    if c1Opt.Some? && c2Opt.Some? then
      Some(Seq(c1Opt.value, c2Opt.value))
    else if c1Opt.Some? then
      Some(c1Opt.value)
    else
      c2Opt
  }

  function SeqSimpleCmdAndCmdOpt(c1Opt: Option<SimpleCmd>, c2: Cmd) : Cmd
  {
    if c1Opt.Some? then
      Seq(SimpleCmd(c1Opt.value), c2)
    else 
      c2
  }

  function SeqCmdAndSimpleCmdOpt(c1Opt: Option<Cmd>, c2Opt: Option<SimpleCmd>) : Cmd
    requires c1Opt.Some? || c2Opt.Some?
  {
    if c1Opt.Some? && c2Opt.Some? then
      Seq(c1Opt.value, SimpleCmd(c2Opt.value))
    else if c1Opt.Some? then
      c1Opt.value
    else
      SimpleCmd(c2Opt.value)
  }

  /** Makes sure that adjacent simple commands are combined into the same simple command.
      This way the AST-to-CFG transformation can be made simpler while reducing the number of generated
      basic blocks. */
  function NormalizeAst(c: Cmd, precedingSimple: Option<SimpleCmd>) : (Option<Cmd>, Option<SimpleCmd>)
    ensures var (cOpt', scExitOpt) := NormalizeAst(c, precedingSimple); cOpt'.Some? || scExitOpt.Some?
  {
    match c 
    case SimpleCmd(sc) => 
      if precedingSimple.Some? then (None, Some(SeqSimple(precedingSimple.value, sc))) else (None, Some(sc))
    case Break(_) => 
      (Some(SeqSimpleCmdAndCmdOpt(precedingSimple, c)), None)
    case Seq(c1, c2) => 
      var (c1Opt', scExitOpt1) := NormalizeAst(c1, precedingSimple);
      var (c2Opt', scExitOpt2) := NormalizeAst(c2, scExitOpt1);

      var prefixCmd := SeqCmdOpt(c1Opt', c2Opt');
      
      (prefixCmd, scExitOpt2)
    case Scope(optLbl, varDecls, body) =>
      var (body', scExitOpt) := NormalizeAst(body, None);
      var bodyNew := SeqCmdAndSimpleCmdOpt(body', scExitOpt);

      (Some(SeqSimpleCmdAndCmdOpt(precedingSimple, Scope(optLbl, varDecls, bodyNew))), None)
    case If(optCond, thn, els) =>
      var (thnOpt', scExitOpt1) := NormalizeAst(thn, None);
      var (elsOpt', scExitOpt2) := NormalizeAst(els, None);

      var thn' := SeqCmdAndSimpleCmdOpt(thnOpt', scExitOpt1);
      var els' := SeqCmdAndSimpleCmdOpt(elsOpt', scExitOpt2);

      (Some(SeqSimpleCmdAndCmdOpt(precedingSimple, If(optCond, thn', els'))), None)
    case Loop(invs, body) =>
      var (bodyOpt', scExitOpt) := NormalizeAst(body, None);
      var body' := SeqCmdAndSimpleCmdOpt(bodyOpt', scExitOpt);

      (Some(SeqSimpleCmdAndCmdOpt(precedingSimple, Loop(invs, body') )), None)
  }

  lemma TransformAstCorrectness<A(!new)>(a: absval_interp<A>, c: Cmd, precedingSimple: Option<SimpleCmd>, post: WpPostShallow<A>)
    requires LabelsWellDefAux(SeqSimpleCmdAndCmdOpt(precedingSimple, c), post.scopes.Keys)
    requires var (cOpt', scExitOpt):= NormalizeAst(c, precedingSimple);
             LabelsWellDefAux(SeqCmdAndSimpleCmdOpt(cOpt', scExitOpt), post.scopes.Keys)
    ensures 
      var (cOpt', scExitOpt):= NormalizeAst(c, precedingSimple);
      forall s :: WpShallow(a, SeqSimpleCmdAndCmdOpt(precedingSimple, c), post)(s) == WpShallow(a, SeqCmdAndSimpleCmdOpt(cOpt', scExitOpt), post)(s)
  {
    var (cOpt', scExitOpt):= NormalizeAst(c, precedingSimple);

    match c
    case SimpleCmd(sc) =>
    case Break(_) =>
    case Seq(c1, c2) => 
      /*
      var prefixCmd := SeqCmdOpt(c1Opt', c2Opt');
      
      (prefixCmd, scExitOpt2)
      */


      /* Case where 
          precedingSimple, cOpt1', scExitOpt1, cOpt2', scExitOpt2 are Some(precedingSimple), Some(c1'), Some(scExit1), c2', Some(scExit2) respectively
        Wp(Seq(precedingSimple, c1), post)(s) == (IH)
        Wp(Seq(c1', scExit1), post)(s) == (helper lemma)
        Wp(c1', WpShallow(a, scExit1, post))(s)

        Wp(Seq(scExit1, c2), post)(s) == (IH) 
        Wp(Seq(c2', scExit2), post)(s) == (helper lemma)
        Wp(c2', WpShallow(a, scExit2, post))(s) == (helper lemma)

        Wp(Seq(precedingSimple, Seq(c1,c2)), post)(s) == (helper lemma)
        Wp(Seq(Seq(precedingSimple, c1), c2), post)(s) == (def. Wp)
        Wp(Seq(precedingSimple, c1), Wp(c2, post))(s) == (IH --> post instantiated with Wp(c2, post))
        Wp(Seq(c1', scExit1), Wp(c2, post))(s) == (helper lemma)
        Wp(c1', Wp(Seq(scExit1, c2), post))(s) == (IH. + Wp pointwise lemma)
        Wp(c1', Wp(Seq(c2', scExit2), post))(s) ==
        Wp(Seq(Seq(c1',c2'), scExit2), post)(s)
      */

      var (c1Opt', scExitOpt1) := NormalizeAst(c1, precedingSimple);
      var (c2Opt', scExitOpt2) := NormalizeAst(c2, scExitOpt1);

      forall s | true 
        ensures WpShallow(a, SeqSimpleCmdAndCmdOpt(precedingSimple, c), post)(s) == WpShallow(a, SeqCmdAndSimpleCmdOpt(cOpt', scExitOpt), post)(s)
      {
        if precedingSimple.Some?  && c1Opt'.Some? && scExitOpt1.Some? && c2Opt'.Some? && scExitOpt2.Some? {
          var preceding := precedingSimple.value;
          var (c1', scExit1, c2', scExit2) := (c1Opt'.value, scExitOpt1.value, c2Opt'.value, scExitOpt2.value);
          var post2 := WpShallow(a, c2, post);
          calc {
            WpShallow(a, Seq(SimpleCmd(preceding), Seq(c1,c2)), post)(s); { assume false; }
            WpShallow(a, Seq(Seq(SimpleCmd(preceding), c1), c2), post)(s);
            WpShallow(a, Seq(SimpleCmd(preceding), c1), WpPostShallow(post2, post.currentScope, post.scopes))(s); //IH1
            WpShallow(a, Seq(c1', SimpleCmd(scExit1)), WpPostShallow(post2, post.currentScope, post.scopes))(s);
            WpShallow(a, c1', WpPostShallow(WpShallow(a, Seq(SimpleCmd(scExit1), c2), post), post.currentScope, post.scopes))(s); //IH2
            WpShallow(a, c1', WpPostShallow(WpShallow(a, Seq(c2', SimpleCmd(scExit2)), post), post.currentScope, post.scopes))(s);
            WpShallow(a, Seq(Seq(c1',c2'), SimpleCmd(scExit2)), post)(s);
          }
        }
      }

      /*
      forall s | true 
        ensures WpShallow(a, SeqSimpleCmdAndCmdOpt(precedingSimple, c), post)(s) == WpShallow(a, SeqCmdAndSimpleCmdOpt(cOpt', scExitOpt), post)(s)
      {
        calc {
          WpShallow(a, SeqSimpleCmdAndCmdOpt(precedingSimple, c), post)(s);
          WpShallow()
        }
      }
      */
    case If(condOpt, thn, els) =>

    case _ => assume false;
  }

}