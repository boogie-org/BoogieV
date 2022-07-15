include "../lang/BoogieLang.dfy"
include "../lang/BoogieSemantics.dfy"
include "../dafny-libraries/src/Wrappers.dfy"
include "../util/AstSubsetPredicates.dfy"
include "../util/SemanticsUtil.dfy"
include "../util/Util.dfy"


module IfGuardElim {
  import opened BoogieLang
  import opened BoogieSemantics
  import opened Wrappers
  import opened AstSubsetPredicates
  import opened SemanticsUtil
  import Util

  function method EliminateIfGuards(c: Cmd) : Cmd
    ensures NoIfGuard(EliminateIfGuards(c))
  {
    match c
    case SimpleCmd(sc) => c
    case Break(_) => c
    case Scope(optLabel, varDecls, body) =>
      var body' := EliminateIfGuards(body);
      Scope(optLabel, varDecls, body')
    case If(optGuard, thn, els) =>
      var thn' := EliminateIfGuards(thn);
      var els' := EliminateIfGuards(els);
      if optGuard.Some? then
        var guard := optGuard.value;
        assert NoIfGuard(Seq(SimpleCmd(Assume(guard)), thn'));
        assert NoIfGuard(Seq(SimpleCmd(Assume(UnOp(Not, guard))), els'));
        If(None, Seq(SimpleCmd(Assume(guard)), thn'), Seq(SimpleCmd(Assume(UnOp(Not, guard))), els'))
      else
        If(None, thn', els')
    case Loop(invs, body) =>
      var body' := EliminateIfGuards(body);
      Loop(invs, body')
    case Seq(c1, c2) =>
      var c1' := EliminateIfGuards(c1);
      var c2' := EliminateIfGuards(c2);
      Seq(c1', c2')
  }

  lemma EliminateIfGuardsNoLoops(c: Cmd)
    requires NoLoops(c) && NoBreaks(c)
    ensures NoLoops(EliminateIfGuards(c)) && NoBreaks(EliminateIfGuards(c))
  { 
    match c
    case If(optGuard, thn, els) =>
      var thn' := EliminateIfGuards(thn);
      var els' := EliminateIfGuards(els);
      if optGuard.Some? {
        var guard := optGuard.value;
        assert NoLoops(Seq(SimpleCmd(Assume(guard)), thn'));
        assert NoLoops(Seq(SimpleCmd(Assume(UnOp(Not, guard))), els'));
        assert NoBreaks(Seq(SimpleCmd(Assume(guard)), thn'));
        assert NoBreaks(Seq(SimpleCmd(Assume(UnOp(Not, guard))), els'));
      }
    case _ => 
  }

  lemma EliminateIfGuardsCorrect<A(!new)>(a: absval_interp<A>, c: Cmd, s: state<A>, post: WpPost)
  requires NoLoops(c)
  requires LabelsWellDefAux(c, post.scopes.Keys) && LabelsWellDefAux(EliminateIfGuards(c), post.scopes.Keys)
  ensures WpCmd(a, EliminateIfGuards(c), post)(s) == WpCmd(a, c, post)(s)
  {
    reveal WpCmd();
    match c
    case Seq(c1, c2) => 
      var c2Post := WpCmd(a, c2, post);
      var c2ElimPost := WpCmd(a, EliminateIfGuards(c2), post);

      forall s':state<A> | true
          ensures c2ElimPost(s') == c2Post(s')
      {
        EliminateIfGuardsCorrect(a, c2, s', post);
      }

      calc {
        WpCmd(a, EliminateIfGuards(c), post)(s);
        WpCmd(a, c1, WpPost(c2ElimPost, post.currentScope, post.scopes))(s); 
        { 
          WpCmdPointwise(a, c1, WpPost(c2ElimPost, post.currentScope, post.scopes), WpPost(c2Post, post.currentScope, post.scopes), s);
        }
        WpCmd(a, c1, WpPost(c2Post, post.currentScope, post.scopes))(s);
      }
    case If(optGuard, thn, els) =>
      var thn' := EliminateIfGuards(thn);
      var els' := EliminateIfGuards(els);

      if optGuard.Some? {
        var guard := optGuard.value;
        
        calc {
          WpCmd(a, If(Some(guard), thn, els), post)(s); 
          { WpShallowIfEquiv(a, guard, thn, els, post, s); }
          WpCmd(a, If(None, Seq(SimpleCmd(Assume(guard)), thn), Seq(SimpleCmd(Assume(UnOp(Not, guard))), els)), post)(s);
          Util.AndOpt(
            WpCmd(a, Seq(SimpleCmd(Assume(guard)), thn), post)(s),
            WpCmd(a, Seq(SimpleCmd(Assume(UnOp(Not, guard))), els), post)(s)
          );
          Util.AndOpt(
            WpCmd(a, SimpleCmd(Assume(guard)), WpPost(WpCmd(a, thn, post), post.currentScope, post.scopes))(s),
            WpCmd(a, SimpleCmd(Assume(UnOp(Not, guard))), WpPost(WpCmd(a, els, post), post.currentScope, post.scopes))(s)
          );
          { 
            forall s | true
            ensures WpCmd(a, thn, post)(s) == WpCmd(a, thn', post)(s)
            {
              EliminateIfGuardsCorrect(a, thn, s, post);
            }

            forall s | true
            ensures WpCmd(a, els, post)(s) == WpCmd(a, els', post)(s)
            {
              EliminateIfGuardsCorrect(a, els, s, post);
            }
            WpCmdPointwise2(a, SimpleCmd(Assume(guard)), WpPost(WpCmd(a, thn, post), post.currentScope, post.scopes), 
              WpPost(WpCmd(a, thn', post), post.currentScope, post.scopes));
            WpCmdPointwise2(a, SimpleCmd(Assume(guard)), WpPost(WpCmd(a, els, post), post.currentScope, post.scopes), 
              WpPost(WpCmd(a, els', post), post.currentScope, post.scopes));
          }
          Util.AndOpt(
            WpCmd(a, SimpleCmd(Assume(guard)), WpPost(WpCmd(a, thn', post), post.currentScope, post.scopes))(s),
            WpCmd(a, SimpleCmd(Assume(UnOp(Not, guard))), WpPost(WpCmd(a, els', post), post.currentScope, post.scopes))(s)
          );
        }
      }    
    case Scope(optLabel, varDecls, body) => 
      var updatedScopes := if optLabel.Some? then post.scopes[optLabel.value := post.normal] else post.scopes;
      assert updatedScopes.Keys == if optLabel.Some? then {optLabel.value} + post.scopes.Keys else post.scopes.Keys;

      var bodyPost := ResetVarsPost(varDecls, WpPost(post.normal, post.normal, updatedScopes), s);

      forall s: state<A> | true 
        ensures WpCmd(a, EliminateIfGuards(body), bodyPost)(s) == 
                WpCmd(a, body, bodyPost)(s)
      {
        calc {
          WpCmd(a, EliminateIfGuards(body), bodyPost)(s); { EliminateIfGuardsCorrect(a, body, s, bodyPost); }
          WpCmd(a, body, bodyPost)(s);
        }
      }

      ForallVarDeclsPointwise(a, varDecls, WpCmd(a, EliminateIfGuards(body), bodyPost), WpCmd(a, body, bodyPost), s);
    case _ =>  //trivial (EliminateIfGuards is the identity function here)
  }
}