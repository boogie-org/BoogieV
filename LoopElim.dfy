include "BoogieLang.dfy"
include "BoogieSemantics.dfy"
include "dafny-libraries/src/Wrappers.dfy"

import opened BoogieLang
import opened BoogieSemantics
import opened Wrappers


function EliminateLoops(c: Cmd) : Cmd {
    match c
    case Scope(optLbl, varDecls, body) => Scope(optLbl, varDecls, EliminateLoops(body))
    case If(optCond, thn, els) => If(optCond, EliminateLoops(thn), EliminateLoops(els))
    case Loop(invs, body) =>
        var modDecls : seq<(var_name, Ty)> := ModifiedVars(body);
        var invsConj := NAryBinOp(And, Expr.TrueExpr, invs);

        var seqResult :=
            [ SimpleCmd(Assert(invsConj)),
              SimpleCmd(Havoc(modDecls)),
              SimpleCmd(Assume(invsConj)),
              body,
              SimpleCmd(Assert(invsConj)),
              SimpleCmd(Assume(Expr.FalseExpr))
            ];
        
        SeqToCmd(seqResult)
    case Seq(c1, c2) =>
        Seq(EliminateLoops(c1), EliminateLoops(c2))
    case _ => c
}

/** Shallow WP */

lemma EliminateLoopsCorrect<A(!new)>(a: absval_interp<A>, c: Cmd, s: state<A>, post: WpPostShallow)
requires LabelsWellDefAux(c, post.scopes.Keys) && LabelsWellDefAux(EliminateLoops(c), post.scopes.Keys)
ensures  WpShallow(a, EliminateLoops(c), post)(s) == WpShallow(a, c, post)(s)
{
    match c
    case Seq(c1, c2) => 
        var c2Post := WpShallow(a, c2, post);
        var c2ElimPost := WpShallow(a, EliminateLoops(c2), post);

        forall s':state<A> | true
            ensures c2ElimPost(s') == c2Post(s')
        {
            EliminateLoopsCorrect(a, c2, s', post);
        }

        calc {
            WpShallow(a, EliminateLoops(c), post)(s);
            WpShallow(a, c1, WpPostShallow(c2ElimPost, post.currentScope, post.scopes))(s); 
            { 
                WpShallowPointwise(a, c1, WpPostShallow(c2ElimPost, post.currentScope, post.scopes), WpPostShallow(c2Post, post.currentScope, post.scopes), s);
            }
            WpShallow(a, c1, WpPostShallow(c2Post, post.currentScope, post.scopes))(s);
        }
    case Scope(optLabel, varDecls, body) => 
      var updatedScopes := if optLabel.Some? then post.scopes[optLabel.value := post.normal] else post.scopes;
      assert updatedScopes.Keys == if optLabel.Some? then {optLabel.value} + post.scopes.Keys else post.scopes.Keys;

      var bodyPost := ResetVarsPost(a, varDecls, WpPostShallow(post.normal, post.normal, updatedScopes), s);

      forall s: state<A> | true 
        ensures WpShallow(a, EliminateLoops(body), bodyPost)(s) == 
                WpShallow(a, body, bodyPost)(s)
      {
          calc {
            WpShallow(a, EliminateLoops(body), bodyPost)(s); {EliminateLoopsCorrect(a, body, s, bodyPost); }
            WpShallow(a, body, bodyPost)(s);
          }
      }

      ForallVarDeclsPointwise(a, varDecls, WpShallow(a, EliminateLoops(body), bodyPost), WpShallow(a, body, bodyPost), s);
    case Loop(invs, body) =>
        //trivial because of how the Wp is defined

    case _ => //trivial (EliminateLoops is the identity function here)
}