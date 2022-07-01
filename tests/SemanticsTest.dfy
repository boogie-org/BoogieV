include "../BoogieSemantics.dfy"
include "../BoogieLang.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"

module SemanticsTest {
  import opened BoogieLang
  import opened BoogieSemantics
  import opened Wrappers
  import opened Util

  const innerBody : Cmd := Break(Some("A"));

  const scopeInner : Cmd :=
    Scope(None, [("x", TPrim (TInt))], innerBody);

  const scopeMiddle : Cmd :=
    Scope(Some("A"), [("x", TPrim (TInt))], scopeInner);

  const cond: Expr := BinOp(Var("x"), Eq, ELit(LitInt(0)));

  const outerBody: Cmd := 
      Seq(
          SimpleCmd(Assume(cond)), 
          Seq(scopeMiddle, SimpleCmd(Assert(cond)))
      );

  const scopeOuter : Cmd := 
    Scope(None, [("x", TPrim (TInt))], outerBody);
  
  /** 
    Scope {
      var x: int;
      assume x == 0;
      Scope A {
        var x: int;
        Scope {
          var x: int;
          break A;
        }
      }
      assert x == 0;
    }
   */


  function TruePred<A>() : Predicate<A> {
    s => Some(true)
  }

  function TruePost<A>() : WpPostShallow<A> {
    WpPostShallow(TruePred(), TruePred(), map[])
  }


  lemma LabelsWellDefScopeOuter()
    ensures LabelsWellDefAux(scopeOuter, {})
  {
    calc {
      LabelsWellDefAux(scopeOuter, {});
      { assert {"A"}+{} == {"A"}; }
      LabelsWellDefAux(scopeMiddle, {"A"});
    }
  }

  lemma ScopeOuterTest<A(!new)>(a: absval_interp<A>, s: state<A>)
    requires LabelsWellDefAux(scopeOuter, TruePost<A>().scopes.Keys)
    requires WpShallow(a, scopeOuter, TruePost())(s) != None //"well-typed"
    ensures WpShallow(a, scopeOuter, TruePost())(s) == Some(true)
  {
    var decls := [("x", TPrim (TInt))];
    var post := TruePost<A>();
    var postOuter := WpPostShallow(post.normal, post.normal, post.scopes);


    var p1 := WpShallow(a, outerBody, ResetVarsPost(decls, postOuter, s));
    calc {
      WpShallow(a, scopeOuter, TruePost())(s);
      { reveal WpShallow(); }
      ForallVarDeclsShallow( a, decls, p1 )(s);
    }

    calc {
      ForallVarDeclsShallow( a, decls, p1 )(s);
      { 
        SomeForallVarDeclsShallow(a, decls, p1, s);
      }
      Some(forall vs | ValuesRespectDecls(a, vs, decls) :: p1(StateUpdVarDecls(s, decls, vs)) == Some(true));
    }

    forall vs | ValuesRespectDecls(a, vs, decls)
    ensures p1(StateUpdVarDecls(s, decls, vs)) == Some(true)
    {
      var s' := StateUpdVarDecls(s, decls, vs);

      assert |vs| == |decls| == 1;

      assert s' == s["x" := vs[0]] by {
        calc {
          StateUpdVarDecls(s, decls, vs);
          StateUpdVarDecls(s, decls[1..], vs[1..])["x" := vs[0]];
          StateUpdVarDecls(s, [], [])["x" := vs[0]];
          s["x" := vs[0]];
        }
      }

      assert p1(s') != None by {
        SomeForallVarDeclsShallow2(a, decls, p1, s, vs);
      }

    var postOuter' := ResetVarsPost(decls, postOuter, s);
      calc {
        p1(s');
        WpShallow(a, outerBody, postOuter')(s');
        { reveal WpShallow(); }
        WpShallowSimpleCmd(a, Assume(cond), WpShallow(a, Seq(scopeMiddle, SimpleCmd(Assert(cond))), postOuter'))(s');
      }

      var vCond := ExprEvalBoolOpt(a, cond, s').value; //we know it is not None since p1(s') != None

      var postMiddle := WpPostShallow(WpShallow(a, SimpleCmd(Assert(cond)), postOuter'), postOuter'.currentScope, postOuter'.scopes);

      assert postOuter'.scopes["A" := post.normal].Keys == {"A"} + postOuter'.scopes.Keys; 

      if vCond {

        var postMiddle' := WpPostShallow(postMiddle.normal, postMiddle.normal, postOuter'.scopes["A" := postMiddle.normal]);

        var p2 := WpShallow(a, scopeInner, ResetVarsPost(decls, postMiddle', s'));

        calc {
          WpShallow(a, Seq(scopeMiddle, SimpleCmd(Assert(cond))), postOuter')(s');
          { reveal WpShallow(); }
          WpShallow(a, scopeMiddle, postMiddle)(s');
          { reveal WpShallow(); }
          ForallVarDeclsShallow( a, decls, p2 )(s');
        }

        calc {
          ForallVarDeclsShallow( a, decls, p2 )(s');
          { 
            SomeForallVarDeclsShallow(a, decls, p2, s');
          }
          Some(forall vs | ValuesRespectDecls(a, vs, decls) :: p2(StateUpdVarDecls(s', decls, vs)) == Some(true));
        }

        forall vs | ValuesRespectDecls(a, vs, decls)
        ensures p2(StateUpdVarDecls(s', decls, vs)) == Some(true)
        {
          var s'' := StateUpdVarDecls(s', decls, vs); 

          assert p2(s'') != None by {
            SomeForallVarDeclsShallow2(a, decls, p2, s', vs);
          }

          var postMiddle'' := ResetVarsPost(decls, postMiddle', s');
          var postInner := WpPostShallow(postMiddle''.normal, postMiddle''.normal, postMiddle''.scopes);
          
          var p3 := WpShallow(a, innerBody, ResetVarsPost(decls, postInner, s''));

          calc {
            p2(s'');
            WpShallow(a, scopeInner, postMiddle'')(s'');
            { reveal WpShallow(); }
            ForallVarDeclsShallow(a, decls, p3)(s'');
          }

          calc {
            ForallVarDeclsShallow( a, decls, p3 )(s'');
            { 
              SomeForallVarDeclsShallow(a, decls, p3, s'');
            }
            Some(forall vs | ValuesRespectDecls(a, vs, decls) :: p3(StateUpdVarDecls(s'', decls, vs)) == Some(true));
          }

          forall vs | ValuesRespectDecls(a, vs, decls)
          ensures p3(StateUpdVarDecls(s'', decls, vs)) == Some(true)
          {
            var s3 := StateUpdVarDecls(s'', decls, vs); 

            assert p3(s3) != None by {
              SomeForallVarDeclsShallow2(a, decls, p3, s'', vs);
            }

            calc {
              p3(s3);
              WpShallow(a, Break(Some("A")), ResetVarsPost(decls, postInner, s''))(s3);
              { reveal WpShallow(); } //TODO: slow, find way to speed up
              ResetVarsPost(decls, postInner, s'').scopes["A"](s3);
              ResetVarsPred(decls, postInner.scopes["A"], s'')(s3);
              ResetVarsPred(decls, postMiddle''.scopes["A"], s'')(s3);
              ResetVarsPred(decls, ResetVarsPost(decls, postMiddle', s').scopes["A"], s'')(s3);
              ResetVarsPred(decls, ResetVarsPred(decls, postMiddle.normal, s'), s'')(s3);
              ResetVarsPred(decls, ResetVarsPred(decls, WpShallow(a, SimpleCmd(Assert(cond)), postOuter'), s'), s'')(s3);
            }

            calc {
              ResetVarsPred(decls, ResetVarsPred(decls, WpShallow(a, SimpleCmd(Assert(cond)), postOuter'), s'), s'')(s3);
              ResetVarsPred(decls, WpShallow(a, SimpleCmd(Assert(cond)), postOuter'), s')(ResetVarsState(decls, s3, s''));
              WpShallow(a, SimpleCmd(Assert(cond)), postOuter')(ResetVarsState(decls, ResetVarsState(decls, s3, s''), s'));
            }

            var sInput := ResetVarsState(decls, ResetVarsState(decls, s3, s''), s');

            assert "x" in sInput.Keys;

            assert sInput["x"] == s'["x"];

            var resLeft := EvalExpr(a, Var("x"), sInput).value;
            var resRight := EvalExpr(a, ELit(LitInt(0)), sInput).value;

            assert resLeft == s'["x"];
            assert resRight == LitV(LitInt(0));

            var res := ExprEvalBoolOpt(a, cond, sInput).value;

            calc {
              ExprEvalBoolOpt(a, cond, sInput).value;
              resLeft == resRight;
              s'["x"] == LitV(LitInt(0));
              EvalExpr(a, Var("x"), s').value == EvalExpr(a, ELit(LitInt(0)), s').value;
              ExprEvalBoolOpt(a, cond, s').value;
              true;
            }

            assert ExprEvalBoolOpt(a, cond, sInput).value;

            var resOuter := postOuter'.normal(sInput);

            calc {
              WpShallow(a, SimpleCmd(Assert(cond)), postOuter')(sInput);
              { reveal WpShallow(); }
              WpShallowSimpleCmd(a, Assert(cond), postOuter'.normal)(sInput);
              postOuter'.normal(sInput);
              ResetVarsPred(decls, post.normal, s)(sInput);
              post.normal(ResetVarsState(decls, sInput, s));
              Some(true);
            }
          }
        }
      }
    }
  }
}

