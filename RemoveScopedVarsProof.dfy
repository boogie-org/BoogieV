include "BoogieSemantics.dfy"
include "DesugarScopedVarsImpl.dfy"
include "MakeScopedVarsUniqueProof.dfy"
include "Naming.dfy"
include "dafny-libraries/src/Collections/Sequences/Seq.dfy"
include "dafny-libraries/src/Collections/Maps/Maps.dfy"

module RemoveScopedVarsUniqueProof {

  import opened BoogieLang
  import opened BoogieSemantics
  import Sequences = Seq
  import Maps
  import Util
  import opened Wrappers
  import opened DesugarScopedVarsImpl
  import MakeScopedVarsUniqueProof
  import opened Naming

  predicate PredDepend<A(!new)>(p: Predicate<A>, depVars: set<var_name>)
  {
    forall s1, s2 | 
      (forall x | x in depVars :: Maps.Get(s1, x) == Maps.Get(s2, x)) :: 
      p(s1) == p(s2)
  }

  predicate PostDepend<A(!new)>(post: WpPost<A>, depVars: set<var_name>)
  {
    && PredDepend(post.normal, depVars)
    && PredDepend(post.currentScope, depVars)
    && (forall lbl | lbl in post.scopes.Keys :: PredDepend(post.scopes[lbl], depVars))
  }

  lemma PredDependMonotone<A(!new)>(p: Predicate<A>, depVars: set<var_name>, depVars': set<var_name>)
  requires depVars <= depVars'
  requires PredDepend(p, depVars)
  ensures PredDepend(p, depVars')
  { }

  lemma PostDependMonotone<A(!new)>(post: WpPost<A>, depVars: set<var_name>, depVars': set<var_name>)
  requires depVars <= depVars'
  requires PostDepend(post, depVars)
  ensures PostDepend(post, depVars')
  { }

  lemma {:verify false} RemoveScopedVarsPreserveWf(c: Cmd, activeVars: set<var_name>)
    requires c.WellFormedVars(activeVars)
    ensures 
      var (c', decls) := RemoveScopedVars(c);
      c'.WellFormedVars(activeVars+GetVarNames(decls))
  {
    var (c', decls) := RemoveScopedVars(c);
    match c
    case SimpleCmd(sc) => SimpleCmdWellFormedVarsLarger(sc, activeVars, activeVars+GetVarNames(decls));
    case Break(_) => 
    case Scope(optLabel, varDecls, body) => 
      var (body', declsBody) := RemoveScopedVars(body);
      assert body'.WellFormedVars((activeVars+GetVarNames(varDecls))+GetVarNames(declsBody)) by {
        RemoveScopedVarsPreserveWf(body, activeVars+GetVarNames(varDecls));
      }

      calc {
        (activeVars+GetVarNames(varDecls))+GetVarNames(declsBody);
        activeVars+(GetVarNames(varDecls)+GetVarNames(declsBody));
        activeVars+GetVarNames(varDecls+declsBody);
      }

      assert body'.WellFormedVars(activeVars+GetVarNames(varDecls+declsBody));

      calc {
        c'.WellFormedVars(activeVars+GetVarNames(decls));
        body'.WellFormedVars((activeVars+GetVarNames(varDecls+declsBody))+GetVarNames([]));
        { assert GetVarNames([]) == {}; }
        body'.WellFormedVars((activeVars+GetVarNames(varDecls+declsBody))+{});
        { assert (activeVars+GetVarNames(varDecls+declsBody))+{} == activeVars+GetVarNames(varDecls+declsBody); }
        body'.WellFormedVars(activeVars+GetVarNames(varDecls+declsBody));
      }
    case If(None, thn, els) => 
      var (thn', declsThn) := RemoveScopedVars(thn);
      var (els', declsEls) := RemoveScopedVars(els);

      assert 
        && thn'.WellFormedVars(activeVars+GetVarNames(declsThn))
        && els'.WellFormedVars(activeVars+GetVarNames(declsEls));

      assert GetVarNames(decls) == GetVarNames(declsThn)+GetVarNames(declsEls);

      CmdWellFormedVarsLarger(thn', activeVars+GetVarNames(declsThn), activeVars+GetVarNames(decls));
      CmdWellFormedVarsLarger(els', activeVars+GetVarNames(declsEls), activeVars+GetVarNames(decls));
    case Seq(c1, c2) =>
      var (c1', decls1) := RemoveScopedVars(c1);
      var (c2', decls2) := RemoveScopedVars(c2);

      CmdWellFormedVarsLarger(c1', activeVars+GetVarNames(decls1), activeVars+GetVarNames(decls));
      CmdWellFormedVarsLarger(c2', activeVars+GetVarNames(decls2), activeVars+GetVarNames(decls));
    case _ => assume false;
  }


  lemma WpSimplePredDepend<A(!new)>(a: absval_interp<A>, xs: set<var_name>, sc: SimpleCmd, p: Predicate<A>)
    requires sc.WellFormedVars(xs)
    requires PredDepend(p, xs)
    ensures PredDepend(WpSimpleCmd(a, sc, p), xs)
  {
    forall s1, s2 | (forall x | x in xs :: Maps.Get(s1, x) == Maps.Get(s2, x))
    ensures WpSimpleCmd(a, sc, p)(s1) == WpSimpleCmd(a, sc, p)(s2)
    {
      match sc
      case Skip =>
      case Assert(e) =>
        assert EvalExpr(a, e, s1) == EvalExpr(a, e, s2) by {
          EvalExprFreeVarEq(a, e, s1, s2);
        }
      case Assume(e) =>
        assert EvalExpr(a, e, s1) == EvalExpr(a, e, s2) by {
          EvalExprFreeVarEq(a, e, s1, s2);
        }
      case Assign(x, t, e) =>
        assert EvalExpr(a, e, s1) == EvalExpr(a, e, s2) by {
          EvalExprFreeVarEq(a, e, s1, s2);
        }
      case Havoc(varDecls) => 

      case SeqSimple(sc1, sc2) => 
        calc {
          WpSimpleCmd(a, SeqSimple(sc1, sc2), p)(s1);
          WpSimpleCmd(a, sc1, WpSimpleCmd(a, sc2, p))(s1);
          { assert PredDepend(WpSimpleCmd(a, sc2, p), xs) by {
              WpSimplePredDepend(a, xs, sc2, p);
            }
            WpSimplePredDepend(a, xs, sc1, WpSimpleCmd(a, sc2, p));
          }
          WpSimpleCmd(a, sc1, WpSimpleCmd(a, sc2, p))(s2);
        }
    }
  }

  lemma WpPredDepend<A(!new)>(a: absval_interp<A>, xs: set<var_name>, c: Cmd, post: WpPost<A>)
    requires c.WellFormedVars(xs)
    requires LabelsWellDefAux(c, post.scopes.Keys)
    requires PostDepend(post, xs)
    ensures PredDepend(WpCmd(a, c, post), xs)
  {
    match c
    case SimpleCmd(sc) => assume false;
    case Break(_) => reveal WpCmd();
    case Scope(_, varDecls, body) => assume false;
    case If(optCond, thn, els) => assume false;
    case Loop(invs, body) => assume false;
    case Seq(c1, c2) => assume false;
  }

  lemma StateUpdVarDeclsEqOutsideDecls<A>(s: state<A>, decls: seq<VarDecl>, vs: seq<Val<A>>, x: var_name)
    requires |decls| == |vs|
    requires x !in GetVarNames(decls)
    ensures Maps.Get(StateUpdVarDecls(s, decls, vs), x) == Maps.Get(s, x)
  { }

  lemma StateUpdVarDeclsEqOnDecls<A>(s1: state<A>, s2: state<A>, decls: seq<VarDecl>, vs: seq<Val<A>>, x: var_name)
    requires |decls| == |vs|
    requires x in GetVarNames(decls)
    ensures  Maps.Get(StateUpdVarDecls(s1, decls, vs), x) == Maps.Get(StateUpdVarDecls(s2, decls, vs), x)
  {
    if |decls| > 0 {
      var y := decls[0].0;

      if x != y {
        var s1' := StateUpdVarDecls(s1, decls[1..], vs[1..]);
        var s2' := StateUpdVarDecls(s2, decls[1..], vs[1..]);

        assert Maps.Get(s1', x) == Maps.Get(s2', x) by {
          StateUpdVarDeclsEqOnDecls(s1, s2, decls[1..], vs[1..], x);
        }
      }
    }
  }

  lemma ForallPredDepend<A(!new)>(a: absval_interp<A>, activeVars: set<var_name>, decls: seq<VarDecl>, p: Predicate<A>)
    requires PredDepend(p, activeVars+GetVarNames(decls))
    ensures PredDepend(ForallVarDecls(a, decls, p), activeVars)
  {
    if |decls| == 0 {
      reveal ForallVarDecls();
    } else {
      forall s1,s2: state<A> | (forall x | x in activeVars :: Maps.Get(s1, x) == Maps.Get(s2, x))
      ensures ForallVarDecls(a, decls, p)(s1) == ForallVarDecls(a, decls, p)(s2)
      {
         forall vs | ValuesRespectDecls(a, vs, decls)
         ensures p(StateUpdVarDecls(s1, decls, vs)) == p(StateUpdVarDecls(s2, decls, vs))
         {
           var s1' := StateUpdVarDecls(s1, decls, vs);
           var s2' := StateUpdVarDecls(s2, decls, vs);

           forall x | x in activeVars + GetVarNames(decls) 
           ensures Maps.Get(s1', x) == Maps.Get(s2', x)
           {
            if x in GetVarNames(decls) {
              StateUpdVarDeclsEqOnDecls(s1, s2, decls, vs, x);
            } else {
              assert x in activeVars && x !in GetVarNames(decls);
              StateUpdVarDeclsEqOutsideDecls(s1, decls, vs, x);
              StateUpdVarDeclsEqOutsideDecls(s2, decls, vs, x);
            }
           }
         }

         ForallVarDeclsEquiv(a, decls, decls, p, p, s1, s2);
      }
    }
  }

  lemma ForallWpPredDepend<A(!new)>(a: absval_interp<A>, activeVars: set<var_name>, decls: seq<VarDecl>, c: Cmd, post: WpPost<A>)
    requires c.WellFormedVars(activeVars+GetVarNames(decls))
    requires LabelsWellDefAux(c, post.scopes.Keys)
    requires PostDepend(post, activeVars)
    ensures PredDepend(ForallVarDecls(a, decls, WpCmd(a, c, post)), activeVars)
  {
    assert PredDepend(WpCmd(a, c, post), activeVars+GetVarNames(decls)) by {
      assert PostDepend(post, activeVars+GetVarNames(decls)) by {
        PostDependMonotone(post, activeVars, activeVars+GetVarNames(decls));
      }
      WpPredDepend(a, activeVars+GetVarNames(decls), c, post);
    }

    ForallPredDepend(a, activeVars, decls, WpCmd(a, c, post));
  }

  lemma RemoveScopedVarsCorrect<A(!new)>(a: absval_interp<A>, activeVars: set<var_name>, c: Cmd, post: WpPost<A>)
    requires 
      var (c', decls) := RemoveScopedVars(c);
      && LabelsWellDefAux(c, post.scopes.Keys) 
      && LabelsWellDefAux(c', post.scopes.Keys) 
      && c.WellFormedVars(activeVars) 
      && PostDepend(post, activeVars)
      //&& activeVars !! GetVarNames(decls)
    ensures 
      var (c', decls) := RemoveScopedVars(c);
      forall s :: WpCmd(a, c, post)(s) == ForallVarDecls(a, decls, WpCmd(a, c', post))(s)
    {
      var (c', decls) := RemoveScopedVars(c);
      assert c'.WellFormedVars(activeVars+GetVarNames(decls)) by {
        RemoveScopedVarsPreserveWf(c, activeVars);
      }

      forall s | true
      ensures WpCmd(a, c, post)(s) == ForallVarDecls(a, decls, WpCmd(a, c', post))(s)
      {
        match c 
        case SimpleCmd(sc) => ForallVarDeclsEmpty(a, WpCmd(a, c', post)); 
        case Break(_) => ForallVarDeclsEmpty(a, WpCmd(a, c', post)); 
        case Scope(_, varDecls, body) => assume false;
        case If(None, thn, els) => assume false;
        case Seq(c1, c2) => 
          // WpPost(WpCmd(a, c2, post), post.currentScope, post.scopes)
          var (c1', decls1) := RemoveScopedVars(c1);
          var (c2', decls2) := RemoveScopedVars(c2);

          var post2 := WpPost(WpCmd(a, c2, post), post.currentScope, post.scopes);
          var post2' := WpPost(ForallVarDecls(a, decls2, WpCmd(a, c2',post)), post.currentScope, post.scopes);
          var post2NoQuant' := WpPost(WpCmd(a, c2',post), post.currentScope, post.scopes);

          assert c2'.WellFormedVars(activeVars+GetVarNames(decls2)) by {
            RemoveScopedVarsPreserveWf(c2, activeVars);
          }

          calc {
            WpCmd(a, Seq(c1, c2), post)(s);
            { reveal WpCmd(); }
            WpCmd(a, c1, post2)(s);
            { 
              RemoveScopedVarsCorrect(a, activeVars, c2, post); 
              WpCmdPointwise(a, c1, post2, post2', s);
            }
            WpCmd(a, c1, post2')(s);
            { 
              assert PredDepend(ForallVarDecls(a, decls2, WpCmd(a, c2',post)), activeVars) by {
                ForallWpPredDepend(a, activeVars, decls2, c2', post);
              }
              RemoveScopedVarsCorrect(a, activeVars, c1, post2'); 

              //reveal due to opaque bug
              reveal WpCmd();
              reveal ForallVarDecls();
            }
            ForallVarDecls(a, decls1, WpCmd(a, c1', post2'))(s);
            { assume false; }
            ForallVarDecls(a, decls1, ForallVarDecls(a, decls2, WpCmd(a, c1', post2NoQuant')))(s);
            { assume false; }
            ForallVarDecls(a, decls1+decls2, WpCmd(a, c1', post2NoQuant'))(s);
            { assume false; }
            ForallVarDecls(a, decls1+decls2, WpCmd(a, Seq(c1', c2'), post))(s);
          }
        case _ => assume false;
      }

      /* these reveal statements are needed due to a bug 
        (see https://github.com/dafny-lang/dafny/issues/2260) 
      */
      reveal WpCmd();
      reveal ForallVarDecls();
      
    } 
}