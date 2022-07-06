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

  lemma {:verify false} PredDependMonotone<A(!new)>(p: Predicate<A>, depVars: set<var_name>, depVars': set<var_name>)
  requires depVars <= depVars'
  requires PredDepend(p, depVars)
  ensures PredDepend(p, depVars')
  { }

  lemma {:verify false} PostDependMonotone<A(!new)>(post: WpPost<A>, depVars: set<var_name>, depVars': set<var_name>)
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


  lemma {:verify false} WpSimplePredDepend<A(!new)>(a: absval_interp<A>, xs: set<var_name>, sc: SimpleCmd, p: Predicate<A>)
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
        ForallPredDepend(a, xs, varDecls, p);
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

  lemma {:verify false} WpPredDepend<A(!new)>(a: absval_interp<A>, xs: set<var_name>, c: Cmd, post: WpPost<A>)
    requires c.WellFormedVars(xs)
    requires LabelsWellDefAux(c, post.scopes.Keys)
    requires PostDepend(post, xs)
    ensures PredDepend(WpCmd(a, c, post), xs)
  {
    reveal WpCmd();
    match c
    case SimpleCmd(sc) => WpSimplePredDepend(a, xs, sc, post.normal);
    case Break(_) => 
    case Scope(optLabel, varDecls, body) => 

      assume false;
    case If(optCond, thn, els) => assume false;
    case Loop(invs, body) => assume false;
    case Seq(c1, c2) => assume false;
  }

  lemma {:verify false} StateUpdVarDeclsEqOutsideDecls<A>(s: state<A>, decls: seq<VarDecl>, vs: seq<Val<A>>, x: var_name)
    requires |decls| == |vs|
    requires x !in GetVarNames(decls)
    ensures Maps.Get(StateUpdVarDecls(s, decls, vs), x) == Maps.Get(s, x)
  { }

  lemma {:verify false} StateUpdVarDeclsEqOnDecls<A>(s1: state<A>, s2: state<A>, decls: seq<VarDecl>, vs: seq<Val<A>>, x: var_name)
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

  lemma {:verify false} ForallPredDepend<A(!new)>(a: absval_interp<A>, activeVars: set<var_name>, decls: seq<VarDecl>, p: Predicate<A>)
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

  lemma {:verify false} ForallWpPredDepend<A(!new)>(a: absval_interp<A>, activeVars: set<var_name>, decls: seq<VarDecl>, c: Cmd, post: WpPost<A>)
    requires c.WellFormedVars(activeVars+GetVarNames(decls))
    requires LabelsWellDefAux(c, post.scopes.Keys)
    requires PostDepend(post, activeVars)
    ensures PredDepend(ForallVarDecls(a, decls, WpCmd(a, c, post)), activeVars)
  {
    assert PredDepend(WpCmd(a, c, post), activeVars+GetVarNames(decls)) by {
      assert PostDepend(post, activeVars+GetVarNames(decls));
      WpPredDepend(a, activeVars+GetVarNames(decls), c, post);
    }

    ForallPredDepend(a, activeVars, decls, WpCmd(a, c, post));
  }

  lemma test<A(!new)>(a: absval_interp<A>, decls: seq<VarDecl>, c1: Cmd, c2: Cmd, post: WpPost<A>, s: state<A>)
    requires LabelsWellDefAux(c1, post.scopes.Keys)
    requires LabelsWellDefAux(c2, post.scopes.Keys)
    ensures 
      WpCmd(a, c1, WpPost(ForallVarDecls(a, decls, WpCmd(a, c2, post)), post.currentScope, post.scopes))(s)
    ==
      ForallVarDecls(a, decls, WpCmd(a, c1, WpPost(WpCmd(a, c2,post), post.currentScope, post.scopes)))(s)

  lemma {:verify true} RemoveScopedVarsCorrect<A(!new)>(a: absval_interp<A>, activeVars: set<var_name>, c: Cmd, post: WpPost<A>)
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
            { 
              //def. post2'
            }
            ForallVarDecls(a, decls1, WpCmd(a, c1', WpPost(ForallVarDecls(a, decls2, WpCmd(a, c2',post)), post.currentScope, post.scopes)))(s);
            { assume false; }
            ForallVarDecls(a, decls1, ForallVarDecls(a, decls2, WpCmd(a, c1', post2NoQuant')))(s);
            { ForallVarDeclsAppend(a, decls1, decls2, WpCmd(a, c1', post2NoQuant'), s); }
            ForallVarDecls(a, decls1+decls2, WpCmd(a, c1', post2NoQuant'))(s);
            { reveal WpCmd(); }
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

    lemma {:verify true} ValuesRespectDeclsSlice<A(!new)>(a: absval_interp<A>, vs: seq<Val<A>>, varDecls: seq<VarDecl>, start: nat, end: nat)
    requires ValuesRespectDecls(a, vs, varDecls)
    requires 0 <= start <= end <= |varDecls|
    ensures ValuesRespectDecls(a, vs[start..end], varDecls[start..end])
    {
      forall i | 0 <= i < |vs[start..end]|
      ensures TypeOfVal(a, vs[start..end][i]) == varDecls[start..end][i].1 {
        assert vs[start..end][i] == vs[start+i];
        assert varDecls[start..end][i] == varDecls[start+i];
        assert TypeOfValues(a, vs)[start+i] == seq(|varDecls|, i requires 0 <= i < |varDecls| => varDecls[i].1)[start+i];
        assert TypeOfVal(a, vs[start+i]) == varDecls[start+i].1;
      }
    }

    lemma SeqSliceAux<A>(s1: seq<A>, s2: seq<A>)
      requires |s1| > 0
      ensures (s1+s2)[1..] == s1[1..]+s2
    { }

    lemma StateUpdVarDeclsSplit2<A(!new)>(s: state<A>, d1: seq<VarDecl>, d2: seq<VarDecl>, vs1: seq<Val<A>>, vs2: seq<Val<A>>)
      requires |d1| == |vs1| && |d2| == |vs2|
      ensures StateUpdVarDecls(s, d1+d2, vs1+vs2) == StateUpdVarDecls(StateUpdVarDecls(s, d1, vs1), d2, vs2)

    lemma StateUpdVarDeclsSplit<A(!new)>(s: state<A>, d1: seq<VarDecl>, d2: seq<VarDecl>, vs1: seq<Val<A>>, vs2: seq<Val<A>>)
      requires |d1| == |vs1| && |d2| == |vs2|
      ensures StateUpdVarDecls(s, d1+d2, vs1+vs2) == StateUpdVarDecls(StateUpdVarDecls(s, d2, vs2), d1, vs1)
    {
      if |d1| == 0 {
        calc {
          StateUpdVarDecls(s, d1+d2, vs1+vs2);
          { 
            assert d1+d2 == d2;
            assert vs1+vs2 == vs2;
          }
          StateUpdVarDecls(s, d2, vs2);
          StateUpdVarDecls(StateUpdVarDecls(s, d2, vs2), d1, vs1);
        }
      } else {
        var x := d1[0].0;
        var v := vs1[0];
        assert (d1+d2)[0].0 == x;
        assert (vs1+vs2)[0] == v;

        var sA := StateUpdVarDecls(s, (d1+d2)[1..], (vs1+vs2)[1..]);
        var sB := StateUpdVarDecls(StateUpdVarDecls(s, d2, vs2), d1[1..], vs1[1..]);

        assert sA == sB by {
          assert StateUpdVarDecls(s, d1[1..]+d2, vs1[1..]+vs2) == StateUpdVarDecls(StateUpdVarDecls(s, d2, vs2), d1[1..], vs1[1..]) by {
            StateUpdVarDeclsSplit(s, d1[1..], d2, vs1[1..], vs2);
          }
          assert (d1+d2)[1..] == d1[1..]+d2 by {
            SeqSliceAux(d1, d2); //DISCUSS (why can't Dafny prove the assertion without the helper lemma?)
          }
          assert (vs1+vs2)[1..] == vs1[1..]+vs2 by {
            SeqSliceAux(vs1, vs2);
          }
        }

        assert sA[x := v] == sB[x := v];

        assert StateUpdVarDecls(s, d1+d2, vs1+vs2) == sA[x := v];
        assert StateUpdVarDecls(StateUpdVarDecls(s, d2, vs2), d1, vs1) == sB[x := v];
      }
    }

    
    lemma {:verify false} ForallVarDeclsAppend<A(!new)>(
      a: absval_interp<A>, 
      varDecls1: seq<(var_name, Ty)>, 
      varDecls2: seq<(var_name, Ty)>, 
      p: Predicate<A>,
      s: state<A>)
    ensures    ForallVarDecls(a, varDecls1, ForallVarDecls(a, varDecls2, p))(s)
            == ForallVarDecls(a, varDecls1+varDecls2, p)(s);
    {
      var varDecls := varDecls1+varDecls2;
      if |varDecls2| == 0 {
        calc {
          ForallVarDecls(a, varDecls1, ForallVarDecls(a, varDecls2, p))(s);
          { reveal ForallVarDecls(); }
          ForallVarDecls(a, varDecls1, p)(s);
          { assert varDecls1 == varDecls; }
          ForallVarDecls(a, varDecls, p)(s);
        }
      } else {
        if ForallVarDecls(a, varDecls, p)(s) == None {
          NoneForallVarDecls(a, varDecls, p, s);
          var vs :| (ValuesRespectDecls(a, vs, varDecls) && p(StateUpdVarDecls(s, varDecls, vs)) == None);

          assert |vs| == |varDecls|;
          var vs1 := vs[0..|varDecls1|];
          var vs2 := vs[|varDecls1|..|varDecls|];

          assert vs1+vs2 == vs;

          assert varDecls1 == varDecls[0..|varDecls1|];
          assert varDecls2 == varDecls[|varDecls1|..|varDecls|];

          assert ValuesRespectDecls(a, vs1, varDecls1) by {
            ValuesRespectDeclsSlice(a, vs, varDecls, 0, |varDecls1|);
          }
          assert ValuesRespectDecls(a, vs2, varDecls2) by {
            ValuesRespectDeclsSlice(a, vs, varDecls, |varDecls1|, |varDecls|);
          }

          var s1 := StateUpdVarDecls(s, varDecls1, vs1);
          assume StateUpdVarDecls(s, varDecls, vs) == StateUpdVarDecls(StateUpdVarDecls(s, varDecls1, vs1), varDecls2, vs2);
          //TODO: need to rephrase StateUpdVarDecls?


          assert ForallVarDecls(a, varDecls1, ForallVarDecls(a, varDecls2, p))(s) == None by {
            assert ForallVarDecls(a, varDecls2, p)(s1) == None by {
              assert p(StateUpdVarDecls(s1, varDecls2, vs2)) == None;
              NoneForallVarDecls2(a, varDecls2, vs2, p, s1);
            }


            if |varDecls1| == 0 {
              reveal ForallVarDecls();
            } else {
              NoneForallVarDecls2(a, varDecls1, vs1, ForallVarDecls(a, varDecls2, p), s);
            }
          }
        } else {
          assume false;
        }
      }
    }
}