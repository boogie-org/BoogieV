include "BoogieSemantics.dfy"
include "DesugarScopedVarsImpl.dfy"
include "MakeScopedVarsUniqueProof.dfy"
include "Naming.dfy"
include "ForallAppend.dfy"
include "dafny-libraries/src/Collections/Sequences/Seq.dfy"
include "dafny-libraries/src/Collections/Maps/Maps.dfy"
include "AstSubsetPredicates.dfy"

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
  import ForallAppend
  import opened AstSubsetPredicates

  predicate {:opaque} StateEqualOn<A(!new)>(s1: state<A>, s2: state<A>, xs: set<var_name>)
  {
    forall x | x in xs :: Maps.Get(s1, x) == Maps.Get(s2, x)
  }

  predicate {:opaque} PredDepend<A(!new)>(p: Predicate<A>, depVars: set<var_name>)
  {
    forall s1, s2 | 
      StateEqualOn(s1, s2, depVars) :: 
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
    requires 
     && c.WellFormedVars(activeVars)
     && NoLoopsNoIfCond(c)
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
  }


  lemma {:verify true} WpSimplePredDepend<A(!new)>(a: absval_interp<A>, xs: set<var_name>, sc: SimpleCmd, p: Predicate<A>)
    requires sc.WellFormedVars(xs)
    requires PredDepend(p, xs)
    ensures PredDepend(WpSimpleCmd(a, sc, p), xs)
  {
    reveal PredDepend();
    forall s1, s2 | StateEqualOn(s1, s2, xs)
    ensures WpSimpleCmd(a, sc, p)(s1) == WpSimpleCmd(a, sc, p)(s2)
    {
      reveal StateEqualOn();
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

  lemma ResetVarsStateAux1<A(!new)>(s1: state<A>, s2: state<A>, xs: set<var_name>, d: seq<VarDecl>, s: state<A>, s': state<A>)
  requires StateEqualOn(s1, s2, xs)
  requires StateEqualOn(s, s', xs)
  ensures StateEqualOn(ResetVarsState(d, s, s1), ResetVarsState(d, s', s2), xs)
  {
    reveal StateEqualOn();
    if |d| > 0 {
      var x := d[0].0;
      var s1' := ResetVarsState(d[1..], s, s1);
      var s2' := ResetVarsState(d[1..], s', s2);
      assert StateEqualOn(s1', s2', xs);
    }
  }

  lemma ResetVarsPredAux1<A(!new)>(s1: state<A>, s2: state<A>, xs: set<var_name>, d: seq<VarDecl>, p: Predicate<A>, s: state<A>, s': state<A>)
  requires PredDepend(p, xs)
  requires StateEqualOn(s1, s2, xs)
  requires StateEqualOn(s, s', xs)
  ensures ResetVarsPred(d, p, s1)(s) == ResetVarsPred(d, p, s2)(s')
  {
    reveal PredDepend();

    assert StateEqualOn(s, s', xs);
    if |d| > 0 {

      assert ResetVarsPred(d, p, s1)(s) == ResetVarsPred(d, p, s2)(s') by {
        calc {
          ResetVarsPred(d, p, s1)(s);
          p(ResetVarsState(d, s, s1));
          { assert StateEqualOn(ResetVarsState(d, s, s1), ResetVarsState(d, s', s2), xs) by {
              ResetVarsStateAux1(s1, s2, xs, d, s, s');
            } 
          }
          p(ResetVarsState(d, s', s2));
          ResetVarsPred(d, p, s2)(s');
        }
      }
    }
 }

  lemma ResetVarsPredAux1'<A(!new)>(s1: state<A>, s2: state<A>, xs: set<var_name>, d: seq<VarDecl>, p: Predicate<A>)
  requires PredDepend(p, xs)
  requires StateEqualOn(s1, s2, xs)
  ensures forall s: state<A> :: ResetVarsPred(d, p, s1)(s) == ResetVarsPred(d, p, s2)(s)
  {
    reveal StateEqualOn();
    forall s: state<A> | true
    { 
      ResetVarsPredAux1(s1, s2, xs, d, p, s, s);
    }
  }

  lemma ResetVarsPredAux2<A(!new)>(s: state<A>, xs: set<var_name>, d: seq<VarDecl>, p: Predicate<A>)
  requires PredDepend(p, xs)
  ensures PredDepend(ResetVarsPred(d, p, s), xs)
  {
    reveal StateEqualOn();
    forall s1, s2 | StateEqualOn(s1, s2, xs)
    ensures ResetVarsPred(d, p, s)(s1) == ResetVarsPred(d, p, s)(s2)
    {
      ResetVarsPredAux1(s, s, xs, d, p, s1, s2);
    }
    reveal PredDepend();
  }

  lemma ResetVarsPostAux1<A(!new)>(s1: state<A>, s2: state<A>, xs: set<var_name>, d: seq<VarDecl>, post: WpPost<A>)
  requires PostDepend(post, xs)
  requires StateEqualOn(s1, s2, xs)
  ensures PostPointwise(ResetVarsPost(d, post, s1), ResetVarsPost(d, post, s2))
  {
    ResetVarsPredAux1'(s1, s2, xs, d, post.normal);
    ResetVarsPredAux1'(s1, s2, xs, d, post.currentScope);
    forall l | l in post.scopes.Keys
    ensures forall s :: ResetVarsPred(d, post.scopes[l], s1)(s) == ResetVarsPred(d, post.scopes[l], s2)(s)
    { ResetVarsPredAux1'(s1, s2, xs, d, post.scopes[l]); }
  }

  lemma ResetVarsPostAux2<A(!new)>(s: state<A>, xs: set<var_name>, d: seq<VarDecl>, post: WpPost<A>)
  requires PostDepend(post, xs)
  ensures PostDepend(ResetVarsPost(d, post, s), xs)
  {
    ResetVarsPredAux2(s, xs, d, post.normal);
    ResetVarsPredAux2(s, xs, d, post.currentScope);
    forall l | l in post.scopes.Keys
    ensures PredDepend(ResetVarsPred(d, post.scopes[l], s), xs)
    { ResetVarsPredAux2(s, xs, d, post.scopes[l]); }
  }

  lemma {:verify true} WpPredDepend<A(!new)>(a: absval_interp<A>, xs: set<var_name>, c: Cmd, post: WpPost<A>)
    requires c.WellFormedVars(xs)
    requires NoLoopsNoIfCond(c)
    requires LabelsWellDefAux(c, post.scopes.Keys)
    requires PostDepend(post, xs)
    ensures PredDepend(WpCmd(a, c, post), xs)
    decreases c
  {
    match c
    case SimpleCmd(sc) => reveal WpCmd(); WpSimplePredDepend(a, xs, sc, post.normal);
    case Break(_) => reveal WpCmd();
    case Scope(optLabel, varDecls, body) => 
      var updatedScopes := 
        if optLabel.Some? then 
          post.scopes[optLabel.value := post.normal]
        else post.scopes;

      assert updatedScopes.Keys == if optLabel.Some? then {optLabel.value} + post.scopes.Keys else post.scopes.Keys;
      var post' := WpPost(post.normal, post.normal, updatedScopes);
      
      //s => ForallVarDecls( a, varDecls, WpCmd(a, body, ResetVarsPost(varDecls, post', s)) )(s)
      forall s1, s2 : state<A> | StateEqualOn(s1, s2, xs)
      ensures WpCmd(a, c, post)(s1) == WpCmd(a, c, post)(s2)
      {
        assert L1:
          ForallVarDecls( a, varDecls, WpCmd(a, body, ResetVarsPost(varDecls, post', s1)) )(s1) 
        == 
          ForallVarDecls( a, varDecls, WpCmd(a, body, ResetVarsPost(varDecls, post', s2)) )(s1) by {
            assert PostPointwise(ResetVarsPost(varDecls, post', s1), ResetVarsPost(varDecls, post', s2)) by {
              ResetVarsPostAux1(s1, s2, xs, varDecls, post');
            }

            WpCmdPointwise2(a, body, ResetVarsPost(varDecls, post', s1), ResetVarsPost(varDecls, post', s2));

            ForallVarDeclsPointwise( 
              a, 
              varDecls, 
              WpCmd(a, body, ResetVarsPost(varDecls, post', s1)), 
              WpCmd(a, body, ResetVarsPost(varDecls, post', s2)),
              s1);
          }
        
        assert L2:
          PredDepend(ForallVarDecls( a, varDecls, WpCmd(a, body, ResetVarsPost(varDecls, post', s2)) ), xs) by {
          
          assert PostDepend(ResetVarsPost(varDecls, post', s2), xs) by {
            ResetVarsPostAux2(s2, xs, varDecls, post');
          }

          assert PostDepend(ResetVarsPost(varDecls, post', s2), xs+GetVarNames(varDecls)) by {
            PostDependMonotone(ResetVarsPost(varDecls, post', s2), xs, xs+GetVarNames(varDecls));
          }
          
          WpPredDepend(a, xs+GetVarNames(varDecls), body, ResetVarsPost(varDecls, post', s2));

          ForallPredDepend(a, xs, varDecls, WpCmd(a, body, ResetVarsPost(varDecls, post', s2)));
        }

        calc {
          WpCmd(a, c, post)(s1);
          { reveal WpCmd(); }
          ForallVarDecls( a, varDecls, WpCmd(a, body, ResetVarsPost(varDecls, post', s1)) )(s1);
          { 
            reveal L1;
            reveal L2;
            reveal PredDepend();
          }
          ForallVarDecls( a, varDecls, WpCmd(a, body, ResetVarsPost(varDecls, post', s2)) )(s2);
          { reveal WpCmd(); }
          WpCmd(a, c, post)(s2);
        }
      }
      reveal PredDepend();
    case If(None, thn, els) => 
      reveal WpCmd();
      forall s1,s2 | StateEqualOn(s1, s2, xs)
      ensures WpCmd(a, c, post)(s1) == WpCmd(a, c, post)(s2)
      {
        calc {
          WpCmd(a, If(None, thn, els), post)(s1);
          Util.AndOpt(WpCmd(a, thn, post)(s1), WpCmd(a, els, post)(s1));
          { WpPredDepend(a, xs, thn, post); 
            WpPredDepend(a, xs, els, post);
            reveal PredDepend(); }
          Util.AndOpt(WpCmd(a, thn, post)(s2), WpCmd(a, els, post)(s2));
        }
      }
      reveal PredDepend();
    case Seq(c1, c2) => 
      reveal WpCmd();
      reveal PredDepend();
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
      assert PostDepend(post, activeVars+GetVarNames(decls)) by {
        PostDependMonotone(post, activeVars, activeVars+GetVarNames(decls));
      }
      WpPredDepend(a, activeVars+GetVarNames(decls), c, post);
    }

    ForallPredDepend(a, activeVars, decls, WpCmd(a, c, post));
  }

  lemma {:verify false} PullForallWp<A(!new)>(a: absval_interp<A>, xs: set<var_name>, xs1: set<var_name>, d2: seq<VarDecl>, c1: Cmd, p2: Predicate<A>, post: WpPost<A>, s: state<A>)
    requires LabelsWellDefAux(c1, post.scopes.Keys)
    requires && PostDepend(post, xs) /** needed to make sure that d2 is not captured in post */
             && xs !! GetVarNames(d2)
   // requires PredDepend(p2, xs+GetVarNames(d2))
    requires && c1.WellFormedVars(xs1) /** needed to make sure that c1 and d2 do not intefere */
             && xs1 !! GetVarNames(d2)
    ensures 
      WpCmd(a, c1, WpPost(ForallVarDecls(a, d2, p2), post.currentScope, post.scopes))(s)
    ==
      ForallVarDecls(a, d2, WpCmd(a, c1, WpPost(p2, post.currentScope, post.scopes)))(s)


  lemma HasNoDuplicatesAppend<T>(s1: seq<T>, s2: seq<T>)
  requires Sequences.HasNoDuplicates(s1+s2)
  ensures 
    && Sequences.HasNoDuplicates(s1)
    && Sequences.HasNoDuplicates(s2)
  {
    reveal Sequences.HasNoDuplicates();
    forall i, j | 0 <= i < |s1| && 0 <= j < |s1| && i != j 
    ensures s1[i] != s1[j]
    {
      assert s1[i] == (s1+s2)[i];
      assert s1[j] == (s1+s2)[j];
    }

    forall i, j | 0 <= i < |s2| && 0 <= j < |s2| && i != j 
    ensures s2[i] != s2[j]
    {
      assert s2[i] == (s1+s2)[|s1|+i];
      assert s2[j] == (s1+s2)[|s1|+j];
    }
  }

  lemma HasNoDuplicatesAppDisj(s1: seq<VarDecl>, s2: seq<VarDecl>)
  requires Sequences.HasNoDuplicates(GetVarNamesSeq(s1+s2))
  ensures GetVarNames(s1) !! GetVarNames(s2)
  {
    var s12 := GetVarNamesSeq(s1+s2);
    
    forall x | x in GetVarNames(s1)
    ensures x !in GetVarNames(s2)
    {
      var i :| 0 <= i < |s1| && s1[i].0 == x;
      assert s12[i] == x;

      forall j | 0 <= j < |s2|
      ensures x != s2[j].0
      {
        assert s12[|s1|+j] == s2[j].0;
        reveal Sequences.HasNoDuplicates();
      }
    }
  }

  lemma RemoveScopedVarsGetDecls(c: Cmd)
    requires NoLoopsNoIfCond(c)
    ensures
      var (c', decls) := RemoveScopedVars(c);
      GetDecls(c) == decls
  { }
 
  lemma {:verify true} RemoveScopedVarsCorrect<A(!new)>(a: absval_interp<A>, activeVars: set<var_name>, c: Cmd, post: WpPost<A>)
    requires 
      var (c', decls) := RemoveScopedVars(c);
      && LabelsWellDefAux(c, post.scopes.Keys) 
      && LabelsWellDefAux(c', post.scopes.Keys) 
      && c.WellFormedVars(activeVars) 
      && PostDepend(post, activeVars)
      && Sequences.HasNoDuplicates(GetVarNamesSeq(GetDecls(c)))
      && NoLoopsNoIfCond(c)
      //&& activeVars !! GetVarNames(decls)
    ensures 
      var (c', decls) := RemoveScopedVars(c);
      (forall s :: WpCmd(a, c, post)(s) == ForallVarDecls(a, decls, WpCmd(a, c', post))(s))
    {
      var (c', decls) := RemoveScopedVars(c);
      assert GetDecls(c) == decls by {
        RemoveScopedVarsGetDecls(c);
      }
      /*
      assert c'.WellFormedVars(activeVars+GetVarNames(decls)) by {
        RemoveScopedVarsPreserveWf(c, activeVars);
      }
      */

      forall s | true
      ensures 
        WpCmd(a, c, post)(s) == ForallVarDecls(a, decls, WpCmd(a, c', post))(s)
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
              assert Sequences.HasNoDuplicates(GetVarNamesSeq(GetDecls(c2))) by {
                assert GetVarNamesSeq(GetDecls(c1)+GetDecls(c2)) == GetVarNamesSeq(GetDecls(c1)) + GetVarNamesSeq(GetDecls(c2));
                HasNoDuplicatesAppend(GetVarNamesSeq(GetDecls(c1)), GetVarNamesSeq(GetDecls(c2)));
              }
              RemoveScopedVarsCorrect(a, activeVars, c2, post); 
              WpCmdPointwise(a, c1, post2, post2', s);
            }
            WpCmd(a, c1, post2')(s);
            { 
              assert PredDepend(ForallVarDecls(a, decls2, WpCmd(a, c2',post)), activeVars) by {
                ForallWpPredDepend(a, activeVars, decls2, c2', post);
              }

              assert Sequences.HasNoDuplicates(GetVarNamesSeq(GetDecls(c1))) by {
                assert GetVarNamesSeq(GetDecls(c1)+GetDecls(c2)) == GetVarNamesSeq(GetDecls(c1)) + GetVarNamesSeq(GetDecls(c2));
                HasNoDuplicatesAppend(GetVarNamesSeq(GetDecls(c1)), GetVarNamesSeq(GetDecls(c2)));
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
            { 
              assert decls1 == GetDecls(c1) && decls2 == GetDecls(c2) by {
                RemoveScopedVarsGetDecls(c1);
                RemoveScopedVarsGetDecls(c2);
              }
              
              assert GetVarNames(decls1) !! GetVarNames(decls2) by {
                HasNoDuplicatesAppDisj(decls1, decls2);
              }
              ForallAppend.ForallVarDeclsAppend(a, decls1, decls2, WpCmd(a, c1', post2NoQuant'), s); }
            ForallVarDecls(a, decls1+decls2, WpCmd(a, c1', post2NoQuant'))(s);
            { reveal WpCmd(); }
            ForallVarDecls(a, decls1+decls2, WpCmd(a, Seq(c1', c2'), post))(s);
          }
      }

      /* these reveal statements are needed due to a bug 
        (see https://github.com/dafny-lang/dafny/issues/2260) 
      */
      reveal WpCmd();
      reveal ForallVarDecls();
      
    } 
}