include "../lang/BoogieSemantics.dfy"
include "../transformations/DesugarScopedVarsImpl.dfy"
include "../util/Naming.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"
include "../dafny-libraries/src/Collections/Maps/Maps.dfy"
include "../util/AstSubsetPredicates.dfy"

module MakeScopedVarsUniqueProof {

  import opened BoogieLang
  import opened BoogieSemantics
  import Sequences = Seq
  import Maps
  import Util
  import opened Wrappers
  import opened DesugarScopedVarsImpl
  import opened Naming
  import opened AstSubsetPredicates

  type MapOrig<V> = map<var_name, Option<V>>

  lemma UnionOfInjectiveMaps<K,V>(m1: map<K,V>, m2: map<K,V>)
    requires 
      && Maps.Injective(m1)
      && Maps.Injective(m2)
      && m1.Values !! m2.Values
    ensures Maps.Injective(m1 + m2)
  {
    var m := m1 + m2;
    reveal Maps.Injective();

    forall x, x' | x != x' && x in m && x' in m
    ensures m[x] != m[x']
    {
      if x in m2.Keys && x' in m2.Keys {
        // conclusion follows from Maps.Injective(m1)
      } else if x !in m2.Keys && x' !in m2.Keys {
        // conclusion follows from Maps.Injective(m2)
      } else {
        var y1 := if x in m2.Keys then x' else x;
        var y2 := if x in m2.Keys then x else x';

        assert m[y1] != m[y2] by {
          assert m[y1] == m1[y1];
          assert m[y2] == m2[y2];
          assert m1[y1] in m1.Values;
          assert m2[y2] in m2.Values;
        }
      }
    }
  }

  predicate {:opaque} RelState<V>(m: map<var_name, var_name>, s1: map<var_name, V>, s2: map<var_name, V>, s2Orig: map<var_name, Option<V>>)
  {
    && (forall k | k in m.Keys :: Maps.Get(s1, k) == Maps.Get(s2, m[k]))
    && (forall k | k in s2Orig.Keys :: Maps.Get(s2, k) == s2Orig[k])
    && m.Values !! s2Orig.Keys
  }

  predicate {:opaque} RelPred<A(!new)>(m: map<var_name, var_name>, post1: Predicate<A>, post2: Predicate<A>, s2Orig: MapOrig<Val<A>>)
  {
    forall s, s' | RelState(m, s, s', s2Orig) :: post1(s) == post2(s')
  }

  lemma RelStateUpdPreserve<V>(varMapping: map<var_name, var_name>, s1: map<var_name, V>, s2: map<var_name, V>, s2Orig: MapOrig<V>, x: var_name, v: V)
  requires RelState(varMapping, s1, s2, s2Orig)
  requires Maps.Injective(varMapping)
  requires x in varMapping.Keys
  ensures RelState(varMapping, s1[x := v], s2[varMapping[x] := v], s2Orig)
  {
    reveal RelState();
    var x' := varMapping[x];
    forall k | k in varMapping.Keys 
    ensures Maps.Get(s1[x := v], k) == Maps.Get(s2[varMapping[x] := v], varMapping[k])
    {
      var k' := varMapping[k];
      if k != x {
        calc {
          Maps.Get(s1[x := v], k);
          Maps.Get(s1, k);
          Maps.Get(s2, k');
          { reveal Maps.Injective(); }
          Maps.Get(s2[x' := v], k');
        }
      }
    }
  }

  lemma RelStateUpdVarDeclsPreserve<A>(
      varMapping: map<var_name, var_name>, 
      s1: state<A>,
      s2: state<A>, 
      s2Orig: MapOrig<Val<A>>, 
      varDecls: seq<VarDecl>, 
      varDecls': seq<VarDecl>,
      vs: seq<Val<A>>)
  requires RelState(varMapping, s1, s2, s2Orig)
  requires Maps.Injective(varMapping)
  requires GetVarNames(varDecls) <= varMapping.Keys
  requires |vs| == |varDecls| == |varDecls'|
  requires (forall i | 0 <= i < |varDecls| :: varDecls'[i].0 == varMapping[varDecls[i].0])
  ensures RelState(varMapping, StateUpdVarDecls(s1, varDecls, vs), StateUpdVarDecls(s2, varDecls', vs), s2Orig)
  {
    if |varDecls| > 0 {       
        var s1' := StateUpdVarDecls(s1, varDecls[1..], vs[1..]);
        var s2' := StateUpdVarDecls(s2, varDecls'[1..], vs[1..]);

        assert RelState(varMapping, s1', s2', s2Orig) by {
          RelStateUpdVarDeclsPreserve(varMapping, s1, s2, s2Orig, varDecls[1..], varDecls'[1..], vs[1..]);
        }

        RelStateUpdPreserve(varMapping, s1', s2', s2Orig, varDecls[0].0, vs[0]);
    }
  }

  lemma ForallVarDeclRel<A(!new)>(
      a: absval_interp<A>, 
      varDecls: seq<(var_name, Ty)>, 
      varMapping: map<var_name, var_name>, 
      p1: Predicate<A>,
      p2: Predicate<A>,
      s2Orig: MapOrig<Val<A>>)
      requires RelPred(varMapping, p1, p2, s2Orig)
      requires GetVarNames(varDecls) <= varMapping.Keys
      requires Maps.Injective(varMapping)
      ensures 
        var f := (vDecl : (var_name, Ty)) => 
            if vDecl.0 in varMapping.Keys then (varMapping[vDecl.0], vDecl.1) else vDecl;
        var varDecls' := Sequences.Map(f, varDecls);
        RelPred(varMapping, ForallVarDecls(a, varDecls, p1), ForallVarDecls(a, varDecls', p2), s2Orig)
    {
      var f := (vDecl : (var_name, Ty)) => 
          if vDecl.0 in varMapping.Keys then (varMapping[vDecl.0], vDecl.1) else vDecl;
      var varDecls' := Sequences.Map(f, varDecls);
      if |varDecls| == 0 {
        //trivial
        reveal ForallVarDecls();
        assert ForallVarDecls(a, varDecls, p1) == p1;
      } else {
        var (x,t) := varDecls[0];
        var x' := varMapping[x];

        var f := (vDecl : (var_name, Ty)) => 
            if vDecl.0 in varMapping.Keys then (varMapping[vDecl.0], vDecl.1) else vDecl;
        var varDecls' := Sequences.Map(f, varDecls);

        forall s1, s2 | RelState(varMapping, s1, s2, s2Orig)
        ensures ForallVarDecls(a, varDecls, p1)(s1) == ForallVarDecls(a, varDecls', p2)(s2)
        {
          forall vs | ValuesRespectDecls(a, vs, varDecls)
          ensures p1(StateUpdVarDecls(s1, varDecls, vs)) == p2(StateUpdVarDecls(s2, varDecls', vs))
          {
            var s1' := StateUpdVarDecls(s1, varDecls, vs);
            var s2' := StateUpdVarDecls(s2, varDecls', vs);
            assert RelState(varMapping, s1', s2', s2Orig) by {
              RelStateUpdVarDeclsPreserve(varMapping, s1, s2, s2Orig, varDecls, varDecls', vs);
            }
            reveal RelPred();
          }
          ForallVarDeclsEquiv(a, varDecls, varDecls', p1, p2, s1, s2);
        }

        reveal RelPred();
      }
    }

  lemma ForallVarDeclRel2<A(!new)>(
      a: absval_interp<A>, 
      varDecls: seq<(var_name, Ty)>, 
      varMapping: map<var_name, var_name>, 
      p1: Predicate<A>,
      p2: Predicate<A>,
      s1: state<A>,
      s2: state<A>,
      sOrig: MapOrig<Val<A>>)
      requires RelPred(varMapping, p1, p2, sOrig)
      requires RelState(varMapping, s1, s2, sOrig)
      requires GetVarNames(varDecls) <= varMapping.Keys
      requires Maps.Injective(varMapping)
      ensures 
        var f := (vDecl : (var_name, Ty)) => 
            if vDecl.0 in varMapping.Keys then (varMapping[vDecl.0], vDecl.1) else vDecl;
        var varDecls' := Sequences.Map(f, varDecls);
        ForallVarDecls(a, varDecls, p1)(s1) ==  ForallVarDecls(a, varDecls', p2)(s2)
    {
      ForallVarDeclRel(a, varDecls, varMapping, p1, p2, sOrig);
      reveal RelPred();
    }

  lemma {:induction false} SubstSimpleCmdCorrect<A(!new)>(a: absval_interp<A>, sc: SimpleCmd, varMapping: map<var_name, var_name>, 
      post1: Predicate<A>, post2: Predicate<A>, s2Orig: MapOrig<Val<A>>)
      requires sc.NoBinders()
      requires RelPred(varMapping, post1, post2, s2Orig)
      requires sc.WellFormedVars(varMapping.Keys)
      requires Maps.Injective(varMapping)
      ensures 
        var sc' := sc.SubstSimpleCmd(varMapping);
        RelPred(varMapping, WpSimpleCmd(a, sc, post1), WpSimpleCmd(a, sc', post2), s2Orig)
    {
      var sc' := sc.SubstSimpleCmd(varMapping);
      var pre1 := WpSimpleCmd(a, sc, post1);
      var pre2 := WpSimpleCmd(a, sc', post2);
      forall s1:map<var_name, Val<A>>, s2 | RelState(varMapping, s1, s2, s2Orig)
        ensures pre1(s1) == pre2(s2)
      {
        reveal RelPred();
        match sc {
          case Skip => 
          case Assume(e) => 
            reveal RelState();
            MultiSubstExprSpec2(a, varMapping, e, s1, s2);
          case Assert(e) => 
            reveal RelState();
            reveal RelPred();
            MultiSubstExprSpec2(a, varMapping, e, s1, s2);
          case Assign(x, t, e) =>
            var e' := e.MultiSubstExpr(varMapping);
            var v1Opt := EvalExpr(a, e, s1);
            var v2Opt := EvalExpr(a, e', s2);
            assert v1Opt == v2Opt by {
              reveal RelState();
              MultiSubstExprSpec2(a, varMapping, e, s1, s2);
            }

            if(v1Opt.Some?) {
              var v := v1Opt.value;
              var x' := varMapping[x];

              assert RelState(varMapping, s1[x := v], s2[x' := v], s2Orig) by {
                RelStateUpdPreserve(varMapping, s1, s2, s2Orig, x, v);
              }
            }
          case Havoc(vDecls) => 
            var f := 
              (vDecl : (var_name, Ty)) => 
                    if vDecl.0 in varMapping.Keys then (varMapping[vDecl.0], vDecl.1) else vDecl;
            var vDecls' := Sequences.Map(f, vDecls);
            
            calc {
              WpSimpleCmd(a, Havoc(vDecls), post1)(s1);
              ForallVarDecls(a, vDecls, post1)(s1);
              { ForallVarDeclRel2(a, vDecls, varMapping, post1, post2, s1, s2, s2Orig); }
              ForallVarDecls(a, vDecls', post2)(s2);
              WpSimpleCmd(a, Havoc(vDecls'), post2)(s2);
              WpSimpleCmd(a, Havoc(vDecls).SubstSimpleCmd(varMapping), post2)(s2);
            }
          case SeqSimple(sc1, sc2) =>
            var sc1' := sc1.SubstSimpleCmd(varMapping);
            var sc2' := sc2.SubstSimpleCmd(varMapping);

            var post1' := WpSimpleCmd(a, sc2, post1);
            var post2' := WpSimpleCmd(a, sc2', post2);


            calc {
              WpSimpleCmd(a, SeqSimple(sc1, sc2), post1)(s1);
              WpSimpleCmd(a, sc1, post1')(s1);
              { 
                assert RelPred(varMapping, post1', post2', s2Orig) by {
                  SubstSimpleCmdCorrect(a, sc2, varMapping, post1, post2, s2Orig);
                }
                SubstSimpleCmdCorrect(a, sc1, varMapping, post1', post2', s2Orig); 
              }
              WpSimpleCmd(a, sc1', post2')(s2);
              WpSimpleCmd(a, SeqSimple(sc1', sc2'), post2)(s2);
            }
        }
      }
    }

    predicate {:opaque} RelPost<A(!new)>(m: map<var_name, var_name>, post1: WpPost<A>, post2: WpPost<A>, s2Orig: MapOrig<Val<A>>)
    {
      && post1.scopes.Keys == post2.scopes.Keys
      && RelPred(m, post1.normal, post2.normal, s2Orig)
      && RelPred(m, post1.currentScope, post2.currentScope, s2Orig)
      && (forall lbl | lbl in post1.scopes.Keys :: RelPred(m, post1.scopes[lbl], post2.scopes[lbl], s2Orig))
    }

    lemma ResetVarsStateLookup<A(!new)>(varDecls: seq<VarDecl>, s: state<A>, sOrig: state<A>, x: var_name)
    requires x in GetVarNames(varDecls)
    ensures Maps.Get(ResetVarsState(varDecls, s, sOrig), x) == Maps.Get(sOrig, x)
    { }

    lemma ResetVarsStateLookup2<A(!new)>(varDecls: seq<VarDecl>, s: state<A>, sOrig: state<A>, x: var_name)
    requires x !in GetVarNames(varDecls)
    ensures Maps.Get(ResetVarsState(varDecls, s, sOrig), x) == Maps.Get(s, x)
    { }

    lemma RelStateSwitch<A(!new)>(
      m: map<var_name, var_name>, 
      varDecls: seq<VarDecl>, 
      varDecls': seq<VarDecl>,
      sA: state<A>, 
      sB: state<A>, 
      s1: state<A>,
      s2: state<A>,
      s2Orig: MapOrig<Val<A>>)
    requires |varDecls| == |varDecls'|
    requires m.Values !! GetVarNames(varDecls')
    requires s2Orig.Keys !! GetVarNames(varDecls')
    requires 
      var s2OrigNewKeys := set x | x in GetVarNames(varDecls) && x in m.Keys :: m[x];
      var s2Orig' := s2Orig + map x' | x' in s2OrigNewKeys :: Maps.Get(s2, x');
      var m' := m + ConvertVDeclsToSubstMap(varDecls, varDecls');
      && RelState(m', sA, sB, s2Orig')
      && RelState(m, s1, s2, s2Orig)
    requires |varDecls| == |varDecls'|
    ensures 
      RelState(m, ResetVarsState(varDecls, sA, s1), ResetVarsState(varDecls', sB, s2), s2Orig)
    {
      reveal RelState();

      var s2OrigNewKeys := set x | x in GetVarNames(varDecls) && x in m.Keys :: m[x];
      var s2Orig' := s2Orig + map x' | x' in s2OrigNewKeys :: Maps.Get(s2, x');
      var mExt := ConvertVDeclsToSubstMap(varDecls, varDecls');
      var m' := m + mExt;

      var sA' := ResetVarsState(varDecls, sA, s1);
      var sB' := ResetVarsState(varDecls', sB, s2);

      forall k | k in m.Keys
      ensures Maps.Get(sA', k) == Maps.Get(sB', m[k])
      {
        if k in mExt {
          assert k in GetVarNames(varDecls);
          assert m[k] in s2OrigNewKeys;
          calc {
            Maps.Get(sB', m[k]);
            {
              assert m[k] !in GetVarNames(varDecls');
              ResetVarsStateLookup2(varDecls', sB, s2, m[k]);
            }
            Maps.Get(sB, m[k]);
            s2Orig'[m[k]];
            Maps.Get(s2, m[k]);
            Maps.Get(s1, k);
            {
              ResetVarsStateLookup(varDecls, sA, s1, k);
            }
            Maps.Get(sA', k);
          }
        } else {
          calc {
            Maps.Get(sB', m[k]);
            {
              assert m[k] !in GetVarNames(varDecls');
              ResetVarsStateLookup2(varDecls', sB, s2, m[k]);
            }
            Maps.Get(sB, m[k]);
            Maps.Get(sA, k);
            {
              assert k !in GetVarNames(varDecls);
              ResetVarsStateLookup2(varDecls, sA, s1, k);
            }
            Maps.Get(sA', k);
          }
        }
      }

      forall k | k in s2Orig.Keys
      ensures Maps.Get(sB', k) == s2Orig[k]
      {
        assert m'.Values !! s2Orig'.Keys;
        assert m.Values !! s2Orig.Keys;
        assert m.Values !! GetVarNames(varDecls');

        calc {
          Maps.Get(sB', k);
          {
            assert k !in GetVarNames(varDecls');
            ResetVarsStateLookup2(varDecls', sB, s2, k);
          }
          Maps.Get(sB, k);
          s2Orig'[k];
          s2Orig[k];
        }
      }
    }

  lemma RelPredSwitch<A(!new)>(
    m: map<var_name, var_name>, 
    varDecls: seq<VarDecl>, 
    varDecls': seq<VarDecl>,
    p: Predicate<A>, 
    q: Predicate<A>, 
    s1: state<A>,
    s2: state<A>,
    s2Orig: MapOrig<Val<A>>)
  requires RelPred(m, p, q, s2Orig)
  requires 
    && |varDecls| == |varDecls'|
    && m.Values !! GetVarNames(varDecls')
    && s2Orig.Keys !! GetVarNames(varDecls')
    && RelState(m, s1, s2, s2Orig)
  ensures 
    var s2OrigNewKeys := set x | x in GetVarNames(varDecls) && x in m.Keys :: m[x];
    var s2Orig' := s2Orig + map x' | x' in s2OrigNewKeys :: Maps.Get(s2, x');
    var m' := m + ConvertVDeclsToSubstMap(varDecls, varDecls');
    RelPred(m', ResetVarsPred(varDecls, p, s1), ResetVarsPred(varDecls', q, s2), s2Orig')
  {
    var s2OrigNewKeys := set x | x in GetVarNames(varDecls) && x in m.Keys :: m[x];
    var s2Orig' := s2Orig + map x' | x' in s2OrigNewKeys :: Maps.Get(s2, x');
    var m' := m + ConvertVDeclsToSubstMap(varDecls, varDecls');

    forall sA, sB : state<A> | RelState(m', sA, sB, s2Orig')
    ensures ResetVarsPred(varDecls, p, s1)(sA) == ResetVarsPred(varDecls', q, s2)(sB)
    {
      var sA' := ResetVarsState(varDecls, sA, s1);
      var sB' := ResetVarsState(varDecls', sB, s2);

      assert p(sA') == q(sB') by {
        assert RelState(m, sA', sB', s2Orig) by {
          RelStateSwitch(m, varDecls, varDecls', sA, sB, s1, s2, s2Orig);
        }
        reveal RelPred();
      }
    }

    reveal RelPred();
  }

  lemma RelPostSwitch<A(!new)>(
    m: map<var_name, var_name>, 
    varDecls: seq<VarDecl>, 
    varDecls': seq<VarDecl>,
    post1: WpPost<A>, 
    post2: WpPost<A>, 
    s1: state<A>,
    s2: state<A>,
    s2Orig: MapOrig<Val<A>>)
  requires RelPost(m, post1, post2, s2Orig)
  requires 
    && |varDecls| == |varDecls'|
    && m.Values !! GetVarNames(varDecls')
    && s2Orig.Keys !! GetVarNames(varDecls')
    && RelState(m, s1, s2, s2Orig)
  ensures 
    var s2OrigNewKeys := set x | x in GetVarNames(varDecls) && x in m.Keys :: m[x];
    var s2Orig' := s2Orig + map x' | x' in s2OrigNewKeys :: Maps.Get(s2, x');
    var m' := m + ConvertVDeclsToSubstMap(varDecls, varDecls');
    RelPost(m', ResetVarsPost(varDecls, post1, s1), ResetVarsPost(varDecls', post2, s2), s2Orig')
  {
    reveal RelPost();

    var s2OrigNewKeys := set x | x in GetVarNames(varDecls) && x in m.Keys :: m[x];
    var s2Orig' := s2Orig + map x' | x' in s2OrigNewKeys :: Maps.Get(s2, x');
    var m' := m + ConvertVDeclsToSubstMap(varDecls, varDecls');

    RelPredSwitch(m, varDecls, varDecls', post1.normal, post2.normal, s1, s2, s2Orig);
    RelPredSwitch(m, varDecls, varDecls', post1.currentScope, post2.currentScope, s1, s2, s2Orig);
    forall lbl | lbl in post1.scopes.Keys
    ensures RelPred(m', ResetVarsPred(varDecls, post1.scopes[lbl], s1), ResetVarsPred(varDecls', post2.scopes[lbl], s2), s2Orig')
    {
      RelPredSwitch(m, varDecls, varDecls', post1.scopes[lbl], post2.scopes[lbl], s1, s2, s2Orig);
    }
  }

  lemma ConvertVDeclsToSubstMapInj(varDecls: seq<VarDecl>, varDecls': seq<VarDecl>)
  requires Sequences.HasNoDuplicates(GetVarNamesSeq(varDecls'))
  requires |varDecls| == |varDecls'|
  ensures 
    && var res := ConvertVDeclsToSubstMap(varDecls, varDecls');
    && Maps.Injective(res)
  {
    reveal Maps.Injective();

    if |varDecls| > 0 {
      var oldName:=  varDecls[0].0;
      var newName := varDecls'[0].0;

      var m' := ConvertVDeclsToSubstMap(varDecls[1..], varDecls'[1..]);

      assert GetVarNamesSeq(varDecls'[1..]) == GetVarNamesSeq(varDecls')[1..];

      assert Maps.Injective(m') by {
        assert Sequences.HasNoDuplicates(GetVarNamesSeq(varDecls'[1..])) by {
          reveal Sequences.HasNoDuplicates();
        }

        ConvertVDeclsToSubstMapInj(varDecls[1..], varDecls'[1..]);
      }

      var m := m'[oldName := newName];

      forall x, x' | x != x' && x in m && x' in m 
      ensures m[x] != m[x']
      {
        if x == oldName || x' == oldName {
          var y' := if x == oldName then x' else x;

          assert newName != m[y'] by {
            assert m[y'] == m'[y'];
            assert m'[y'] in GetVarNamesSeq(varDecls'[1..]) by {
              assert m'[y'] in GetVarNames(varDecls'[1..]);
              GetVarNamesContainedSeq(m'[y'], varDecls'[1..]);
            }

            /* 
              Find two different indices in varDecls' that map to newName and m'[y'].
              The lookups of those indices in varDecls' will trigger the Sequences.HasNoDuplicates
              quantifier to then obtain the desired inequality. */

            var j :| 1 <= j < |varDecls'| && GetVarNamesSeq(varDecls')[j] == m'[y'];

            assert GetVarNamesSeq(varDecls')[0] == newName;
            reveal Sequences.HasNoDuplicates();
          }
        } 
      }
    }
  }

  lemma StateUpdVarDeclsLookupAux<A>(s1: state<A>, s2: state<A>, varDecls: seq<(var_name, Ty)>, varDecls': seq<(var_name, Ty)>,vs: seq<Val<A>>, k: var_name)
  requires |varDecls| == |varDecls'| == |vs|
  requires k in GetVarNames(varDecls)
  requires Sequences.HasNoDuplicates(GetVarNamesSeq(varDecls'))
  ensures 
    var m := ConvertVDeclsToSubstMap(varDecls, varDecls');
    var s1' := StateUpdVarDecls(s1, varDecls, vs);
    var s2' := StateUpdVarDecls(s2, varDecls', vs);
    s1'[k] == s2'[m[k]]
  { 
    if |varDecls| == 0 {

    } else {
      var oldName := varDecls[0].0;
      var newName := varDecls'[0].0;

      var s1'' := StateUpdVarDecls(s1, varDecls[1..], vs[1..]);
      var s2'' := StateUpdVarDecls(s2, varDecls'[1..], vs[1..]);

      var s1' := s1''[oldName := vs[0]];
      var s2' := s2''[newName := vs[0]];

      var m'' := ConvertVDeclsToSubstMap(varDecls[1..], varDecls'[1..]);
      var m' := m''[oldName := newName];

      if k == oldName {

      } else {
        reveal Sequences.HasNoDuplicates();
        assert m'[k] in GetVarNames(varDecls'[1..]);
        assert GetVarNamesSeq(varDecls'[1..]) == GetVarNamesSeq(varDecls')[1..];
        StateUpdVarDeclsLookupAux(s1, s2, varDecls[1..], varDecls'[1..], vs[1..], k);
        assert m''[k] in GetVarNames(varDecls'[1..]);
        assert m''[k] in GetVarNamesSeq(varDecls'[1..]) by {
          GetVarNamesContainedSeq(m''[k], varDecls'[1..]);
        }
        assert m'[k] != newName by {
          assert newName == GetVarNamesSeq(varDecls')[0];
        }
        calc {
          s1'[k];
          s1''[k];
          s2''[m''[k]];
          s2''[m'[k]];
          s2'[m'[k]];
        }
      }
    }
  }

  lemma ForallVarDeclsRelSwitch<A(!new)>(
      a: absval_interp<A>, 
      varDecls: seq<(var_name, Ty)>, 
      varDecls': seq<(var_name, Ty)>,
      m: map<var_name, var_name>, 
      p1: Predicate<A>,
      p2: Predicate<A>,
      s1: state<A>,
      s2: state<A>,
      s2Orig: MapOrig<Val<A>>)
      requires 
        && |varDecls| == |varDecls'|
        && (forall i | 0 <= i < |varDecls| :: varDecls[i].1 == varDecls'[i].1)
      requires 
        var s2OrigNewKeys := set x | x in GetVarNames(varDecls) && x in m.Keys :: m[x];
        var s2Orig' := s2Orig + map x' | x' in s2OrigNewKeys :: Maps.Get(s2, x');
        var m' := m + ConvertVDeclsToSubstMap(varDecls, varDecls');
        && m.Values !! GetVarNames(varDecls')
        && Sequences.HasNoDuplicates(GetVarNamesSeq(varDecls'))
        && RelPred(m', p1, p2, s2Orig')
        && RelState(m, s1, s2, s2Orig)
        && s2Orig.Keys !! GetVarNames(varDecls')
        //&& m'.Values !! s2Orig'.Keys
      requires Maps.Injective(m)
      ensures 
        ForallVarDecls(a, varDecls, p1)(s1) == 
        ForallVarDecls(a, varDecls', p2)(s2)
  {
    var s2OrigNewKeys := set x | x in GetVarNames(varDecls) && x in m.Keys :: m[x];
    var s2Orig' := s2Orig + map x' | x' in s2OrigNewKeys :: Maps.Get(s2, x');
    var m' := m + ConvertVDeclsToSubstMap(varDecls, varDecls');

    forall vs | ValuesRespectDecls(a, vs, varDecls)
    ensures p1(StateUpdVarDecls(s1, varDecls, vs)) == p2(StateUpdVarDecls(s2, varDecls', vs))
    {
      var s1' := StateUpdVarDecls(s1, varDecls, vs);
      var s2' := StateUpdVarDecls(s2, varDecls', vs);
      assert RelState(m', s1', s2', s2Orig') by {
        reveal RelState();
        forall k | k in m'.Keys 
        ensures Maps.Get(s1', k) == Maps.Get(s2', m'[k])
        {
          if k in GetVarNames(varDecls) {
            StateUpdVarDeclsLookupAux(s1, s2, varDecls, varDecls', vs, k);
          } else {
            assert m[k] == m'[k];
            calc {
              Maps.Get(s1', k);
              { StateUpdVarDeclsLookup1(s1, varDecls, vs, k); }
              Maps.Get(s1, k);
              Maps.Get(s2, m[k]);
              {
                assert m[k] !in GetVarNames(varDecls');
                StateUpdVarDeclsLookup1(s2, varDecls', vs, m[k]);
              }
              Maps.Get(s2', m'[k]);
            }
          }
        }

        forall k | k in s2Orig'.Keys
        ensures Maps.Get(s2', k) == s2Orig'[k]
        {
          reveal RelState();
          assert k !in GetVarNames(varDecls');
          calc {
            Maps.Get(s2', k);
            { StateUpdVarDeclsLookup1(s2, varDecls', vs, k); }
            Maps.Get(s2, k);
          }
        }
        
        assert m'.Values !! s2Orig'.Keys by {
          assert m.Values !! s2Orig.Keys by {
            reveal RelState();
          }
          assert m'.Values <= m.Values + GetVarNames(varDecls');

          assert s2Orig'.Keys <= s2Orig.Keys + s2OrigNewKeys;

          assert s2OrigNewKeys !! m'.Values by {
            forall a, b | a in s2OrigNewKeys && b in m'.Values 
            ensures a != b
            {
              var x :| x in GetVarNames(varDecls) && x in m.Keys && m[x] == a;
              assert x in m.Keys;
              assert m[x] == a;

              assert m'[x] != m[x];

              var y :| y in m'.Keys && m'[y] == b;

              if y !in GetVarNames(varDecls) {
                assert x != y;
                calc {
                  m'[y];
                  m[y];
                != { reveal Maps.Injective(); }
                  m[x];
                }
              } else {
                assert m'[y] in GetVarNames(varDecls');
                assert m.Values !! GetVarNames(varDecls');
              }
            }
          }
        }
      }
      reveal RelPred();
    }

    ForallVarDeclsEquiv(a, varDecls, varDecls', p1, p2, s1, s2);
  } 

  /** 
   The lemma shows that if two postconditions post1 and post2 behave the same  
   for states related via substMap (the mapping between active original variables
   and their desugared counterparts), then the corresponding weakest preconditions
   of the original and desugared programs must behave the same on related states.

   The parameter s2Orig plays a key role in the proof of scopes.  Suppose 

    Scope {
      var x: int
      ...
      Scope {
        var x: int
        ...
      }
    } 
    
    is desugared to
    
    Scope {
      var x1: int
      ...
      Scope {
        var x2: int
        ...
      }
    } 

  When proving the relationship between outer scopes, in the proof, s2Orig is chosen to be
  the empty map.
  When proving the relationship between the inner scopes, s2Orig is chosen to be 
  the singleton map where x1 maps to the value that x1 had right before executing the inner scope.
  In general, the domain of s2Orig is the set of desugared variables that are currently shadowed.

  RelState(..., ..., s2, s2Orig) ensures that the state s2 in the desugared program coincides
  with s2Orig on s2Orig's domain. That is, in the proof, it makes explicit that shadowed 
  variables cannot be modified. This is essential in the scopes case, because if shadowed variables 
  were modified, then one cannot prove that the programs after the scopes are related.
  In terms of weakest preconditions, this means that we cannot use the fact that the 
  given postconditions post1 and post2 are related, because this relationship holds only
  if the shadowed variabels are not modified.  
  */
  lemma {:induction false} MakeScopedVarsUniqueCorrect<A(!new)>(
        a: absval_interp<A>,
        c: Cmd, 
        substMap: map<var_name, var_name>, 
        counter: nat,
        post1: WpPost<A>,
        post2: WpPost<A>,
        s2Orig: MapOrig<Val<A>>,
        names: set<string>)
      requires c.WellFormedVars(substMap.Keys)
      requires Maps.Injective(substMap)
      requires c.NoBinders()
      requires 
        var (c', counter') := MakeScopedVarsUnique(c, substMap, counter);
        && NoLoopsNoIfGuard(c)
        && LabelsWellDefAux(c, post1.scopes.Keys) 
        && LabelsWellDefAux(c', post2.scopes.Keys)
        && RelPost(substMap, post1, post2, s2Orig)
        && s2Orig.Keys <= VarNameSet(names, 0, counter)
        && substMap.Values <= VarNameSet(names, 0, counter) 
      //requires forall vDecl | vDecls in seqSubstMap :: substMap(vDecl.) == sequSubstMap
      ensures 
        var (c', counter') := MakeScopedVarsUnique(c, substMap, counter);
        RelPred(substMap, WpCmd(a, c, post1), WpCmd(a, c', post2), s2Orig)
    {
      reveal RelPost();
      match c {
        case SimpleCmd(sc) =>
          reveal WpCmd();
          SubstSimpleCmdCorrect(a, sc, substMap, post1.normal, post2.normal, s2Orig);
        case Break(_) => reveal WpCmd();
        case Seq(c1, c2) => 
          var (c1', counter1') := MakeScopedVarsUnique(c1, substMap, counter);
          var (c2', counter2') := MakeScopedVarsUnique(c2, substMap, counter1');

          var post1' := WpPost(WpCmd(a, c2, post1), post1.currentScope, post1.scopes);
          var post2' := WpPost(WpCmd(a, c2', post2), post2.currentScope, post2.scopes);

          assert RelPost(substMap, post1', post2', s2Orig) by {
            assert RelPred(substMap, WpCmd(a, c2, post1), WpCmd(a, c2', post2), s2Orig) by {
              VarNameSetExtend(names, 0, counter, counter1');
              MakeScopedVarsUniqueCorrect(a, c2, substMap, counter1', post1, post2, s2Orig, names);
            }
          }

          assert RelPred(substMap, WpCmd(a, c1, post1'), WpCmd(a, c1', post2'), s2Orig) by {
            MakeScopedVarsUniqueCorrect(a, c1, substMap, counter, post1', post2', s2Orig, names);
          }

          reveal WpCmd();
        case Scope(optLabel, varDecls, body) => 
          /* Goal: RelPred(substMap, WpCmd(a, c, post1), WpCmd(a, c', post2)) */
          var varDecls' := CreateUniqueVarDecls(varDecls, counter);

          assert Sequences.HasNoDuplicates(GetVarNamesSeq(varDecls')) by {
            CreateUniqueVarDeclsNoDup(varDecls, counter);
          }

          var counter' := counter + |varDecls'|;
          var substMap' := substMap + ConvertVDeclsToSubstMap(varDecls, varDecls');
          assert substMap'.Keys == GetVarNames(varDecls)+substMap.Keys;
          var (body', counter'') := MakeScopedVarsUnique(body, substMap', counter');
          //(Scope(optLabel, varDecls', body''), counter'')
          var c' := Scope(optLabel, varDecls', body');

          var updatedScopes1 := 
            if optLabel.Some? then 
              post1.scopes[optLabel.value := post1.normal]
            else post1.scopes;
          assert updatedScopes1.Keys == if optLabel.Some? then {optLabel.value} + post1.scopes.Keys else post1.scopes.Keys;
          
          var updatedScopes2 := 
            if optLabel.Some? then 
              post2.scopes[optLabel.value := post2.normal]
            else post2.scopes;
          assert updatedScopes2.Keys == if optLabel.Some? then {optLabel.value} + post2.scopes.Keys else post2.scopes.Keys;
          
          var post1' := WpPost(post1.normal, post1.normal, updatedScopes1);
          var post2' := WpPost(post2.normal, post2.normal, updatedScopes2);

          forall s1,s2 | RelState(substMap, s1, s2, s2Orig)
          ensures WpCmd(a, c, post1)(s1) == WpCmd(a, c', post2)(s2)
          {
            /* We want to prove that if a name x in varDecls is already mapped to x' in substMap, then 
              it must be the case that x' will not be modified within the scope, since we map x to a new
              name and x' won't be reused in the scope. We need this to make sure that when the scope is finished
              and the variables are reset, x and x' are again related in the resulting states (
                for x we know the value is reset to the previous value, for x' we prove the value cannot have changed
              ). */
            var s2OrigNewKeys := set x | x in GetVarNames(varDecls) && x in substMap.Keys :: substMap[x];
            var s2Orig' := s2Orig + map x' | x' in s2OrigNewKeys :: Maps.Get(s2, x');

            assert 
              && substMap.Values !! GetVarNames(varDecls')
              && s2Orig.Keys !! GetVarNames(varDecls') by {
              VarNameSetDisjoint(names, GetVarNames(varDecls), 0, counter, counter, counter + |varDecls'|);
            }

            calc {
              WpCmd(a, Scope(optLabel, varDecls, body), post1)(s1);
              {reveal WpCmd();}
              ForallVarDecls(a, varDecls, WpCmd(a, body, ResetVarsPost(varDecls, post1', s1)))(s1);
              { 
                assert RelPost(substMap', ResetVarsPost(varDecls, post1', s1), ResetVarsPost(varDecls', post2', s2), s2Orig') by 
                { 
                  assert RelPost(substMap, post1, post2, s2Orig);

                  assert RelPost(substMap, post1', post2', s2Orig);
                  {
                    reveal RelPost();
                  }

                  RelPostSwitch(substMap, varDecls, varDecls', post1', post2', s1, s2, s2Orig);
                }

                assert Maps.Injective(substMap') by {
                  assert Maps.Injective(ConvertVDeclsToSubstMap(varDecls, varDecls')) by {
                    ConvertVDeclsToSubstMapInj(varDecls, varDecls');
                  }
                  assert substMap.Values !! GetVarNames(varDecls');
                  UnionOfInjectiveMaps(substMap, ConvertVDeclsToSubstMap(varDecls, varDecls'));
                }

                assert RelPred(substMap', 
                  WpCmd(a, body, ResetVarsPost(varDecls, post1', s1)), 
                  WpCmd(a, body', ResetVarsPost(varDecls', post2', s2)),
                  s2Orig') by
                  { 
                    assert s2Orig'.Keys <= VarNameSet(names+GetVarNames(varDecls), 0, counter') by {
                      VarNameSetExtend2(names, GetVarNames(varDecls), 0, counter, counter');
                    }

                    assert substMap'.Values <= VarNameSet(names+GetVarNames(varDecls), 0, counter') by {
                      assert substMap'.Values <= VarNameSet(names, 0, counter) + VarNameSet(GetVarNames(varDecls), counter, counter + |varDecls|);
                      VarNameSetAppend(names, GetVarNames(varDecls), 0, counter, counter, counter + |varDecls|);
                    }

                    MakeScopedVarsUniqueCorrect(
                      a, body, substMap', counter',  ResetVarsPost(varDecls, post1', s1), ResetVarsPost(varDecls', post2', s2), s2Orig',
                      names+GetVarNames(varDecls)
                    ); 
                  }
                  
                  var p1 := WpCmd(a, body, ResetVarsPost(varDecls, post1', s1));
                  var p2 := WpCmd(a, body', ResetVarsPost(varDecls', post2', s2));

                  ForallVarDeclsRelSwitch(
                      a, 
                      varDecls, 
                      varDecls',
                      substMap, 
                      p1,
                      p2,
                      s1,
                      s2,
                      s2Orig);
              }
              ForallVarDecls(a, varDecls', WpCmd(a, body', ResetVarsPost(varDecls', post2', s2)))(s2);
              {reveal WpCmd();}
              WpCmd(a, Scope(optLabel, varDecls', body'), post2)(s2);
            }
          }

          reveal RelPred();
        case If(None, thn, els) => 
          var (thn', counter') := MakeScopedVarsUnique(thn, substMap, counter);
          var (els', counter'') := MakeScopedVarsUnique(els, substMap, counter');

          assert RelPred(substMap, WpCmd(a, thn, post1), WpCmd(a, thn', post2), s2Orig) by {
            MakeScopedVarsUniqueCorrect(a, thn, substMap, counter, post1, post2, s2Orig, names);
          }

          assert RelPred(substMap, WpCmd(a, els, post1), WpCmd(a, els', post2), s2Orig) by {
            VarNameSetExtend(names, 0, counter, counter');
            MakeScopedVarsUniqueCorrect(a, els, substMap, counter', post1, post2, s2Orig, names);
          }

          reveal RelPred();

          forall sA, sB | RelState(substMap, sA, sB, s2Orig)
          ensures WpCmd(a, c, post1)(sA) == WpCmd(a, If(None, thn', els'), post2)(sB)
          {
            calc {
              WpCmd(a, c, post1)(sA);
              { reveal WpCmd(); }
              Util.AndOpt(WpCmd(a, thn, post1)(sA), WpCmd(a, els, post1)(sA));
              Util.AndOpt(WpCmd(a, thn', post2)(sB), WpCmd(a, els', post2)(sB));
              { reveal WpCmd(); }
              WpCmd(a, If(None, thn', els'), post2)(sB);
            }
          }
      }
    }

}