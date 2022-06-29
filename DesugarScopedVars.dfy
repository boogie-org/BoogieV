include "BoogieSemantics.dfy"
include "dafny-libraries/src/Collections/Sequences/Seq.dfy"
include "dafny-libraries/src/Collections/Maps/Maps.dfy"

module DesugarScopedVars {

  import opened BoogieLang
  import opened BoogieSemantics
  import Sequences = Seq
  import Maps
  import Util
  import opened Wrappers

  predicate {:opaque} RelState<V>(m: map<var_name, var_name>, s1: map<var_name, V>, s2: map<var_name, V>)
  {
    (forall k | k in m.Keys :: Maps.Get(s1, k) == Maps.Get(s2, m[k]))
  }

  lemma RelStateLarger<V>(m: map<var_name, var_name>, m': map<var_name, var_name>, s1: map<var_name, V>, s2: map<var_name, V>)
  requires RelState(m', s1, s2)
  requires MapGte(m', m)
  ensures RelState(m, s1, s2)
  {
    reveal MapGte();
    reveal RelState();
  }

 lemma {:verify false} RelStateEmpty<V>(s1: map<var_name, V> , s2: map<var_name, V>)
  ensures RelState(map[], s1, s2)
 { reveal RelState(); }

  predicate {:opaque} RelPred<A(!new)>(m: map<var_name, var_name>, post1: Predicate<A>, post2: Predicate<A>)
  {
    forall s, s' | RelState(m, s, s') :: post1(s) == post2(s')
  }

  predicate {:opaque} MapGte(m': map<var_name, var_name>, m: map<var_name, var_name>)
  {
    forall x | x in m.Keys :: x in m'.Keys && m[x] == m'[x]
  }

  lemma RelPredLarger<A(!new)>(m: map<var_name, var_name>, m': map<var_name, var_name>, post1: Predicate<A>, post2: Predicate<A>)
  requires RelPred(m, post1, post2)
  requires MapGte(m', m)
  ensures RelPred(m', post1, post2)
  {
    reveal RelPred();
    forall s1,s2: map<var_name, Val<A>> | RelState(m', s1, s2)
    ensures post1(s1) == post2(s2)
    {
      RelStateLarger(m, m', s1, s2);
    }
  }

  predicate {:opaque} RelPost<A(!new)>(m: map<var_name, var_name>, post1: WpPostShallow<A>, post2: WpPostShallow<A>)
  {
    && post1.scopes.Keys == post2.scopes.Keys
    && RelPred(m, post1.normal, post2.normal)
    && RelPred(m, post1.currentScope, post2.currentScope)
    && (forall lbl | lbl in post1.scopes.Keys :: RelPred(m, post1.scopes[lbl], post2.scopes[lbl]))
  }

  function method MultiSubstExpr(e: Expr, varMapping: map<var_name, var_name>): Expr

 lemma {:verify false} MultiSubstExprSpec<A(!new)>(a: absval_interp<A>, varMapping: map<var_name, var_name>, e: Expr, s1: state<A>, s2: state<A>)
    requires forall x | x in e.FreeVars() :: 
      && (x in varMapping.Keys ==> Maps.Get(s1, x) == Maps.Get(s2, varMapping[x]))
      && (x !in varMapping.Keys ==> Maps.Get(s1, x) == Maps.Get(s2, x))
    ensures EvalExpr(a, e, s1) == EvalExpr(a, MultiSubstExpr(e, varMapping), s2)
  
 lemma {:verify false} MultiSubstExprSpec2<A(!new)>(a: absval_interp<A>, varMapping: map<var_name, var_name>, e: Expr, s1: state<A>, s2: state<A>)
    requires RelState(varMapping, s1, s2)
    requires e.FreeVars() <= varMapping.Keys
    ensures EvalExpr(a, e, s1) == EvalExpr(a, MultiSubstExpr(e, varMapping), s2)
  {
    reveal RelState();
    MultiSubstExprSpec(a, varMapping, e, s1, s2);
  }

  function method SubstSimpleCmd(sc: SimpleCmd, varMapping: map<var_name, var_name>) : SimpleCmd
  {
    match sc
    case Skip => Skip 
    case Assert(e) => Assert(MultiSubstExpr(e, varMapping))
    case Assume(e) => Assume(MultiSubstExpr(e, varMapping))
    case Assign(x, t, e) =>
      var newLHS := if x in varMapping.Keys then varMapping[x] else x;
      var newRHS := MultiSubstExpr(e, varMapping);
      Assign(newLHS, t, newRHS)
    case Havoc(varDecls) =>
      var f := (vDecl : (var_name, Ty)) => 
          if vDecl.0 in varMapping.Keys then (varMapping[vDecl.0], vDecl.1) else vDecl;
      var varDecls' := Sequences.Map(f, varDecls);
      Havoc(varDecls')
    case SeqSimple(c1, c2)  =>
      SeqSimple(SubstSimpleCmd(c1, varMapping), SubstSimpleCmd(c2, varMapping))
  }

 lemma {:verify false} {:induction false} ForallVarDeclsRel<A(!new)>(
    a: absval_interp<A>, 
    varDecls: seq<(var_name, Ty)>, 
    varMapping: map<var_name, var_name>, 
    p1: Predicate<A>,
    p2: Predicate<A>)
    requires RelPred(varMapping, p1, p2)
    requires GetVarNames(varDecls) <= varMapping.Keys
    requires Maps.Injective(varMapping)
    ensures 
      var f := (vDecl : (var_name, Ty)) => 
          if vDecl.0 in varMapping.Keys then (varMapping[vDecl.0], vDecl.1) else vDecl;
      var varDecls' := Sequences.Map(f, varDecls);
      RelPred(varMapping, ForallVarDeclsShallow(a, varDecls, p1), ForallVarDeclsShallow(a, varDecls', p2))
  {
    var f := (vDecl : (var_name, Ty)) => 
        if vDecl.0 in varMapping.Keys then (varMapping[vDecl.0], vDecl.1) else vDecl;
    var varDecls' := Sequences.Map(f, varDecls);
    if |varDecls| == 0 {
      //trivial
      reveal ForallVarDeclsShallow();
      assert ForallVarDeclsShallow(a, varDecls, p1) == p1;
    } else {
      var (x,t) := varDecls[0];
      var x' := varMapping[x];

      var f := (vDecl : (var_name, Ty)) => 
          if vDecl.0 in varMapping.Keys then (varMapping[vDecl.0], vDecl.1) else vDecl;
      var varDecls' := Sequences.Map(f, varDecls);

      forall s1: map<var_name, Val<A>>, s2, v: Val<A> | RelState(varMapping, s1, s2) && TypeOfVal(a, v) == t
        ensures ForallVarDeclsShallow(a, varDecls[1..], p1)(s1[x := v]) == ForallVarDeclsShallow(a, varDecls'[1..], p2)(s2[x' := v])
      {
        assert RelState(varMapping, s1[x := v], s2[x' := v]) by {
          RelStateUpdPreserve(varMapping, s1, s2, x, v);
        }
        ForallVarDeclsRel(a, varDecls[1..], varMapping, p1, p2);
        reveal RelPred();

        assert varDecls'[1..] == Sequences.Map(f, varDecls[1..]);
      }

      reveal ForallVarDeclsShallow();
    }
  }

 lemma {:verify false} ForallVarDeclsRel2<A(!new)>(
    a: absval_interp<A>, 
    varDecls: seq<(var_name, Ty)>, 
    varMapping: map<var_name, var_name>, 
    p1: Predicate<A>,
    p2: Predicate<A>,
    s1: state<A>,
    s2: state<A>)
    requires RelPred(varMapping, p1, p2)
    requires RelState(varMapping, s1, s2)
    requires GetVarNames(varDecls) <= varMapping.Keys
    requires Maps.Injective(varMapping)
    ensures 
      var f := (vDecl : (var_name, Ty)) => 
          if vDecl.0 in varMapping.Keys then (varMapping[vDecl.0], vDecl.1) else vDecl;
      var varDecls' := Sequences.Map(f, varDecls);
      ForallVarDeclsShallow(a, varDecls, p1)(s1) ==  ForallVarDeclsShallow(a, varDecls', p2)(s2)
  {
    ForallVarDeclsRel(a, varDecls, varMapping, p1, p2);
    reveal RelPred();
  }

 lemma {:verify false} RelStateUpdPreserve<V>(varMapping: map<var_name, var_name>, s1: map<var_name, V>, s2: map<var_name, V>, x: var_name, v: V)
 requires RelState(varMapping, s1, s2)
 requires Maps.Injective(varMapping)
 requires x in varMapping.Keys
 ensures RelState(varMapping, s1[x := v], s2[varMapping[x] := v])
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

 lemma {:verify false} {:verify true} RelStateRemovePreserve<V>(varMapping: map<var_name, var_name>, s1: map<var_name, V>, s2: map<var_name, V>, x: var_name)
 requires RelState(varMapping, s1, s2)
 requires Maps.Injective(varMapping)
 requires x in varMapping.Keys
 ensures RelState(varMapping, s1-{x}, s2-{varMapping[x]})
 {
  reveal RelState();
  var x' := varMapping[x];
  forall k | k in varMapping.Keys 
  ensures Maps.Get(s1-{x}, k) == Maps.Get(s2-{x'}, varMapping[k])
  {
    var k' := varMapping[k];
    if k != x {
      calc {
        Maps.Get(s1-{x}, k);
        Maps.Get(s1, k);
        Maps.Get(s2, k');
        { reveal Maps.Injective(); }
        Maps.Get(s2-{x'}, k');
      }
    }
  }
 }

 lemma {:verify false} {:induction false} SubstSimpleCmdCorrect<A(!new)>(a: absval_interp<A>, sc: SimpleCmd, varMapping: map<var_name, var_name>, 
    post1: Predicate<A>, post2: Predicate<A>)
    requires RelPred(varMapping, post1, post2)
    requires sc.WellFormedVars(varMapping.Keys)
    requires Maps.Injective(varMapping)
    ensures 
      var sc' := SubstSimpleCmd(sc, varMapping);
      RelPred(varMapping, WpShallowSimpleCmd(a, sc, post1), WpShallowSimpleCmd(a, sc', post2))
  {
    var sc' := SubstSimpleCmd(sc, varMapping);
    var pre1 := WpShallowSimpleCmd(a, sc, post1);
    var pre2 := WpShallowSimpleCmd(a, sc', post2);
    forall s1:map<var_name, Val<A>>, s2 | RelState(varMapping, s1, s2)
      ensures pre1(s1) == pre2(s2)
    {
      reveal RelPred();
      match sc {
        case Skip => 
        case Assume(e) => 
          MultiSubstExprSpec2(a, varMapping, e, s1, s2);
        case Assert(e) => 
          reveal RelPred();
          MultiSubstExprSpec2(a, varMapping, e, s1, s2);
        case Assign(x, t, e) =>
          var e' := MultiSubstExpr(e, varMapping);
          var v1Opt := EvalExpr(a, e, s1);
          var v2Opt := EvalExpr(a, e', s2);
          assert v1Opt == v2Opt by {
            MultiSubstExprSpec2(a, varMapping, e, s1, s2);
          }

          if(v1Opt.Some?) {
            var v := v1Opt.value;
            var x' := varMapping[x];

            assert RelState(varMapping, s1[x := v], s2[x' := v]) by {
              RelStateUpdPreserve(varMapping, s1, s2, x, v);
            }
          }
        case Havoc(vDecls) => 
          var f := 
            (vDecl : (var_name, Ty)) => 
                  if vDecl.0 in varMapping.Keys then (varMapping[vDecl.0], vDecl.1) else vDecl;
          var vDecls' := Sequences.Map(f, vDecls);
          
          calc {
            WpShallowSimpleCmd(a, Havoc(vDecls), post1)(s1);
            ForallVarDeclsShallow(a, vDecls, post1)(s1);
            { ForallVarDeclsRel2(a, vDecls, varMapping, post1, post2, s1, s2); }
            ForallVarDeclsShallow(a, vDecls', post2)(s2);
            WpShallowSimpleCmd(a, Havoc(vDecls'), post2)(s2);
            WpShallowSimpleCmd(a, SubstSimpleCmd(Havoc(vDecls), varMapping), post2)(s2);
          }
        case SeqSimple(sc1, sc2) =>
          var sc1' := SubstSimpleCmd(sc1, varMapping);
          var sc2' := SubstSimpleCmd(sc2, varMapping);

          var post1' := WpShallowSimpleCmd(a, sc2, post1);
          var post2' := WpShallowSimpleCmd(a, sc2', post2);


          calc {
            WpShallowSimpleCmd(a, SeqSimple(sc1, sc2), post1)(s1);
            WpShallowSimpleCmd(a, sc1, post1')(s1);
            { 
              assert RelPred(varMapping, post1', post2') by {
                SubstSimpleCmdCorrect(a, sc2, varMapping, post1, post2);
              }
              SubstSimpleCmdCorrect(a, sc1, varMapping, post1', post2'); 
            }
            WpShallowSimpleCmd(a, sc1', post2')(s2);
            WpShallowSimpleCmd(a, SeqSimple(sc1', sc2'), post2)(s2);
          }
      }
    }
  }

  function method CreateUniqueName(names: set<var_name>): var_name
    ensures CreateUniqueName(names) !in names
  
  const SEP : string := "#";

  function method VersionedName(name: string, n: nat) : string
  {
    name + SEP + Util.NatToString(n)
  }

  lemma {:verify false} SuffixDiffSameLength(prefix1: string, prefix2: string, suffix1:string, suffix2: string)
    requires |suffix1| == |suffix2|
    requires suffix1 != suffix2
    ensures prefix1+suffix1 != prefix1+suffix2
  {
    var i :| 0 <= i < |suffix1| && suffix1[i] != suffix2[i];

    var j := |suffix1|-i-1;

    calc {
      Sequences.Reverse(suffix1)[j];
      suffix1[i];
    !=
      suffix2[i];
      Sequences.Reverse(suffix2)[j];
    }

    assert Sequences.Reverse(prefix1+suffix1)[j] == Sequences.Reverse(suffix1)[j];
    assert Sequences.Reverse(prefix2+suffix2)[j] == Sequences.Reverse(suffix2)[j];

    assert Sequences.Reverse(prefix1+suffix1) != Sequences.Reverse(prefix2+suffix2) by {
      calc {
        Sequences.Reverse(prefix1+suffix1)[j];
        Sequences.Reverse(suffix1)[j];
      !=
        Sequences.Reverse(suffix2)[j];
        Sequences.Reverse(prefix2+suffix2)[j];
      }
    }
  }

  lemma VersionedNameInjective(prefix1: string, prefix2: string, i1: nat, i2: nat)
  requires i1 != i2
  ensures VersionedName(prefix1, i1) != VersionedName(prefix2, i2)
  {
    Util.NatToStringInjective(i1, i2);

    var i1S := Util.NatToString(i1);
    var i2S := Util.NatToString(i2);

    var s1 := prefix1 + SEP + i1S;
    var s2 := prefix2 + SEP + i2S;

    if |i1S| == |i2S| {
      assert s1 != s2 by {
        SuffixDiffSameLength(prefix1+SEP, prefix2+SEP, i1S, i2S);
      }
    } else {
      if |i1S| < |i2S| {
        var suffix1 := SEP+i1S;

        var prefix2 := prefix2 + SEP + i2S[0..|i2S|-|i1S|-1];
        var suffix2 := i2S[|i2S|-|i1S|-1..];

        assert suffix1[0] != suffix2[0] by {
          Util.HashTagNotInNatString(i2);
        }

        SuffixDiffSameLength(prefix1, prefix2 + SEP + i2S[0..|i2S|-|i1S|-1], SEP + i1S, i2S[|i2S|-|i1S|-1..]);

        assert prefix1+(SEP+i1S) == prefix1+SEP+i1S;
        assert (prefix2+SEP+i2S[0..|i2S|-|i1S|-1])+i2S[|i2S|-|i1S|-1..] == prefix2+SEP+i2S;
      } else {
        //symmetric to other case
        var suffix2 := SEP+i2S;

        var prefix1' := prefix1 + SEP + i1S[0..|i1S|-|i2S|-1];
        var suffix1 := i1S[|i1S|-|i2S|-1..];

        assert suffix1[0] != suffix2[0] by {
          Util.HashTagNotInNatString(i1);
        }

        SuffixDiffSameLength(prefix1', prefix2, suffix1, suffix2);

        assert (prefix1+SEP+i1S[0..|i1S|-|i2S|-1])+i1S[|i1S|-|i2S|-1..] == prefix1+SEP+i1S;
        assert prefix2+(SEP+i2S) == prefix2+SEP+i2S;
      }
    }
  }

  function {:opaque} VarNameSet(names: set<string>, i0: nat, i1: nat) : set<string>
  {
    set prefix, i | prefix in names && i0 <= i < i1 :: VersionedName(prefix, i)
  }

  lemma {:verify false} VarNameSetDisjoint(names: set<string>, i0: nat, i1: nat, i2: nat, i3: nat)
    requires i0 <= i1 <= i2 <= i3
    ensures VarNameSet(names, i0, i1) !! VarNameSet(names, i2, i3)
  {
    forall i,j,name1,name2 | i != j
    ensures VersionedName(name1, i) != VersionedName(name2, j)
    {
      VersionedNameInjective(name1, name2, i, j);
    }

    reveal VarNameSet();
  }

  function method CreateUniqueVarDecls(varDecls: seq<(var_name, Ty)>, usedNames: set<var_name>, counter: nat) : seq<(var_name,Ty)>
    ensures 
      var res := CreateUniqueVarDecls(varDecls, usedNames, counter);
      |varDecls| == |res|
  {
    /** TODO
      Currently, a suffix is added to every variable even if there are no clashes. 
      This makes it harder to read the target output. It would be nice if one could 
      reuse a name if it does not clash with anything else that has been so far. 
      Doing this would require a fold to avoid updating the counter if a name is 
      reused. Such a change would require restructuring the proof of the transformation
      making the names unique. 
      Alternatively, one could apply such a transformation later to remove the counters
      from names that don't require them. 
     */
    seq(|varDecls|, i requires 0 <= i < |varDecls| => (VersionedName(varDecls[i].0, counter+i), varDecls[i].1))
  }

  function method ConvertVDeclsToSubstMap(varDecls: seq<(var_name, Ty)>, varDecls': seq<(var_name, Ty)>) : map<var_name, var_name>
    requires |varDecls| == |varDecls'|
  {
    if |varDecls| == 0 then
      map[]
    else
      var oldName:= varDecls[0].0;
      var newVDecl := varDecls'[0];
      ConvertVDeclsToSubstMap(varDecls[1..], varDecls'[1..])[oldName := newVDecl.0]
  }

  /*
  * substMap: active variables that are mapped
  * freshVars: all fresh variable declarations
  */
  function method DesugarScopedVars(
    c: Cmd, 
    substMap: map<var_name, var_name>, 
    usedVars: (set<var_name>,nat),
    ghost seqSubstMap: seq<(var_name, Ty)>): (Cmd, (set<var_name>, nat))
    /*requires substMap.Values <= set c,x | x in substMap.Keys && 0 < c < usedVars.1 :: VersionedName(x, c)
    requires forall x | x in substMap.Keys :: exists c : nat :: c <= usedVars.1 && substMap[x] == VersionedName(x, c)
    ensures 
      forall x | x in substMap.Keys :: exists c : nat :: c <= usedVars.1 && substMap[x] == VersionedName(x, c)*/
  {
    match c
    case SimpleCmd(sc) => (SimpleCmd(SubstSimpleCmd(sc, substMap)), usedVars)
    case Break(_) => (c, usedVars)
    case Seq(c1, c2) => 
      var (c1', usedVars1') := DesugarScopedVars(c1, substMap, usedVars, seqSubstMap);
      var (c2', usedVars2') := DesugarScopedVars(c2, substMap, usedVars1', seqSubstMap);
      (Seq(c1', c2'), usedVars2')
    case Scope(optLabel, varDecls, body) =>
      var varDecls' := CreateUniqueVarDecls(varDecls, usedVars.0, usedVars.1);
      var usedVars' := (usedVars.0 + GetVarNames(varDecls'), usedVars.1 + |varDecls'|);
      var substMap' := substMap + ConvertVDeclsToSubstMap(varDecls, varDecls');
      var (body'', usedVars'') := DesugarScopedVars(body, substMap', usedVars', seqSubstMap);
      (Scope(optLabel, varDecls', body''), usedVars'')
    case If(None, thn, els) => 
      //TODO: make sure If(Some(...)) has been desugared
      var (thn', usedVars') := DesugarScopedVars(thn, substMap, usedVars, seqSubstMap);
      var (els', usedVars'') := DesugarScopedVars(els, substMap, usedVars', seqSubstMap);
      (If(None, thn', els'), usedVars'')
    case _ => (c, usedVars) //TODO (precondition should eliminate this case)
  }  


  lemma {:verify false} ResetVarsStateRel<A(!new)>(
    varMapping: map<var_name, var_name>, 
    vDecls1: seq<(var_name, Ty)>, 
    vDecls2: seq<(var_name, Ty)>, 
    sOrig1: state<A>,
    sOrig2: state<A>,
    s1: state<A>,
    s2: state<A>)
  requires Maps.Injective(varMapping)
  requires RelState(varMapping, sOrig1, sOrig2)
  requires RelState(varMapping, s1, s2)
  requires |vDecls1| == |vDecls2|
  requires (forall i | 0 <= i < |vDecls1| :: var (x,t) := vDecls1[i]; 
    x in varMapping.Keys && vDecls2[i].0 == varMapping[x] && vDecls2[i].1 == t)
  ensures RelState(varMapping, ResetVarsState(vDecls1, s1, sOrig1), ResetVarsState(vDecls2, s2, sOrig2))
  {
    if |vDecls1| == 0 {

    } else {
      var (x,t) := vDecls1[0];
      var (x',_) := vDecls2[0];
      assert varMapping[x] == x';

      var s1' := ResetVarsState(vDecls1[1..], s1, sOrig1);
      var s2' := ResetVarsState(vDecls2[1..], s2, sOrig2);


      assert x in sOrig1.Keys <==> x' in sOrig2.Keys by {
        reveal RelState();
      }

      assert RelState(varMapping, s1', s2') by {
        ResetVarsStateRel(varMapping, vDecls1[1..], vDecls2[1..], sOrig1, sOrig2, s1, s2);
      }

      if x in sOrig1.Keys {
        assert sOrig1[x] == sOrig2[x'] by {
          reveal RelState();
        }

        assert RelState(varMapping, s1'[x := sOrig1[x]], s2'[x' := sOrig2[x']]) by {
          RelStateUpdPreserve(varMapping, s1', s2', x, sOrig1[x]);
        }
      } else {
        assert RelState(varMapping, s1'-{x}, s2'-{x'}) by {
          RelStateRemovePreserve(varMapping, s1', s2', x);
        }
      }
    }
  }


  lemma {:verify false} ResetVarsStateRel2<A(!new)>(
    m: map<var_name, var_name>, 
    m': map<var_name, var_name>, 
    vDecls1: seq<(var_name, Ty)>, 
    vDecls2: seq<(var_name, Ty)>, 
    sOrig1: state<A>,
    sOrig2: state<A>,
    s1: state<A>,
    s2: state<A>)
  requires Maps.Injective(m)
  requires RelState(m, sOrig1, sOrig2)
  requires RelState(m', s1, s2)
  requires |vDecls1| == |vDecls2|
  requires (forall i | 0 <= i < |vDecls1| :: var (x,t) := vDecls1[i]; 
    x in m.Keys && vDecls2[i].0 == m[x] && vDecls2[i].1 == t)
  requires (forall x | x in m.Keys && x !in GetVarNames(vDecls1) :: x in m'.Keys && m'[x] == m[x])
  ensures RelState(m, ResetVarsState(vDecls1, s1, sOrig1), ResetVarsState(vDecls2, s2, sOrig2))
  {
      if |vDecls1| == 0 {
        assume false;

      } else {
        var (x,t) := vDecls1[0];
        var (x',_) := vDecls2[0];
        assert m[x] == x';

        var s1' := ResetVarsState(vDecls1[1..], s1, sOrig1);
        var s2' := ResetVarsState(vDecls2[1..], s2, sOrig2);


        assert x in sOrig1.Keys <==> x' in sOrig2.Keys by {
          reveal RelState();
        }

        assert RelState(m, s1', s2') by {
          ResetVarsStateRel2(m, m', vDecls1[1..], vDecls2[1..], sOrig1, sOrig2, s1, s2);
        }

        if x in sOrig1.Keys {
          assert sOrig1[x] == sOrig2[x'] by {
            reveal RelState();
          }

          assert RelState(m, s1'[x := sOrig1[x]], s2'[x' := sOrig2[x']]) by {
            RelStateUpdPreserve(m, s1', s2', x, sOrig1[x]);
          }
        } else {
          assert RelState(m, s1'-{x}, s2'-{x'}) by {
            RelStateRemovePreserve(m, s1', s2', x);
          }
        }
      }
    }

  /** 
  * The intuition of ResetVarsPredRel2 is that if we know RelPred(m, p1, p2), then we know that resetting
  * the variables in p1 and p2 yields predicates that are related to any injective map m that agrees with m on all
  * keys that are not reset. The variables that are reset are guaranteed to map to the same value in our setting.
  */

  lemma {:verify true} ResetVarsPredRel2<A(!new)>(
    a: absval_interp<A>, 
    m: map<var_name, var_name>, 
    m': map<var_name, var_name>, 
    vDecls1: seq<(var_name, Ty)>, 
    vDecls2: seq<(var_name, Ty)>, 
    p1: Predicate<A>, 
    p2: Predicate<A>,
    s1: state<A>,
    s2: state<A>)
  requires Maps.Injective(m)
  requires RelPred(m, p1, p2)
  requires RelState(m, s1, s2)
  requires |vDecls1| == |vDecls2|
  requires (forall i | 0 <= i < |vDecls1| :: var (x,t) := vDecls1[i]; 
    x in m.Keys && vDecls2[i].0 == m[x] && vDecls2[i].1 == t)
  requires (forall x | x in m.Keys && x !in GetVarNames(vDecls1) :: x in m'.Keys && m'[x] == m[x])
  ensures RelPred(m', ResetVarsPred(a, vDecls1, p1, s1), ResetVarsPred(a, vDecls2, p2, s2))
  {
    if |vDecls1| == 0 {
      assert ResetVarsPred(a, vDecls1, p1, s1) == p1;
      assert ResetVarsPred(a, vDecls2, p2, s1) == p2;
      //assume RelPred(m', p1, p2);
      assert MapGte(m', m) by {
        reveal MapGte();
      }

      RelPredLarger(m, m', p1, p2);
    } else {
      forall s, s' | RelState(m', s, s')
      ensures ResetVarsPred(a, vDecls1, p1, s1)(s) == ResetVarsPred(a, vDecls2, p2, s2)(s')
      { 
        calc {
          ResetVarsPred(a, vDecls1, p1, s1)(s);
          p1(ResetVarsState(vDecls1, s, s1));
          { ResetVarsStateRel2(m, m', vDecls1, vDecls2, s1, s2, s, s'); 
            reveal RelPred(); }
          p2(ResetVarsState(vDecls2, s', s2));
          ResetVarsPred(a, vDecls2, p2, s2)(s');
        }
      }

      reveal RelPred();
    }
  }


  lemma {:verify false} ResetVarsPredRel<A(!new)>(
    a: absval_interp<A>, 
    varMapping: map<var_name, var_name>, 
    vDecls1: seq<(var_name, Ty)>, 
    vDecls2: seq<(var_name, Ty)>, 
    p1: Predicate<A>, 
    p2: Predicate<A>,
    s1: state<A>,
    s2: state<A>)
  requires Maps.Injective(varMapping)
  requires RelPred(varMapping, p1, p2)
  requires RelState(varMapping, s1, s2)
  requires |vDecls1| == |vDecls2|
  requires (forall i | 0 <= i < |vDecls1| :: var (x,t) := vDecls1[i]; 
    x in varMapping.Keys && vDecls2[i].0 == varMapping[x] && vDecls2[i].1 == t)
  ensures RelPred(varMapping, ResetVarsPred(a, vDecls1, p1, s1), ResetVarsPred(a, vDecls2, p2, s2))
  {
    if |vDecls1| == 0 {
    } else {
      forall s, s' | RelState(varMapping, s, s')
      ensures ResetVarsPred(a, vDecls1, p1, s1)(s) == ResetVarsPred(a, vDecls2, p2, s2)(s')
      { 
        calc {
          ResetVarsPred(a, vDecls1, p1, s1)(s);
          p1(ResetVarsState(vDecls1, s, s1));
          { ResetVarsStateRel(varMapping, vDecls1, vDecls2, s1, s2, s, s'); 
            reveal RelPred(); }
          p2(ResetVarsState(vDecls2, s', s2));
          ResetVarsPred(a, vDecls2, p2, s2)(s');
        }
      }

      reveal RelPred();
    }
  }
   
 lemma {:verify false} DesugarScopedVarsCorrect<A(!new)>(
    a: absval_interp<A>,
    c: Cmd, 
    substMap: map<var_name, var_name>, 
    usedVars: (set<var_name>, nat),
    seqSubstMap: seq<(var_name, Ty)>,
    post1: WpPostShallow<A>,
    post2: WpPostShallow<A>)
  requires c.WellFormedVars(substMap.Keys)
  requires |seqSubstMap| == |substMap.Keys|
  requires Maps.Injective(substMap)
  requires 
    var (c', usedVars') := DesugarScopedVars(c, substMap, usedVars, seqSubstMap);
    && LabelsWellDefAux(c, post1.scopes.Keys) 
    && LabelsWellDefAux(c', post2.scopes.Keys)
    && RelPost(substMap, post1, post2)
  
  //requires forall vDecl | vDecls in seqSubstMap :: substMap(vDecl.) == sequSubstMap
  ensures 
    var (c', usedVars') := DesugarScopedVars(c, substMap, usedVars, seqSubstMap);
    RelPred(substMap, WpShallow(a, c, post1), WpShallow(a, c', post2))
  /** proof sketch notes:  
    for scopes case, will have to show that the updated substMap remains injective 
  */
 {
   reveal RelPost();
   match c {
    case SimpleCmd(sc) =>
      SubstSimpleCmdCorrect(a, sc, substMap, post1.normal, post2.normal);
    case Break(_) =>
    case Seq(c1, c2) => 
      var (c1', usedVars1') := DesugarScopedVars(c1, substMap, usedVars, seqSubstMap);
      var (c2', usedVars2') := DesugarScopedVars(c2, substMap, usedVars1', seqSubstMap);

      var post1' := WpPostShallow(WpShallow(a, c2, post1), post1.currentScope, post1.scopes);
      var post2' := WpPostShallow(WpShallow(a, c2', post2), post2.currentScope, post2.scopes);

      assert RelPost(substMap, post1', post2') by {
        assert RelPred(substMap, WpShallow(a, c2, post1), WpShallow(a, c2', post2)) by {
          DesugarScopedVarsCorrect(a, c2, substMap, usedVars1', seqSubstMap, post1, post2);
        }
      }

      assert RelPred(substMap, WpShallow(a, c1, post1'), WpShallow(a, c1', post2')) by {
        DesugarScopedVarsCorrect(a, c1, substMap, usedVars, seqSubstMap, post1', post2');
      }
    case Scope(optLabel, varDecls, body) => 
      /* Goal: RelPred(substMap, WpShallow(a, c, post1), WpShallow(a, c', post2)) */
      /*
      var updatedScopes := 
      
          post.scopes[optLabel.value := post.normal]
        else post.scopes;
      var unquantifiedBody := 
        assert updatedScopes.Keys == if optLabel.Some? then {optLabel.value} + post.scopes.Keys else post.scopes.Keys;
        var post' := WpPostShallow(post.normal, post.normal, updatedScopes);
        prevState => 
          WpShallow(a, body, ResetVarsPost(a, varDecls, post', prevState));
      
      s => ForallVarDeclsShallow(a, varDecls, unquantifiedBody(s))(s)
      */
      var varDecls' := CreateUniqueVarDecls(varDecls, usedVars.0, usedVars.1);
      var usedVars' := (usedVars.0 + GetVarNames(varDecls'), usedVars.1 + |varDecls'|);
      var substMap' := substMap + ConvertVDeclsToSubstMap(varDecls, varDecls');
      var (body'', usedVars'') := DesugarScopedVars(body, substMap', usedVars', seqSubstMap);
      //(Scope(optLabel, varDecls', body''), usedVars'')
      var c' := Scope(optLabel, varDecls', body'');

      var updatedScopes1 := 
        if optLabel.Some? then 
          post1.scopes[optLabel.value := post1.normal]
        else post1.scopes;

      var unquantifiedBody1 := 
        assert updatedScopes1.Keys == if optLabel.Some? then {optLabel.value} + post1.scopes.Keys else post1.scopes.Keys;
        var post1' := WpPostShallow(post1.normal, post1.normal, updatedScopes1);
        prevState => 
          WpShallow(a, body, ResetVarsPost(a, varDecls, post1', prevState));

      var updatedScopes2 := 
        if optLabel.Some? then 
          post1.scopes[optLabel.value := post1.normal]
        else post1.scopes;

      var unquantifiedBody2 := 
        assert updatedScopes2.Keys == if optLabel.Some? then {optLabel.value} + post1.scopes.Keys else post1.scopes.Keys;
        var post1' := WpPostShallow(post1.normal, post1.normal, updatedScopes2);
        prevState => 
          WpShallow(a, body'', ResetVarsPost(a, varDecls', post1', prevState));
      
      forall s, s' | RelState(substMap, s,s')
      ensures WpShallow(a, c, post1)(s) == WpShallow(a, c', post2)(s)
      {
        calc {

        }
      }

      assume false;
    case If(guard, thn, els) => assume false;
    case Loop(invariants, body) => assume false;
   }
 }

function method RemoveScopedVars(c: Cmd): (Cmd, (seq<(var_name, Ty)>))
  /*requires substMap.Values <= set c,x | x in substMap.Keys && 0 < c < usedVars.1 :: VersionedName(x, c)
  requires forall x | x in substMap.Keys :: exists c : nat :: c <= usedVars.1 && substMap[x] == VersionedName(x, c)
  ensures 
    forall x | x in substMap.Keys :: exists c : nat :: c <= usedVars.1 && substMap[x] == VersionedName(x, c)*/
{
  match c
  case SimpleCmd(sc) => (c, [])
  case Break(_) => (c, [])
  case Seq(c1, c2) => 
    var (c1', decls1) := RemoveScopedVars(c1);
    var (c2', decls2) := RemoveScopedVars(c2);
    (Seq(c1', c2'), decls1 + decls2)
  case Scope(optLabel, varDecls, body) =>
    var (body', declsBody) := RemoveScopedVars(body);
    (Scope(optLabel, [], body'), varDecls + declsBody)
  case If(None, thn, els) => 
    //TODO: make sure If(Some(...)) has been desugared
    var (thn', declsThn) := RemoveScopedVars(thn);
    var (els', declsEls) := RemoveScopedVars(els);
    (If(None, thn', els'), declsThn + declsEls)
  case _ => (c, []) //TODO (precondition should eliminate this case)
}

lemma {:verify false} RelStateRemoveScopedVarsCorrect<A(!new)>(a: absval_interp<A>, c: Cmd, post: WpPostShallow<A>)
  requires 
    var (c', decls) := RemoveScopedVars(c);
    LabelsWellDefAux(c, post.scopes.Keys) && LabelsWellDefAux(c', post.scopes.Keys)
  ensures 
    var (c', decls) := RemoveScopedVars(c);
    forall s :: WpShallow(a, c, post)(s) == ForallVarDeclsShallow(a, decls, WpShallow(a, c', ResetVarsPost(a, decls, post, s)))(s)
  /* almost the same as Scope(None, decls, body)
     Main difference is that currentScope is not updated.
     If show that body has no direct breaks, then it would be the same
  */

}