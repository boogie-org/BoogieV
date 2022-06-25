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

 lemma {:verify false} RelStateEmpty<V>(s1: map<var_name, V> , s2: map<var_name, V>)
  ensures RelState(map[], s1, s2)
 { reveal RelState(); }

  predicate {:opaque} RelPred<A(!new)>(m: map<var_name, var_name>, post1: Predicate<A>, post2: Predicate<A>)
  {
    forall s, s' | RelState(m, s, s') :: post1(s) == post2(s')
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
          RelStatePreserve(varMapping, s1, s2, x, v);
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

 lemma {:verify false} RelStatePreserve<V>(varMapping: map<var_name, var_name>, s1: map<var_name, V>, s2: map<var_name, V>, x: var_name, v: V)
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
              RelStatePreserve(varMapping, s1, s2, x, v);
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
              assert RelPred(varMapping, post1', post2') by{
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
    name + Util.NatToString(n) + SEP
  }

  function method CreateUniqueVarDecls(varDecls: seq<(var_name, Ty)>, usedNames: set<var_name>, counter: nat) : seq<(var_name,Ty)>
    ensures 
      var res := CreateUniqueVarDecls(varDecls, usedNames, counter);
      |varDecls| == |res|
  {
    /*
    var f := (varDecl:(var_name, Ty), res: seq<(var_name, Ty)>) => (
      var (x, t) := varDecl;

      var allUsedNames := usedNames + GetVarNames(res);
      var xFresh := if x !in allUsedNames then x else CreateUniqueName(allUsedNames);
      ([(xFresh, t)]+res)
    );

    var inv := (xs: seq<(var_name,Ty)>, ys: seq<(var_name,Ty)>) => |xs| == |ys|;
    var step := (a: (var_name,Ty), b: seq<(var_name, Ty)>, c: seq<(var_name, Ty)>) => |c| == |b|+1;

    Sequences.LemmaInvFoldRight(inv, step, f, [], varDecls);

    var res := Sequences.FoldRight(f, varDecls, []);
    */

    /** TODO
      Currently, a suffix is added to every variable even if there are no clashes. 
      This makes it harder to read the target output. It would be nice if one could 
      reuse a name if it does not clash with anything else that has been so far. 
      Doing this would require a fold to avoid updating the counter if a name is 
      reused.
     */

    // DISCUSS
    seq(|varDecls|, i => (VersionedName(varDecls[i].0, counter+i), varDecls[i].1))
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
      var (body'', usedVars'') := DesugarScopedVars(body, substMap, usedVars', seqSubstMap);
      (Scope(optLabel, varDecls', body''), usedVars'')
    case If(None, thn, els) => 
      //TODO: make sure If(Some(...)) has been desugared
      var (thn', usedVars') := DesugarScopedVars(thn, substMap, usedVars, seqSubstMap);
      var (els', usedVars'') := DesugarScopedVars(els, substMap, usedVars', seqSubstMap);
      (If(None, thn', els'), usedVars'')
    case _ => (c, usedVars) //TODO (precondition should eliminate this case)
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

  lemma RemoveScopedVarsCorrect<A(!new)>(a: absval_interp<A>, c: Cmd, post: WpPostShallow<A>)
    requires 
      var (c', decls) := RemoveScopedVars(c);
      LabelsWellDefAux(c, post.scopes.Keys) && LabelsWellDefAux(c', post.scopes.Keys)
    ensures 
      var (c', decls) := RemoveScopedVars(c);
      forall s :: WpShallow(a, c, post)(s) == ForallVarDeclsShallow(a, decls, WpShallow(a, c', ResetVarsPost(a, decls, post, s)))(s)
  
  /*
  lemma ScopeNoneSemantics<A(!new)>(a: absval_interp<A>, varDecls: seq<(var_name, Ty)>, body: Cmd, post: WpPostShallow<A>)
      requires LabelsWellDefAux(body, post.scopes.Keys)
    ensures
      forall s : state<A> :: 
        WpShallow(a, Scope(None, varDecls, body), post)(s) ==
        ForallVarDeclsShallow(a, varDecls, WpShallow(a, body, ResetVarsPost(a, varDecls, WpPostShallow(post.normal, post.normal, post.scopes), s)))(s)
    { 
      assume false;
    }
  */

  lemma ScopeSemantics<A(!new)>(a: absval_interp<A>, optLabel: Option<lbl_name>, varDecls: seq<(var_name, Ty)>, body: Cmd, post: WpPostShallow<A>, s: state<A>)
    requires LabelsWellDefAux(Scope(optLabel, varDecls, body), post.scopes.Keys)
    ensures
        WpShallow(a, Scope(optLabel, varDecls, body), post)(s) ==
        ForallVarDeclsShallow(a, varDecls, WpShallow(a, Scope(optLabel, [], body), ResetVarsPost(a, varDecls, post, s)))(s)
  {
      var updatedScopes := 
        if optLabel.Some? then 
          post.scopes[optLabel.value := post.normal]
        else post.scopes;

    assert updatedScopes.Keys == if optLabel.Some? then {optLabel.value} + post.scopes.Keys else post.scopes.Keys;
    var post' := WpPostShallow(post.normal, post.normal, updatedScopes);
    calc {
      WpShallow(a, Scope(optLabel, varDecls, body), post)(s);
      ForallVarDeclsShallow(a, varDecls, WpShallow(a, body, ResetVarsPost(a, varDecls, post', s)))(s);
      { assert ResetVarsPost(a, [], ResetVarsPost(a, varDecls, post', s), s) == ResetVarsPost(a, varDecls, post', s); }
      ForallVarDeclsShallow(a, varDecls, WpShallow(a, body, ResetVarsPost(a, [], ResetVarsPost(a, varDecls, post', s), s)))(s);
      ForallVarDeclsShallow(a, varDecls, WpShallow(a, Scope(optLabel, [], body), ResetVarsPost(a, varDecls, post, s)))(s);
    }
  }
   

  function RenameVarsState<V>(m: map<var_name, var_name>, s: map<var_name, V>) : map<var_name, V>
    ensures 
      var s' := RenameVarsState(m, s);
      && (forall v :: v in s.Keys && v !in m.Keys ==> s'[v] == s[v])
      && (forall v :: v in m.Keys && m[v] in s.Keys ==> s'[v] == s[m[v]])
      && (forall v :: v in m.Keys && m[v] !in s.Keys ==> v !in s'.Keys)
  {
    var renamedState := 
      map v | v in m.Keys && m[v] in s.Keys :: 
        s[m[v]];
    
    var renamedVarsWithNoTarget := set v | v in m.Keys && m[v] !in s.Keys;

    (s - renamedVarsWithNoTarget) + renamedState
  }

  function RenameVarsPred<A>(m: map<var_name, var_name>, p: Predicate<A>) : Predicate<A> 
  {
    s => p(RenameVarsState(m, s))
  }

  function RenameVarsPost<A>(m: map<var_name, var_name>, post: WpPostShallow<A>) : WpPostShallow<A>
  {
    var newScopes := map lbl | lbl in post.scopes.Keys :: RenameVarsPred(m, post.scopes[lbl]);
    WpPostShallow(RenameVarsPred(m, post.normal), RenameVarsPred(m, post.currentScope), newScopes)
  }

 lemma {:verify true} DesugarScopedVarsCorrect<A(!new)>(
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
    case Scope(labelName, varDecls, body) => assume false;
    case If(guard, thn, els) => assume false;
    case Loop(invariants, body) => assume false;
   }
 }


}