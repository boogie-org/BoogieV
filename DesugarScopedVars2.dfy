include "BoogieSemantics.dfy"
include "DesugarScopedVars.dfy"
include "dafny-libraries/src/Collections/Sequences/Seq.dfy"
include "dafny-libraries/src/Collections/Maps/Maps.dfy"

module DesugarScopedVars2 {

  import opened BoogieLang
  import opened BoogieSemantics
  import Sequences = Seq
  import Maps
  import Util
  import opened Wrappers
  import opened DesugarScopedVarsModule

  type MapOrig<V> = map<var_name, Option<V>>

  predicate {:opaque} RelState2<V>(m: map<var_name, var_name>, s1: map<var_name, V>, s2: map<var_name, V>, s2Orig: map<var_name, Option<V>>)
  {
    && (forall k | k in m.Keys :: Maps.Get(s1, k) == Maps.Get(s2, m[k]))
    && (forall k | k in s2Orig.Keys :: Maps.Get(s2, k) == s2Orig[k])
    && m.Values !! s2Orig.Keys
  }

  lemma RelStateLarger<V>(m: map<var_name, var_name>, m': map<var_name, var_name>, s1: map<var_name, V>, s2: map<var_name, V>, s2Orig: map<var_name, Option<V>>)
  requires RelState2(m', s1, s2, s2Orig)
  requires MapGte(m', m)
  ensures RelState2(m, s1, s2, s2Orig)
  {
    reveal MapGte();
    reveal RelState2();
  }

  predicate {:opaque} RelPred<A(!new)>(m: map<var_name, var_name>, post1: Predicate<A>, post2: Predicate<A>, s2Orig: MapOrig<Val<A>>)
  {
    forall s, s' | RelState2(m, s, s', s2Orig) :: post1(s) == post2(s')
  }

  predicate {:opaque} MapGte(m': map<var_name, var_name>, m: map<var_name, var_name>)
  {
    forall x | x in m.Keys :: x in m'.Keys && m[x] == m'[x]
  }

  lemma RelPredLarger<A(!new)>(m: map<var_name, var_name>, m': map<var_name, var_name>, post1: Predicate<A>, post2: Predicate<A>, s2Orig: MapOrig<Val<A>>)
  requires RelPred(m, post1, post2, s2Orig)
  requires MapGte(m', m)
  ensures RelPred(m', post1, post2, s2Orig)
  /*
  {
    reveal RelPred();
    forall s1,s2: map<var_name, Val<A>> | RelState2(m', s1, s2)
    ensures post1(s1) == post2(s2)
    {
      RelStateLarger(m, m', s1, s2);
    }
  }
  */

 lemma {:verify true} RelState2UpdPreserve<V>(varMapping: map<var_name, var_name>, s1: map<var_name, V>, s2: map<var_name, V>, s2Orig: MapOrig<V>, x: var_name, v: V)
 requires RelState2(varMapping, s1, s2, s2Orig)
 requires Maps.Injective(varMapping)
 requires x in varMapping.Keys
 ensures RelState2(varMapping, s1[x := v], s2[varMapping[x] := v], s2Orig)
 {
  reveal RelState2();
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

 lemma ConvertRelState<V>(m: map<var_name, var_name>, s1: map<var_name, V>, s2: map<var_name, V>, s2Orig: MapOrig<V>)
 requires RelState2(m, s1, s2, s2Orig)
 ensures RelState(m, s1, s2)
 {
  reveal RelState2();
  reveal RelState();
 }

 lemma {:verify true} {:induction false} ForallVarDeclsRelNew<A(!new)>(
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
      RelPred(varMapping, ForallVarDeclsShallow(a, varDecls, p1), ForallVarDeclsShallow(a, varDecls', p2), s2Orig)
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

      /*
      forall s1: map<var_name, Val<A>>, s2, v: Val<A> | RelState2(varMapping, s1, s2, s2Orig) && TypeOfVal(a, v) == t
        ensures ForallVarDeclsShallow(a, varDecls[1..], p1)(s1[x := v]) == ForallVarDeclsShallow(a, varDecls'[1..], p2)(s2[x' := v])
      {
        assert RelState2(varMapping, s1[x := v], s2[x' := v], s2Orig) by {
          RelState2UpdPreserve(varMapping, s1, s2, s2Orig, x, v);
        }

        ForallVarDeclsRelNew(a, varDecls[1..], varMapping, p1, p2, s2Orig);
        reveal RelPred();

        assert varDecls'[1..] == Sequences.Map(f, varDecls[1..]);
      }
      */

      assume false;

      //reveal ForallVarDeclsShallow();
    }
  }
 lemma {:verify true} ForallVarDeclsRelNew2<A(!new)>(
    a: absval_interp<A>, 
    varDecls: seq<(var_name, Ty)>, 
    varMapping: map<var_name, var_name>, 
    p1: Predicate<A>,
    p2: Predicate<A>,
    s1: state<A>,
    s2: state<A>,
    sOrig: MapOrig<Val<A>>)
    requires RelPred(varMapping, p1, p2, sOrig)
    requires RelState2(varMapping, s1, s2, sOrig)
    requires GetVarNames(varDecls) <= varMapping.Keys
    requires Maps.Injective(varMapping)
    ensures 
      var f := (vDecl : (var_name, Ty)) => 
          if vDecl.0 in varMapping.Keys then (varMapping[vDecl.0], vDecl.1) else vDecl;
      var varDecls' := Sequences.Map(f, varDecls);
      ForallVarDeclsShallow(a, varDecls, p1)(s1) ==  ForallVarDeclsShallow(a, varDecls', p2)(s2)
  {
    ForallVarDeclsRelNew(a, varDecls, varMapping, p1, p2, sOrig);
    reveal RelPred();
  }

 lemma {:verify true} {:induction false} SubstSimpleCmdCorrect<A(!new)>(a: absval_interp<A>, sc: SimpleCmd, varMapping: map<var_name, var_name>, 
    post1: Predicate<A>, post2: Predicate<A>, s2Orig: MapOrig<Val<A>>)
    requires RelPred(varMapping, post1, post2, s2Orig)
    requires sc.WellFormedVars(varMapping.Keys)
    requires Maps.Injective(varMapping)
    ensures 
      var sc' := SubstSimpleCmd(sc, varMapping);
      RelPred(varMapping, WpShallowSimpleCmd(a, sc, post1), WpShallowSimpleCmd(a, sc', post2), s2Orig)
  {
    var sc' := SubstSimpleCmd(sc, varMapping);
    var pre1 := WpShallowSimpleCmd(a, sc, post1);
    var pre2 := WpShallowSimpleCmd(a, sc', post2);
    forall s1:map<var_name, Val<A>>, s2 | RelState2(varMapping, s1, s2, s2Orig)
      ensures pre1(s1) == pre2(s2)
    {
      ConvertRelState(varMapping, s1, s2, s2Orig);
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
            reveal RelState();
            reveal RelState2();
            MultiSubstExprSpec2(a, varMapping, e, s1, s2);
          }

          if(v1Opt.Some?) {
            var v := v1Opt.value;
            var x' := varMapping[x];

            assert RelState2(varMapping, s1[x := v], s2[x' := v], s2Orig) by {
              RelState2UpdPreserve(varMapping, s1, s2, s2Orig, x, v);
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
            { ForallVarDeclsRelNew2(a, vDecls, varMapping, post1, post2, s1, s2, s2Orig); }
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
              assert RelPred(varMapping, post1', post2', s2Orig) by {
                SubstSimpleCmdCorrect(a, sc2, varMapping, post1, post2, s2Orig);
              }
              SubstSimpleCmdCorrect(a, sc1, varMapping, post1', post2', s2Orig); 
            }
            WpShallowSimpleCmd(a, sc1', post2')(s2);
            WpShallowSimpleCmd(a, SeqSimple(sc1', sc2'), post2)(s2);
          }
      }
    }
  }

  predicate {:opaque} RelPost<A(!new)>(m: map<var_name, var_name>, post1: WpPostShallow<A>, post2: WpPostShallow<A>, s2Orig: MapOrig<Val<A>>)
  {
    && post1.scopes.Keys == post2.scopes.Keys
    && RelPred(m, post1.normal, post2.normal, s2Orig)
    && RelPred(m, post1.currentScope, post2.currentScope, s2Orig)
    && (forall lbl | lbl in post1.scopes.Keys :: RelPred(m, post1.scopes[lbl], post2.scopes[lbl], s2Orig))
  }

 lemma {:verify true} DesugarScopedVarsCorrect<A(!new)>(
    a: absval_interp<A>,
    c: Cmd, 
    substMap: map<var_name, var_name>, 
    usedVars: (set<var_name>, nat),
    post1: WpPostShallow<A>,
    post2: WpPostShallow<A>,
    s2Orig: MapOrig<Val<A>>)
  requires c.WellFormedVars(substMap.Keys)
  requires Maps.Injective(substMap)
  requires 
    var (c', usedVars') := DesugarScopedVars(c, substMap, usedVars);
    && LabelsWellDefAux(c, post1.scopes.Keys) 
    && LabelsWellDefAux(c', post2.scopes.Keys)
    && RelPost(substMap, post1, post2, s2Orig)
  
  //requires forall vDecl | vDecls in seqSubstMap :: substMap(vDecl.) == sequSubstMap
  ensures 
    var (c', usedVars') := DesugarScopedVars(c, substMap, usedVars);
    RelPred(substMap, WpShallow(a, c, post1), WpShallow(a, c', post2), s2Orig)
  /** proof sketch notes:  
    for scopes case, will have to show that the updated substMap remains injective 
  */
 {
   reveal RelPost();
   match c {
    case SimpleCmd(sc) =>
      reveal WpShallow();
      SubstSimpleCmdCorrect(a, sc, substMap, post1.normal, post2.normal, s2Orig);
    case Break(_) => reveal WpShallow();
    case Seq(c1, c2) => 
      var (c1', usedVars1') := DesugarScopedVars(c1, substMap, usedVars);
      var (c2', usedVars2') := DesugarScopedVars(c2, substMap, usedVars1');

      var post1' := WpPostShallow(WpShallow(a, c2, post1), post1.currentScope, post1.scopes);
      var post2' := WpPostShallow(WpShallow(a, c2', post2), post2.currentScope, post2.scopes);

      assert RelPost(substMap, post1', post2', s2Orig) by {
        assert RelPred(substMap, WpShallow(a, c2, post1), WpShallow(a, c2', post2), s2Orig) by {
          DesugarScopedVarsCorrect(a, c2, substMap, usedVars1', post1, post2, s2Orig);
        }
      }

      assert RelPred(substMap, WpShallow(a, c1, post1'), WpShallow(a, c1', post2'), s2Orig) by {
        DesugarScopedVarsCorrect(a, c1, substMap, usedVars, post1', post2', s2Orig);
      }

      reveal WpShallow();
    case Scope(optLabel, varDecls, body) => 
      assume false;
      /* Goal: RelPred(substMap, WpShallow(a, c, post1), WpShallow(a, c', post2)) */
      var varDecls' := CreateUniqueVarDecls(varDecls, usedVars.0, usedVars.1);
      var usedVars' := (usedVars.0 + GetVarNames(varDecls'), usedVars.1 + |varDecls'|);
      var substMap' := substMap + ConvertVDeclsToSubstMap(varDecls, varDecls');
      assert substMap'.Keys == GetVarNames(varDecls)+substMap.Keys;
      var (body', usedVars'') := DesugarScopedVars(body, substMap', usedVars');
      //(Scope(optLabel, varDecls', body''), usedVars'')
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
      
      var post1' := WpPostShallow(post1.normal, post1.normal, updatedScopes1);
      var post2' := WpPostShallow(post2.normal, post2.normal, updatedScopes2);

      forall s1,s2 | RelState2(substMap, s1, s2, s2Orig)
      ensures WpShallow(a, c, post1)(s1) == WpShallow(a, c', post2)(s2)
      {
        var s2Orig' := s2Orig + map l | l in GetVarNames(varDecls) :: if l in substMap.Keys then Maps.Get(s2, substMap[l]) else None;

        calc {
          WpShallow(a, Scope(optLabel, varDecls, body), post1)(s1);
          {reveal WpShallow();}
          ForallVarDeclsShallow(a, varDecls, WpShallow(a, body, ResetVarsPost(varDecls, post1', s1)))(s1);
          { 
            assert RelPost(substMap', ResetVarsPost(varDecls, post1', s1), ResetVarsPost(varDecls', post2', s2), s2Orig') by 
            { assume false; }

            assert Maps.Injective(substMap') by {
              assume false;
            }

            assert RelPred(substMap', 
              WpShallow(a, body, ResetVarsPost(varDecls, post1', s1)), 
              WpShallow(a, body', ResetVarsPost(varDecls', post2', s2)),
              s2Orig') by
              { 
                DesugarScopedVarsCorrect(
                  a, body, substMap', usedVars',  ResetVarsPost(varDecls, post1', s1), ResetVarsPost(varDecls', post2', s2), s2Orig'
                ); 
              }

            /*
            assert RelPred(substMap, 
              ForallVarDeclsShallow(a, varDecls, WpShallow(a, body, ResetVarsPost(varDecls, post1', s1))), 
              ForallVarDeclsShallow(a, varDecls', WpShallow(a, body', ResetVarsPost(varDecls', post2', s2)))) by
              { ForallRel lemma }
            
            //conclusion by 
            { RelPred definition using that RelState2(substMap, s1, s2) }
            */
            assume false;
          }
          ForallVarDeclsShallow(a, varDecls', WpShallow(a, body', ResetVarsPost(varDecls', post2', s2)))(s2);
          {reveal WpShallow();}
          WpShallow(a, Scope(optLabel, varDecls', body'), post2)(s2);
        }
      }

      reveal RelPred();
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
    forall s :: WpShallow(a, c, post)(s) == ForallVarDeclsShallow(a, decls, WpShallow(a, c', ResetVarsPost(decls, post, s)))(s)
  /* almost the same as Scope(None, decls, body)
     Main difference is that currentScope is not updated.
     If show that body has no direct breaks, then it would be the same
  */

}