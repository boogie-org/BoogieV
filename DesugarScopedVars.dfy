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

  predicate RelState<V>(m: map<var_name, var_name>, s1: map<var_name, V>, s2: map<var_name, V>)
  {
    (forall k | k in m.Keys :: Maps.Get(s1, k) == Maps.Get(s2, m[k]))
  }

  lemma RelStateEmpty<V>(s1: map<var_name, V> , s2: map<var_name, V>)
  ensures RelState(map[], s1, s2)
  { }

  predicate RelPred<A(!new)>(m: map<var_name, var_name>, post1: Predicate<A>, post2: Predicate<A>)
  {
    forall s, s' | RelState(m, s, s') :: post1(s) == post2(s')
  }

  predicate RelPost<A(!new)>(m: map<var_name, var_name>, post1: WpPostShallow<A>, post2: WpPostShallow<A>)
  {
    && post1.scopes.Keys == post2.scopes.Keys
    && RelPred(m, post1.normal, post2.normal)
    && RelPred(m, post1.currentScope, post2.currentScope)
    && (forall lbl | lbl in post1.scopes.Keys :: RelPred(m, post1.scopes[lbl], post2.scopes[lbl]))
  }

  function method MultiSubstExpr(e: Expr, varMapping: map<var_name, var_name>): Expr

  lemma MultiSubstExprSpec<A(!new)>(a: absval_interp<A>, varMapping: map<var_name, var_name>, e: Expr, s1: state<A>, s2: state<A>)
    requires forall x | x in e.FreeVars() :: 
      && (x in varMapping.Keys ==> Maps.Get(s1, x) == Maps.Get(s2, varMapping[x]))
      && (x !in varMapping.Keys ==> Maps.Get(s1, x) == Maps.Get(s2, x))
    ensures EvalExpr(a, e, s1) == EvalExpr(a, MultiSubstExpr(e, varMapping), s2)
  
  lemma MultiSubstExprSpec2<A(!new)>(a: absval_interp<A>, varMapping: map<var_name, var_name>, e: Expr, s1: state<A>, s2: state<A>)
    requires RelState(varMapping, s1, s2)
    requires e.FreeVars() <= varMapping.Keys
    ensures EvalExpr(a, e, s1) == EvalExpr(a, MultiSubstExpr(e, varMapping), s2)
  {
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
      var varDecls' := Sequences.Map( 
        (vDecl : (var_name, Ty)) => 
          if vDecl.0 in varMapping.Keys then (varMapping[vDecl.0], vDecl.1) else vDecl,
        varDecls);
      Havoc(varDecls')
    case SeqSimple(c1, c2)  =>
      SeqSimple(SubstSimpleCmd(c1, varMapping), SubstSimpleCmd(c2, varMapping))
  }

  lemma ForallVarDeclsRel<A(!new)>(
    a: absval_interp<A>, 
    varDecls: seq<(var_name, Ty)>, 
    varMapping: map<var_name, var_name>, 
    p1: Predicate<A>,
    p2: Predicate<A>)
    requires RelPred(varMapping, p1, p2)
    requires GetVarNames(varDecls) <= varMapping.Keys
    ensures 
      var varDecls' := Sequences.Map((vDecl : (var_name, Ty)) => (varMapping[vDecl.0], vDecl.1), varDecls);
      RelPred(varMapping, ForallVarDeclsShallow(a, varDecls, p1), ForallVarDeclsShallow(a, varDecls, p2))
  {
    forall s1, s2 | RelState(varMapping, s1, s2)
    ensures ForallVarDeclsShallow(a, varDecls, p1)(s1) == ForallVarDeclsShallow(a, varDecls, p2)(s2)
    {
      if |varDecls| > 0 {

      }
    }
  }

  lemma SubstSimpleCmdCorrect<A(!new)>(a: absval_interp<A>, sc: SimpleCmd, varMapping: map<var_name, var_name>, 
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
      match sc
      case Assume(e) => 
        MultiSubstExprSpec2(a, varMapping, e, s1, s2);
      case Assert(e) => 
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
            forall k | k in varMapping.Keys 
            ensures Maps.Get(s1[x := v], k) == Maps.Get(s2[x' := v], varMapping[k])
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
        }
      case Havoc(vDecls)  => 

      case _ => assume false;
    }
  }


  function method CreateUniqueName(names: set<var_name>): var_name
    ensures CreateUniqueName(names) !in names

  function method CreateUniqueVarDecls(varDecls: seq<(var_name, Ty)>, usedNames: set<var_name>) : seq<(var_name,Ty)>
    ensures 
      var res := CreateUniqueVarDecls(varDecls, usedNames);
      |varDecls| == |res|
  {
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

    res
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
    usedVars: set<var_name>,
    ghost seqSubstMap: seq<(var_name, Ty)>): (Cmd, set<var_name>)
  {
    match c
    case SimpleCmd(sc) => (SimpleCmd(SubstSimpleCmd(sc, substMap)), usedVars)
    case Break(_) => (c, usedVars)
    case Seq(c1, c2) => 
      var (c1', usedVars1') := DesugarScopedVars(c1, substMap, usedVars, seqSubstMap);
      var (c2', usedVars2') := DesugarScopedVars(c2, substMap, usedVars1', seqSubstMap);
      (Seq(c1', c2'), usedVars2')
    case Scope(optLabel, varDecls, body) =>
      var varDecls' := CreateUniqueVarDecls(varDecls, usedVars);
      var usedVars' := usedVars + GetVarNames(varDecls');
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

  lemma DesugarScopedVarsCorrect<A(!new)>(
    a: absval_interp<A>,
    c: Cmd, 
    substMap: map<var_name, var_name>, 
    usedVars: set<var_name>,
    seqSubstMap: seq<(var_name, Ty)>,
    post1: WpPostShallow<A>,
    post2: WpPostShallow<A>,
    s: state<A>)
  requires |seqSubstMap| == |substMap.Keys|
  requires 
    var (c', usedVars') := DesugarScopedVars(c, substMap, usedVars, seqSubstMap);
    && LabelsWellDefAux(c, post1.scopes.Keys) 
    && LabelsWellDefAux(c', post2.scopes.Keys)
    && RelPost(substMap, post1, post2)
  
  //requires forall vDecl | vDecls in seqSubstMap :: substMap(vDecl.) == sequSubstMap
  ensures 
    var (c', usedVars') := DesugarScopedVars(c, substMap, usedVars, seqSubstMap);
    RelPred(substMap, WpShallow(a, c, post1), WpShallow(a, c', post2))

}