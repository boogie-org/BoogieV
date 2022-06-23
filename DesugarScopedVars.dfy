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

  predicate RelState<V>(m: map<var_name, (var_name, Ty)>, s1: map<var_name, V>, s2: map<var_name, V>)
  {
    && (forall k | k in m.Keys :: 
          && (k in s1.Keys <==> m[k].0 in s2.Keys)
          && (k in s1.Keys ==> s1[k] == s2[m[k].0]))
  }

  predicate RelPred<A(!new)>(m: map<var_name, (var_name, Ty)>, post1: Predicate<A>, post2: Predicate<A>)
  {
    forall s, s' | RelState(m, s, s') :: post1(s) == post2(s')
  }

  predicate RelPost<A(!new)>(m: map<var_name, (var_name, Ty)>, post1: WpPostShallow<A>, post2: WpPostShallow<A>)
  {
    && post1.scopes.Keys == post2.scopes.Keys
    && RelPred(m, post1.normal, post2.normal)
    && RelPred(m, post1.currentScope, post2.currentScope)
    && (forall lbl | lbl in post1.scopes.Keys :: RelPred(m, post1.scopes[lbl], post2.scopes[lbl]))
  }

  function method MultiSubstExpr(e: Expr, varMapping: map<var_name, (var_name, Ty)>): Expr

  lemma {:axiom} MultiSubstExprSpec<A(!new)>(a: absval_interp<A>, varMapping: map<var_name, (var_name, Ty)>, e: Expr, s1: state<A>, s2: state<A>)
    requires RelState(varMapping, s1, s2)
    requires forall x | x in e.FreeVars() :: x in varMapping.Keys || Maps.Get(s1, x) == Maps.Get(s2, x)
    ensures EvalExpr(a, e, s1) == EvalExpr(a, MultiSubstExpr(e, varMapping), s2)

  function method SubstSimpleCmd(sc: SimpleCmd, varMapping: map<var_name, (var_name, Ty)>) : SimpleCmd
  {
    match sc
    case Skip => Skip 
    case Assert(e) => Assert(MultiSubstExpr(e, varMapping))
    case Assume(e) => Assume(MultiSubstExpr(e, varMapping))
    case Assign(x, t, e) =>
      var newLHS := if x in varMapping.Keys then varMapping[x].0 else x;
      var newRHS := MultiSubstExpr(e, varMapping);
      Assign(newLHS, t, newRHS)
    case Havoc(varDecls) =>
      var varDecls' := Sequences.Map( 
        vDecl => 
          if vDecl.0 in varMapping.Keys then varMapping[vDecl.0] else vDecl

      Havoc(varDecls)
    case SeqSimple(c1, c2)  =>
      SeqSimple(SubstSimpleCmd(c1, varMapping), SubstSimpleCmd(c2, varMapping))
  }

  lemma {:axiom} SubstSimpleCmdCorrect<A>(a: absval_interp<A>, sc: SimpleCmd, varMapping: map<var_name, (var_name, Ty)>, post: WpPostShallow<A>)
  /*
  ensures 
    var sc' := SubstSimpleCmd(sc, varMapping);
    var freshNames := map k | k in varMapping.Keys :: varMapping[k].0;
    var updatedMap := map k | k in freshNames 

    forall s:state<A> :: WpShallowSimpleCmd(a, sc, post)(s) == WpShallowSimpleCmd(a, sc, post)()
  */


  function method CreateUniqueName(names: set<var_name>): var_name
    ensures CreateUniqueName(names) !in names


  /*
  function method {:opaque} FoldLeft<A,T>(f: (A, T) -> A, init: A, s: seq<T>): A
  {
    if |s| == 0 then init
    else FoldLeft(f, f(init, s[0]), s[1..])
  }
  */
/*
  lemma LemmaInvFoldRight<A,B>(inv: (seq<A>, B) -> bool,
                               stp: (A, B, B) -> bool,
                               f: (A, B) -> B,
                               b: B,
                               xs: seq<A>)
    requires InvFoldRight(inv, stp)
    requires forall a, b :: stp(a, b, f(a, b))
    requires inv([], b)
    ensures inv(xs, FoldRight(f, xs, b))
*/

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

  function method ConvertVDeclsToSubstMap(varDecls: seq<(var_name, Ty)>, varDecls': seq<(var_name, Ty)>) : map<var_name, (var_name, Ty)>
    requires |varDecls| == |varDecls'|
  {
    if |varDecls| == 0 then
      map[]
    else
      var oldName:= varDecls[0].0;
      var newVDecl := varDecls'[0];
      ConvertVDeclsToSubstMap(varDecls[1..], varDecls'[1..])[oldName := newVDecl]
  }

  /*
  * substMap: active variables that are mapped
  * freshVars: all fresh variable declarations
  */
  function method DesugarScopedVars(
    c: Cmd, 
    substMap: map<var_name, (var_name,Ty)>, 
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

  function RenameVarsState<V>(m: map<var_name, (var_name, Ty)>, s: map<var_name, V>) : map<var_name, V>
    ensures 
      var s' := RenameVarsState(m, s);
      && (forall v :: v in s.Keys && v !in m.Keys ==> s'[v] == s[v])
      && (forall v :: v in m.Keys && m[v].0 in s.Keys ==> s'[v] == s[m[v].0])
      && (forall v :: v in m.Keys && m[v].0 !in s.Keys ==> v !in s'.Keys)
  {
    var renamedState := 
      map v | v in m.Keys && m[v].0 in s.Keys :: 
        s[m[v].0];
    
    var renamedVarsWithNoTarget := set v | v in m.Keys && m[v].0 !in s.Keys;

    (s - renamedVarsWithNoTarget) + renamedState
  }

  function RenameVarsPred<A>(m: map<var_name, (var_name, Ty)>, p: Predicate<A>) : Predicate<A> 
  {
    s => p(RenameVarsState(m, s))
  }

  function RenameVarsPost<A>(m: map<var_name, (var_name, Ty)>, post: WpPostShallow<A>) : WpPostShallow<A>
  {
    var newScopes := map lbl | lbl in post.scopes.Keys :: RenameVarsPred(m, post.scopes[lbl]);
    WpPostShallow(RenameVarsPred(m, post.normal), RenameVarsPred(m, post.currentScope), newScopes)
  }

  lemma DesugarScopedVarsCorrect<A(!new)>(
    a: absval_interp<A>,
    c: Cmd, 
    substMap: map<var_name, (var_name,Ty)>, 
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