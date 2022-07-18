include "../lang/BoogieSemantics.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"
include "../dafny-libraries/src/Collections/Maps/Maps.dfy"
include "../util/Naming.dfy"
include "../util/AstSubsetPredicates.dfy"

module DesugarScopedVarsImpl {

  import opened BoogieLang
  import opened BoogieSemantics
  import Sequences = Seq
  import Maps
  import Util
  import opened Wrappers
  import opened Naming
  import opened AstSubsetPredicates

  function method CreateUniqueVarDecls(varDecls: seq<(var_name, Ty)>, counter: nat) : seq<(var_name,Ty)>
    ensures 
      var varDecls' := CreateUniqueVarDecls(varDecls, counter);
      && |varDecls'| == |varDecls|
      && GetVarNames(varDecls') <= VarNameSet(GetVarNames(varDecls), counter, counter + |varDecls|)
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
    var res := seq(|varDecls|, i requires 0 <= i < |varDecls| => (VersionedName(varDecls[i].0, counter+i), varDecls[i].1));
    assert GetVarNames(res) <= VarNameSet(GetVarNames(varDecls), counter, counter + |varDecls|) by {
      /** we reveal VarNameSet() inside this by clause, because if it's done outside by clause, then
          VarNameSet() is revealed to all callers of this function (this behaviour is a bug, see 
          https://github.com/dafny-lang/dafny/issues/1382) 
      */
      reveal VarNameSet();
    }
    res
  }

  lemma CreateUniqueVarDeclsNoDup(varDecls: seq<(var_name, Ty)>, counter: nat)
    ensures 
      var varDecls' := CreateUniqueVarDecls(varDecls, counter);
      Sequences.HasNoDuplicates(GetVarNamesSeq(varDecls'))
  {
    var varDecls' := CreateUniqueVarDecls(varDecls, counter);
    var varNames' := GetVarNamesSeq(varDecls');
    forall i, j | 0 <= i < |varNames'| && 0 <= j < |varNames'| && i != j
    ensures varNames'[i] != varNames'[j]
    {
      calc {
        varNames'[i];
        VersionedName(varDecls[i].0, counter+i);
      != { VersionedNameInjective(varDecls[i].0, varDecls[j].0, counter+i, counter+j); }
        VersionedName(varDecls[j].0, counter+j);
        varNames'[j];
      }
    }
    reveal Sequences.HasNoDuplicates();
  }

  function method ConvertVDeclsToSubstMap(varDecls: seq<(var_name, Ty)>, varDecls': seq<(var_name, Ty)>) : map<var_name, var_name>
    requires |varDecls| == |varDecls'|
    ensures 
      var res := ConvertVDeclsToSubstMap(varDecls, varDecls');
      && res.Keys == GetVarNames(varDecls)
      && res.Values <= GetVarNames(varDecls')
  {
    if |varDecls| == 0 then
      map[]
    else
      var oldName:= varDecls[0].0;
      var newName := varDecls'[0].0;
      var m' := ConvertVDeclsToSubstMap(varDecls[1..], varDecls'[1..]);
      var m := m'[oldName := newName];
      assert m.Values <= {newName} + GetVarNames(varDecls'[1..]);
      m
  }

  /*
  * substMap: active variables that are mapped
  * freshVars: all fresh variable declarations
  */
  function method MakeScopedVarsUnique(
    c: Cmd, 
    substMap: map<var_name, var_name>, 
    counter: nat): (Cmd, nat)
    ensures
      var (_, counter') := MakeScopedVarsUnique(c, substMap, counter);
      counter <= counter'
  {
    match c
    case SimpleCmd(sc) => (SimpleCmd(sc.SubstSimpleCmd(substMap)), counter)
    case Break(_) => (c, counter)
    case Seq(c1, c2) => 
      var (c1', counter1') := MakeScopedVarsUnique(c1, substMap, counter);
      var (c2', counter2') := MakeScopedVarsUnique(c2, substMap, counter1');
      (Seq(c1', c2'), counter2')
    case Scope(optLabel, varDecls, body) =>
      var varDecls' := CreateUniqueVarDecls(varDecls, counter);
      var counter' := counter + |varDecls'|;
      var substMap' := substMap + ConvertVDeclsToSubstMap(varDecls, varDecls');
      var (body'', counter'') := MakeScopedVarsUnique(body, substMap', counter');
      (Scope(optLabel, varDecls', body''), counter'')
    case If(None, thn, els) => 
      //TODO: make sure If(Some(...)) has been desugared
      var (thn', counter') := MakeScopedVarsUnique(thn, substMap, counter);
      var (els', counter'') := MakeScopedVarsUnique(els, substMap, counter');
      (If(None, thn', els'), counter'')
    case _ => (c, counter) //TODO (precondition should eliminate this case)
  }   

  function method RemoveScopedVarsAux(c: Cmd): (Cmd, seq<VarDecl>)
    /*requires substMap.Values <= set c,x | x in substMap.Keys && 0 < c < usedVars.1 :: VersionedName(x, c)
    requires forall x | x in substMap.Keys :: exists c : nat :: c <= usedVars.1 && substMap[x] == VersionedName(x, c)
    ensures 
      forall x | x in substMap.Keys :: exists c : nat :: c <= usedVars.1 && substMap[x] == VersionedName(x, c)*/
  {
    match c
    case SimpleCmd(sc) => (c, [])
    case Break(_) => (c, [])
    case Seq(c1, c2) => 
      var (c1', decls1) := RemoveScopedVarsAux(c1);
      var (c2', decls2) := RemoveScopedVarsAux(c2);
      (Seq(c1', c2'), decls1 + decls2)
    case Scope(optLabel, varDecls, body) =>
      var (body', declsBody) := RemoveScopedVarsAux(body);
      (Scope(optLabel, [], body'), varDecls + declsBody)
    case If(None, thn, els) => 
      //TODO: make sure If(Some(...)) has been desugared
      var (thn', declsThn) := RemoveScopedVarsAux(thn);
      var (els', declsEls) := RemoveScopedVarsAux(els);
      (If(None, thn', els'), declsThn + declsEls)
    case _ => (c, []) //TODO (precondition should eliminate this case)
  }

  function method RemoveScopedVars(c: Cmd) : (Cmd, seq<VarDecl>)
  {
    var (cUnique, _) := MakeScopedVarsUnique(c, map[], 0);
    var (c', decls) := RemoveScopedVarsAux(cUnique);
    (c', decls)
  }

  lemma MakeScopedVarsUniquePreserveStructure(c: Cmd, substMap: map<var_name, var_name>, counter: nat)
    requires NoLoopsNoIfGuard(c) && NoBreaks(c)
    ensures 
      var (c', _) := MakeScopedVarsUnique(c, substMap, counter);
      NoLoopsNoIfGuard(c') && NoBreaks(c')
  { }

  lemma RemoveScopedVarsAuxPreserveStructure(c: Cmd)
    requires NoLoopsNoIfGuard(c) && NoBreaks(c)
    ensures NoLoopsNoIfGuardNoScopedVars(RemoveScopedVarsAux(c).0) && NoBreaks(RemoveScopedVarsAux(c).0)
  { }

  lemma RemoveScopedVarsStructure(c: Cmd)
    requires NoLoopsNoIfGuard(c) && NoBreaks(c)
    ensures NoLoopsNoIfGuardNoScopedVars(RemoveScopedVars(c).0) && NoBreaks(RemoveScopedVars(c).0)
  { 
    var (cUnique, _) := MakeScopedVarsUnique(c, map[], 0);
    MakeScopedVarsUniquePreserveStructure(c, map[], 0);
    RemoveScopedVarsAuxPreserveStructure(cUnique);
  }

  function GetDecls(c: Cmd) : seq<VarDecl>
  {
    match c
    case SimpleCmd(sc) => []
    case Break(_) => []
    case Seq(c1, c2) => 
      var decls1 := GetDecls(c1);
      var decls2 := GetDecls(c2);
      decls1 + decls2
    case Scope(optLabel, varDecls, body) =>
      var declsBody := GetDecls(body);
      varDecls + declsBody
    case If(_, thn, els) => 
      //TODO: make sure If(Some(...)) has been desugared
      var declsThn := GetDecls(thn);
      var declsEls := GetDecls(els);
      declsThn + declsEls
    case Loop(_, body) => GetDecls(body)
  }

  /** TODO */
  lemma UniqueVars(c: Cmd, substMap: map<var_name, var_name>, counter: nat)
    requires 
      var (c',_) := MakeScopedVarsUnique(c, substMap, counter);
      && NoLoopsNoIfGuard(c)
      && NoLoopsNoIfGuard(c')
    ensures 
      var (c', counter') := MakeScopedVarsUnique(c, substMap, counter);
      && Sequences.HasNoDuplicates(GetVarNamesSeq(GetDecls(c')))
      && (iset s | s in GetVarNamesSeq(GetDecls(c'))) <= (iset i: nat, s: string | counter <= i < counter :: VersionedName(s, i))
      && counter <= counter'
  { 
    match c
    case SimpleCmd(sc) =>   
      reveal Sequences.HasNoDuplicates();
      //(SimpleCmd(sc.SubstSimpleCmd(substMap)), counter)
    case Break(_) => 
      reveal Sequences.HasNoDuplicates();
      //(c, counter)
    case Seq(c1, c2) => 
      /*
      var (c1', counter1') := MakeScopedVarsUnique(c1, substMap, counter);
      var (c2', counter2') := MakeScopedVarsUnique(c2, substMap, counter1');
      (Seq(c1', c2'), counter2')
      */
      var (c1', counter1') := MakeScopedVarsUnique(c1, substMap, counter);
      var (c2', counter2') := MakeScopedVarsUnique(c2, substMap, counter1');

      assert (set s | s in GetVarNamesSeq(GetDecls(c1'))) !! (set s | s in GetVarNamesSeq(GetDecls(c2')));
        calc {
          GetVarNamesSeq(GetDecls(Seq(c1',c2')));
          GetVarNamesSeq(GetDecls(c1')+GetDecls(c2'));
          GetVarNamesSeq(GetDecls(c1'))+GetVarNamesSeq(GetDecls(c2'));
        }

      Util.HasNoDuplicatesAppDisj2(GetVarNamesSeq(GetDecls(c1')), GetVarNamesSeq(GetDecls(c2')));

      var temp := (iset i: nat, s: string | counter <= i < counter2' :: VersionedName(s, i));
      assert (iset s | s in GetVarNamesSeq(GetDecls(c1')))+(iset s | s in GetVarNamesSeq(GetDecls(c2'))) <= temp;
    case Scope(optLabel, varDecls, body) =>
      assume false;
      /*
      var varDecls' := CreateUniqueVarDecls(varDecls, counter);
      var counter' := counter + |varDecls'|;
      var substMap' := substMap + ConvertVDeclsToSubstMap(varDecls, varDecls');
      var (body'', counter'') := MakeScopedVarsUnique(body, substMap', counter');
      (Scope(optLabel, varDecls', body''), counter'')
      */
    case If(None, thn, els) => 
      assume false;
      /*
      //TODO: make sure If(Some(...)) has been desugared
      var (thn', counter') := MakeScopedVarsUnique(thn, substMap, counter);
      var (els', counter'') := MakeScopedVarsUnique(els, substMap, counter');
      (If(None, thn', els'), counter'')
      */
  
  }

}