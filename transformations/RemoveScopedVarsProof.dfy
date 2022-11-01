include "../lang/BoogieSemantics.dfy"
include "../transformations/DesugarScopedVarsImpl.dfy"
include "../transformations/MakeScopedVarsUniqueProof.dfy"
include "../transformations/RemoveScopedVarsAuxProof.dfy"
include "../util/Naming.dfy"
include "../util/SemanticsUtil.dfy"
include "../util/ForallAppend.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"
include "../dafny-libraries/src/Collections/Maps/Maps.dfy"
include "../util/AstSubsetPredicates.dfy"

module RemoveScopedVarsProof
{
  import opened BoogieLang
  import opened BoogieSemantics
  import opened SemanticsUtil
  import Sequences = Seq
  import Maps
  import Util
  import opened Wrappers
  import opened DesugarScopedVarsImpl
  import opened Naming
  import ForallAppend
  import opened AstSubsetPredicates

  import opened MakeScopedVarsUniqueProof
  import opened RemoveScopedVarsAuxProof
    
  lemma RemoveScopedVarsCorrect<A(!new)>(a: absval_interp<A>, tcons: set<tcon_name>, activeVars: set<var_name>, c: Cmd)
    requires 
      var (c', decls) := RemoveScopedVarsAux(c);
      && LabelsWellDefAux(c, TruePost<A>().scopes.Keys) 
      && LabelsWellDefAux(c', TruePost<A>().scopes.Keys) 
      && c.WellFormedVars({}) 
      && WfAbsvalInterp(a, tcons)
      && c.WellFormedTypes(tcons)
      && c.NoBinders()
      && NoLoopsNoIfGuard(c)
      && NoLoopsNoIfGuard(c')
      && activeVars !! GetVarNames(decls)
    ensures 
      var (c', decls) := RemoveScopedVars(c);
      && LabelsWellDefAux(c', TruePost<A>().scopes.Keys)
      && (forall s :: WpCmd(a, c, TruePost())(s) == ForallVarDecls(a, decls, WpCmd(a, c', TruePost()))(s))
    {
        var (cUnique, _) := MakeScopedVarsUnique(c, map[], 0);
        var (c', decls) := RemoveScopedVarsAux(cUnique);
        
        var substMap : map<var_name,var_name> := map[];
        assert substMap.Keys == {};
        assert c.WellFormedVars(substMap.Keys);
        assert Maps.Injective(substMap) by {
            reveal Maps.Injective();
        }
        assert c.NoBinders();

        assert NoLoopsNoIfGuard(c);
        assert LabelsWellDefAux(c, TruePost<A>().scopes.Keys);
        assume LabelsWellDefAux(cUnique, TruePost<A>().scopes.Keys); //TODO
        assert RelPost(substMap, post1, post2, s2Orig);


        /*
        MakeScopedVarsUniqueCorrect<A>(
                a,
                c, 
                map[], //substMap 
                0,
                TruePost(),
                TruePost(),
                map[], //s2Orig
                {}); //names
        */
        assume false;
    }
}