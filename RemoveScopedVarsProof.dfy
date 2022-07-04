include "BoogieSemantics.dfy"
include "MakeScopedVarsUniqueImpl.dfy"
include "Naming.dfy"
include "dafny-libraries/src/Collections/Sequences/Seq.dfy"
include "dafny-libraries/src/Collections/Maps/Maps.dfy"

module MakeScopedVarsUniqueProof {

  import opened BoogieLang
  import opened BoogieSemantics
  import Sequences = Seq
  import Maps
  import Util
  import opened Wrappers
  import opened MakeScopedVarsUniqueImpl
  import opened Naming

  lemma RelStateRemoveScopedVarsCorrect<A(!new)>(a: absval_interp<A>, c: Cmd, post: WpPost<A>)
    requires 
      var (c', decls) := RemoveScopedVars(c);
      LabelsWellDefAux(c, post.scopes.Keys) && LabelsWellDefAux(c', post.scopes.Keys)
    ensures 
      var (c', decls) := RemoveScopedVars(c);
      forall s :: WpCmd(a, c, post)(s) == ForallVarDecls(a, decls, WpCmd(a, c', ResetVarsPost(decls, post, s)))(s)
    /* almost the same as Scope(None, decls, body)
      Main difference is that currentScope is not updated.
      If show that body has no direct breaks, then it would be the same
    */
}