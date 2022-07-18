include "../lang/BoogieLang.dfy"

module AstSubsetPredicates
{
  import opened BoogieLang
  import opened Wrappers

  predicate method NoLoops(c: Cmd)
  {
    c.PredicateRec((c: Cmd) => !c.Loop?, sc => true, e => true)
  }

  predicate method NoIfGuard(c: Cmd)
  {
    c.PredicateRec((c: Cmd) => c.If? ==> c.guard == None, sc => true, e => true)
  }

  predicate method NoLoopsNoIfGuard(c: Cmd)
  {
    && NoLoops(c) 
    && NoIfGuard(c)
  }

  predicate method NoScopedVars(c: Cmd)
  {
    c.PredicateRec((c: Cmd) => c.Scope? ==> c.varDecls == [], sc => true, e => true)
  }

  predicate method NoLoopsNoIfGuardNoScopedVars(c: Cmd)
  {
    && NoLoops(c) 
    && NoIfGuard(c)
    && NoScopedVars(c)
  }

  predicate method NoBreaks(c: Cmd)
  {
    c.PredicateRec((c: Cmd) => !c.Break?, sc => true, e => true)
  }

  predicate method IsPassive(sc: SimpleCmd)
  {
    sc.PredicateRec((sc': SimpleCmd) => !sc'.Assign? && !sc'.Havoc?, e => true)
    /*
    match sc
    case Skip => true
    case Assume(_) => true
    case Assert(_) => true
    case Assign(_, _, _) => false
    case Havoc(_) => false
    case SeqSimple(sc1, sc2) => IsPassive(sc1) && IsPassive(sc2)
    */
  }
}