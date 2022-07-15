include "../lang/BoogieLang.dfy"

module AstSubsetPredicates
{
  import opened BoogieLang
  import opened Wrappers

  predicate NoLoops(c: Cmd)
  {
    match c
    case SimpleCmd(_) => true
    case Break(optLbl) => true
    case Seq(c1, c2) => NoLoops(c1) && NoLoops(c2)
    case Loop(_,_) => false
    case Scope(_, varDecls, body) => NoLoops(body)
    case If(_, thn, els) => NoLoops(thn) && NoLoops(els)
  }

  predicate NoIfGuard(c: Cmd)
  {
    match c
    case SimpleCmd(_) => true
    case Break(optLbl) => true
    case Seq(c1, c2) => NoIfGuard(c1) && NoIfGuard(c2)
    case Loop(_, body) => NoIfGuard(body)
    case Scope(_, varDecls, body) => NoIfGuard(body)
    case If(optCond, thn, els) => 
      && optCond == None 
      && NoIfGuard(thn)
      && NoIfGuard(els)
  }

  predicate NoLoopsNoIfGuard(c: Cmd)
  {
    && NoLoops(c) 
    && NoIfGuard(c)
  }

  predicate NoScopedVars(c: Cmd)
  {
    match c
    case SimpleCmd(_) => true
    case Break(optLbl) => true
    case Seq(thn, els) => 
      && NoScopedVars(thn) 
      && NoScopedVars(els)
    case Loop(_,_) => false
    case Scope(_, varDecls, body) => 
      && varDecls == [] 
      && NoScopedVars(body)
    case If(_, thn, els) => NoScopedVars(thn) && NoScopedVars(els)
  }

  predicate NoLoopsNoIfGuardNoScopedVars(c: Cmd)
  {
    && NoLoops(c) 
    && NoIfGuard(c)
    && NoScopedVars(c)
  }

  predicate NoBreaksScopedVarsLoops(c: Cmd)
  {
    match c
    case SimpleCmd(_) => true
    case Break(optLbl) => false
    case Seq(c1, c2) => NoBreaksScopedVarsLoops(c1) && NoBreaksScopedVarsLoops(c2)
    case Loop(_,_) => false
    case Scope(_, varDecls, body) => varDecls == [] && NoBreaksScopedVarsLoops(body)
    case If(_, thn, els) => NoBreaksScopedVarsLoops(thn) && NoBreaksScopedVarsLoops(els)
  }

  predicate IsPassive(sc: SimpleCmd)
  {
    match sc
    case Skip => true
    case Assume(_) => true
    case Assert(_) => true
    case Assign(_, _, _) => false
    case Havoc(_) => false
    case SeqSimple(sc1, sc2) => IsPassive(sc1) && IsPassive(sc2)
  }
}