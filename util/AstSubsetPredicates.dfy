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

  predicate NoIfCond(c: Cmd)
  {
    match c
    case SimpleCmd(_) => true
    case Break(optLbl) => true
    case Seq(c1, c2) => NoIfCond(c1) && NoIfCond(c2)
    case Loop(_, body) => NoIfCond(body)
    case Scope(_, varDecls, body) => NoIfCond(body)
    case If(optCond, thn, els) => 
      && optCond == None 
      && NoIfCond(thn)
      && NoIfCond(els)
  }

  predicate NoLoopsNoIfCond(c: Cmd)
  {
    && NoLoops(c) 
    && NoIfCond(c)
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

  predicate NoLoopsNoIfCondNoScopedVars(c: Cmd)
  {
    && NoLoops(c) 
    && NoIfCond(c)
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
    case Assign(_, _, _) => false
    case Havoc(_) => false
    case _ => true
  }
}