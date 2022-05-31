include "BoogieLang.dfy"
include "dafny-libraries/src/Wrappers.dfy"

module BoogieOp {
  import opened BoogieLang
  import opened Wrappers

  /** unary operation Evaluation */

  function EvalUopNot<A>(v: Val<A>) : Option<Val<A>>
  {
    match v
    case LitV(LitBool(b)) => Some(LitV(LitBool(!b)))
    case _ => None
  }

  function EvalUopUminus<A>(v: Val<A>) : Option<Val<A>>
  {
    match v 
    case LitV(LitInt(i)) => Some(LitV(LitInt(-i)))
    case _ => None
  }

  function EvalUop<A>(uop: Unop, v: Val<A>) : Option<Val<A>>
  {
    match uop 
    case Not => EvalUopNot(v)
    case UMinus => EvalUopUminus(v)
  }

  /** binary operation Evaluation */

  function BoogieDiv(a: int, b: int): int
    ensures b != 0 ==> BoogieDiv(a,b) == a/b

  function BoogieMod(a: int, b: int): int
    ensures b != 0 ==> BoogieMod(a,b) == a % b

  /** integer binary operations */
  function EvalBinopAdd<A>(v1: Val<A>, v2: Val<A>) : Option<Val<A>>
  {
    match (v1,v2) 
    case (LitV(LitInt(i1)), LitV(LitInt(i2))) => Some(LitV(LitInt(i1 + i2)))
    case _ => None
  }

  function EvalBinopSub<A>(v1: Val<A>, v2: Val<A>) : Option<Val<A>>
  {
    match (v1,v2) 
    case (LitV(LitInt(i1)), LitV(LitInt(i2))) => Some(LitV(LitInt(i1 - i2)))
    case _ => None
  }

  function EvalBinopMul<A>(v1: Val<A>, v2: Val<A>) : Option<Val<A>>
  {
    match (v1,v2) 
    case (LitV(LitInt(i1)), LitV(LitInt(i2))) => Some(LitV(LitInt(i1 * i2)))
    case _ => None
  }

  function EvalBinopDiv<A>(v1: Val<A>, v2: Val<A>) : Option<Val<A>>
  {
    match (v1,v2) 
    case (LitV(LitInt(i1)), LitV(LitInt(i2))) => Some(LitV(LitInt(BoogieDiv(i1,i2))))
    case _ => None
  }

  function EvalBinopMod<A>(v1: Val<A>, v2: Val<A>) : Option<Val<A>>
  {
    match (v1,v2) 
    case (LitV(LitInt(i1)), LitV(LitInt(i2))) => Some(LitV(LitInt(BoogieMod(i1,i2))))
    case _ => None
  }

  /** relational binary operations */

  function EvalBinopLt<A>(v1: Val<A>, v2: Val<A>) : Option<Val<A>>
  {
    match (v1,v2) 
    case (LitV(LitInt(i1)), LitV(LitInt(i2))) => Some(LitV(LitBool(i1 < i2)))
    case _ => None
  }

  function EvalBinopLe<A>(v1: Val<A>, v2: Val<A>) : Option<Val<A>>
  {
    match (v1,v2) 
    case (LitV(LitInt(i1)), LitV(LitInt(i2))) => Some(LitV(LitBool(i1 <= i2)))
    case _ => None
  }

  function EvalBinopGt<A>(v1: Val<A>, v2: Val<A>) : Option<Val<A>>
  {
    match (v1,v2) 
    case (LitV(LitInt(i1)), LitV(LitInt(i2))) => Some(LitV(LitBool(i1 > i2)))
    case _ => None
  }

  function EvalBinopGe<A>(v1: Val<A>, v2: Val<A>) : Option<Val<A>>
  {
    match (v1,v2) 
    case (LitV(LitInt(i1)), LitV(LitInt(i2))) => Some(LitV(LitBool(i1 >= i2)))
    case _ => None
  }

  /** boolean binary operations */

  function EvalBinopAnd<A>(v1: Val<A>, v2: Val<A>) : Option<Val<A>>
  {
    match (v1,v2) 
    case (LitV(LitBool(b1)), LitV(LitBool(b2))) => Some(LitV(LitBool(b1 && b2)))
    case _ => None
  }

  function EvalBinopOr<A>(v1: Val<A>, v2: Val<A>) : Option<Val<A>>
  {
    match (v1,v2) 
    case (LitV(LitBool(b1)), LitV(LitBool(b2))) => Some(LitV(LitBool(b1 || b2)))
    case _ => None
  }

  function EvalBinopImp<A>(v1: Val<A>, v2: Val<A>) : Option<Val<A>>
  {
    match (v1,v2) 
    case (LitV(LitBool(b1)), LitV(LitBool(b2))) => Some(LitV(LitBool(b1  ==> b2)))
    case _ => None
  }

  function EvalBinopIff<A>(v1: Val<A>, v2: Val<A>) : Option<Val<A>>
  {
    match (v1,v2) 
    case (LitV(LitBool(b1)), LitV(LitBool(b2))) => Some(LitV(LitBool(b1  <==> b2)))
    case _ => None
  }

  function EvalBinop<A>(v1: Val<A>, bop: Binop, v2: Val<A>) : Option<Val<A>>
  {
    match bop
    case Eq => Some(LitV(LitBool(v1 == v2)))
    case Neq => Some(LitV(LitBool(v1 != v2)))
    case Add => EvalBinopAdd(v1, v2)
    case Sub => EvalBinopSub(v1, v2)
    case Mul => EvalBinopMul(v1, v2)
    case Div => EvalBinopDiv(v1, v2)
    case Mod => EvalBinopMod(v1, v2)
    case Lt => EvalBinopLt(v1, v2)
    case Le => EvalBinopLe(v1, v2)
    case Gt => EvalBinopGt(v1, v2)
    case Ge => EvalBinopGe(v1, v2)
    case And => EvalBinopAnd(v1, v2)
    case Or => EvalBinopOr(v1, v2)
    case Imp => EvalBinopImp(v1, v2)
    case Iff => EvalBinopIff(v1, v2)
  }
}