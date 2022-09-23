include "../lang/BoogieLang.dfy"

module {:extern "System"} {:compile false} System {
  class {:extern} {:compile false} String {}
}

module {:extern "Microsoft.Boogie.VCExprAST"} {:compile false} VCExprAST {
  class {:extern} {:compile false} VCExpr {}
}

module SMTInterface {

  import opened BoogieLang
  import System
  import opened VCExprAST


  class {:extern} VCExprInterface {
    static method {:extern} Create(x1: string, x2: string) returns (res: VCExprInterface)

    method {:extern} IsVCValid(e: VCExpr) returns (b: bool)

    method {:extern} VCIntVar(x: string) returns (res: VCExpr)
    method {:extern} VCBoolVar(x: string) returns (res: VCExpr)
    method {:extern} VCLitInt(i: int) returns (res: VCExpr)
    method {:extern} VCLitBool(b: bool) returns (res: VCExpr)

    /** binary operations */
    method {:extern} VCEq(e1: VCExpr, e2:VCExpr) returns (res: VCExpr)
    method {:extern} VCNeq(e1: VCExpr, e2: VCExpr) returns (res: VCExpr)
    method {:extern} VCAdd(e1: VCExpr, e2: VCExpr) returns (res: VCExpr)
    method {:extern} VCSub(e1: VCExpr, e2: VCExpr) returns (res: VCExpr)
    method {:extern} VCMul(e1: VCExpr, e2: VCExpr) returns (res: VCExpr)
    method {:extern} VCDiv(e1: VCExpr, e2: VCExpr) returns (res: VCExpr)
    method {:extern} VCMod(e1: VCExpr, e2: VCExpr) returns (res: VCExpr)
    method {:extern} VCLt(e1: VCExpr, e2: VCExpr) returns (res: VCExpr)
    method {:extern} VCLe(e1: VCExpr, e2: VCExpr) returns (res: VCExpr)
    method {:extern} VCGt(e1: VCExpr, e2: VCExpr) returns (res: VCExpr)
    method {:extern} VCGe(e1: VCExpr, e2: VCExpr) returns (res: VCExpr)
    method {:extern} VCAnd(e1: VCExpr, e2: VCExpr) returns (res: VCExpr)
    method {:extern} VCOr(e1: VCExpr, e2: VCExpr) returns (res: VCExpr)
    method {:extern} VCImp(e1: VCExpr, e2: VCExpr) returns (res: VCExpr)
    method {:extern} VCIff(e1: VCExpr, e2: VCExpr) returns (res: VCExpr)
    method {:extern} VCLet(x: string, binding: VCExpr, body: VCExpr) returns (res: VCExpr)
    
    
    /** unary operations */
    method {:extern} VCNot(e: VCExpr) returns (res: VCExpr)
    method {:extern} VCUMinus(e: VCExpr) returns (res: VCExpr)

  }

}

module VCExprAdapter {

  import opened BoogieLang
  import opened SMTInterface
  import opened VCExprAST

  method BinopToVCExpr(vcExprI: VCExprInterface, e1: VCExpr, bop: Binop, e2: VCExpr) returns (res: VCExpr)
  {
    match bop
    case Eq => res := vcExprI.VCEq(e1, e2);
    case Neq => res := vcExprI.VCNeq(e1, e2);
    case Add => res := vcExprI.VCAdd(e1, e2);
    case Sub => res := vcExprI.VCSub(e1, e2); 
    case Mul => res := vcExprI.VCMul(e1, e2); 
    case Div => res := vcExprI.VCDiv(e1, e2); 
    case Mod => res := vcExprI.VCMod(e1, e2); 
    case Lt => res := vcExprI.VCLt(e1, e2);
    case Le => res := vcExprI.VCLe(e1, e2);
    case Gt => res := vcExprI.VCGt(e1, e2);
    case Ge => res := vcExprI.VCGe(e1, e2); 
    case And => res := vcExprI.VCAnd(e1, e2); 
    case Or => res := vcExprI.VCOr(e1, e2); 
    case Imp => res := vcExprI.VCImp(e1, e2); 
    case Iff => res := vcExprI.VCIff(e1, e2); 
  }

  method UnopToVCExpr(vcExprI: VCExprInterface, uop: Unop, e: VCExpr) returns (res: VCExpr)
  {
    match uop
    case Not => res := vcExprI.VCNot(e);
    case UMinus => res := vcExprI.VCUMinus(e);
  }

  method ExprToVCExpr(vcExprI: VCExprInterface, e: Expr) returns (res: VCExpr)
  {
    match e
    case Var(x) => 
      //TODO: need to add type field variable, for now use hack to distinguish block variables from other variables
      if x != [] && x[0] == 'B' {
        res := vcExprI.VCBoolVar(x);
      } else {
        res := vcExprI.VCIntVar(x);
      }
    case ELit(lit) => 
      match lit {
        case LitInt(i) => res := vcExprI.VCLitInt(i);
        case LitBool(b) => res := vcExprI.VCLitBool(b);
      }
    case UnOp(uop, e') =>
      var vcE' := ExprToVCExpr(vcExprI, e');
      res := UnopToVCExpr(vcExprI, uop, vcE');
    case BinOp(e1, bop, e2) => 
      var vcE1' := ExprToVCExpr(vcExprI, e1);
      var vcE2' := ExprToVCExpr(vcExprI, e2);
      res := BinopToVCExpr(vcExprI, vcE1', bop, vcE2');
    case Let(x, e, body) => 
      var vcE := ExprToVCExpr(vcExprI, e);
      var vcBody := ExprToVCExpr(vcExprI, body);
      res := vcExprI.VCLet(x, vcE, vcBody);
  }

}
