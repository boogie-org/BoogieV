include "dafny-libraries/src/Wrappers.dfy"
include "Util.dfy"
include "dafny-libraries/src/Collections/Sequences/Seq.dfy"

module BoogieLang {
  import opened Wrappers 
  import opened Util
  import Sequences = Seq


  datatype Lit = LitInt(int) | LitBool(bool)
  {

    static const TrueLit: Lit := LitBool(true);

    static const FalseLit: Lit := LitBool(false);

    method ToString() returns (s: string) {
      match this {
        case LitInt(i) => 
          s := IntToString(i);
        case LitBool(b) => 
          s := BoolToString(b);
      }
    }
  }

  datatype Binop = Eq | Neq | Add | Sub | Mul | Div | Mod | Lt | Le | Gt | Ge | And | Or | Imp | Iff
  {
    function method ToString() : string {
      match this
      case Eq => "=="
      case Neq => "!="
      case Add => "+"
      case Sub => "-"
      case Mul => "*"
      case Div => "/"
      case Mod => "%"
      case Lt => "<"
      case Le => "<="
      case Gt => ">"
      case Ge => ">="
      case And => "&&"
      case Or => "||"
      case Imp => "==>"
      case Iff => "<==>"
    }
  }

  datatype Unop = Not | UMinus
  {
    function method ToString() : string {
      match this
      case Not => "!"
      case UMinus => "-"
    }
  }

  type var_name = string
  type proc_name = string
  type lbl_name = string
  type tcon_name = string
  type fun_name = string 

  datatype PrimTy = TBool | TInt
  {
    function method ToString() : string {
      match this
      case TBool => "bool"
      case TInt => "int"
    }
  }
  //TODO: reals, bitvectors, etc...

  /** no type variables, because there is no polymorphism. Since there is no polymorphism, it is sufficient for type 
  constructors to not have any parameters */
  datatype Ty =
    | TPrim(PrimTy)
    | TCon(tcon_name)
  {
    function method ToString() : string {
      match this
      case TPrim(tprim) => tprim.ToString()
      case TCon(tcon) => tcon
    }
  }

  function TypeOfLit(lit: Lit) : PrimTy
  {
    match lit
    case LitInt(_) => TInt
    case LitBool(_) => TBool
  }

  type VarDecl = (var_name, Ty)

  datatype BinderKind = ForallQ | ExistsQ
  {
    function method ToString() : string {
      match this 
      case ForallQ => "forall"
      case ExistsQ => "exists"
    }
  }
    
  datatype Expr = 
    | Var(var_name) 
    | ELit(Lit)
    | UnOp(Unop, Expr)
    | BinOp(Expr, Binop, Expr)
    | Old(Expr)
    | Binder(BinderKind, var_name, Ty, Expr) //switch to DeBruijn?
  /** TODO 
    | FunCall(fun_name, List<Expr>)
    /** 
       forall x :: forall y :: P(x,y,z)

        var z: int 0
        DeBruijn: forall (forall P(1,0,2))

        Locally Nameless: forall (forall P(1,0,z))
     */
  */
  {
    method ToString() returns (s: string) {
      match this {
        case Var(x) => return x;
        case ELit(lit) => s := lit.ToString(); return s;
        case UnOp(uop, e) =>
          var uopS := uop.ToString();
          var eS := e.ToString();
          return "(" + uopS + eS + ")";
        case BinOp(e1, bop, e2) => 
          var e1S := e1.ToString();
          var bopS := bop.ToString();
          var e2S := e2.ToString();
          return "(" + e1S + " " + bopS + " " + e2S + ")";
        case Old(e) => 
          var eS := e.ToString();
          return "old(" + eS +")";
        case Binder(binderKind, x, t, e) => 
          var tS := t.ToString();
          var eS := e.ToString();
          var binderKindS := binderKind.ToString();
          return "(" + binderKindS + " " + x + ":" + tS + " :: " + eS + ")";
      }
    }

    function method FreeVars(): set<var_name>
    {
      match this {
        case Var(x) => {x}
        case ELit(lit) => {}
        case UnOp(uop, e) => e.FreeVars()
        case BinOp(e1, bop, e2) => e1.FreeVars() + e2.FreeVars()
        case Old(e) => {}
        case Binder(binderKind, x, t, e) => 
          e.FreeVars() - {x}
      }
    }

    static const TrueExpr: Expr := ELit(LitBool(true));

    static const FalseExpr: Expr := ELit(LitBool(false));
  }

  datatype SimpleCmd =
    | Skip //one reason to add Skip instead of using Assert/Assume true: make explicit that the command does nothing
    | Assert(Expr)
    | Assume(Expr)
    | Assign(var_name, Ty, Expr) 
    | Havoc(seq<VarDecl>)
    | SeqSimple(SimpleCmd, SimpleCmd) 
    /* The reason for adding a separate sequential composition for simple commands is to be able to transform the AST
       into a form that more directly represents the desired CFG block structure.
       Moreover, if we did not add such a constructor, then we would define a basic block as seq<SimpleCmd> 
       (instead of SimpleCmd). As a result, one would have to define various operations on seq<SimpleCmd> that are
       defined on SimpleCmd. This means a lot of the extra work imposed by adding a separate sequential composition
       constructor for SimpleCmd would have to be done anyway. */
  {
    method ToString(indent: nat) returns (s: string) {
      match this {
        case Skip => return "";
        case Assert(e) =>
          var eS := e.ToString();
          return IndentString("assert " + eS + ";", indent);
        case Assume(e) =>
          var eS := e.ToString();
          return IndentString("assert " + eS + ";", indent);
        case Assign(x, _, e) =>
          var eS := e.ToString();
          return IndentString(x + " := " + eS + ";", indent);
        case Havoc(xs) =>
          var declS := "";
          var i := 0;
          while i < |xs| {
            declS := xs[0].0 + if i+1 < |xs| then ", " else "";
            i := i+1;
          }
          return IndentString("havoc " + declS + ";", indent);
        case SeqSimple(sc1, sc2) => return "TODO";
      }
    }

    predicate WellFormedVars(xs: set<var_name>)
    {
      match this
      case Skip => true
      case Assert(e) => e.FreeVars() <= xs
      case Assume(e) => e.FreeVars() <= xs
      case Assign(x, t, e) => x in xs && e.FreeVars() <= xs
      case Havoc(varDecls) => GetVarNames(varDecls) <= xs
      case SeqSimple(sc1, sc2) => sc1.WellFormedVars(xs) && sc2.WellFormedVars(xs)
    }
  }

/** TODO: add return */
  datatype Cmd =
    | SimpleCmd(SimpleCmd)
    | Break(Option<lbl_name>)
    | Seq(Cmd, Cmd)
    | Scope(labelName: Option<lbl_name>, varDecls: seq<VarDecl>, body: Cmd)
    | Loop(invariants: seq<Expr>, body: Cmd) 
    //cond = None represents a non-deterministic if-statement (if(*) {...} else {...})
    | If(guard: Option<Expr>, thn: Cmd, els: Cmd)
  
  /*
    | ProcCall(proc_name, seq<Expr>, seq<var_name>)
  */
  {
    predicate WellFormedVars(xs: set<var_name>)
    {
      match this
      case SimpleCmd(sc) => sc.WellFormedVars(xs)
      case Break(_) => true
      case Scope(_, varDecls, body) =>
        && Sequences.HasNoDuplicates(varDecls)
        && body.WellFormedVars(xs+GetVarNames(varDecls))
      case If(optCond, thn, els) =>
        && (optCond.Some? ==> optCond.value.FreeVars() <= xs)
        && thn.WellFormedVars(xs)
        && els.WellFormedVars(xs)
      case Loop(invs, body) =>
        && (forall inv | inv in invs :: inv.FreeVars() <= xs)
        && body.WellFormedVars(xs)
      case Seq(c1, c2) =>
        && c1.WellFormedVars(xs)
        && c2.WellFormedVars(xs)
    }

    method ToString(indent: nat) returns (s: string) {
      match this {
        case SimpleCmd(simpleC) => s := simpleC.ToString(indent); return s;
        case Break(optLbl) =>
          return IndentString("break" + (if optLbl.Some? then " " + optLbl.value else "") + ";", indent);
        case Scope(optLbl, xs, c) =>
          var i := 0;
          var declS := "";
          while i < |xs| {
            var tS := xs[i].1.ToString();
            declS := declS + " var " + xs[i].0 + ": " + tS + ";";
            i := i+1;
          }
          var cS := c.ToString(indent+2);
          return 
               IndentString("scope ", indent) + (if optLbl.Some? then optLbl.value else "") + "{ \n" +
               IndentString(declS, indent+2) + "\n" + 
               cS + "\n" +
               IndentString("}", indent);
        case Seq(c1, c2) =>
          var c1S := c1.ToString(indent);
          var c2S := c2.ToString(indent);
          return c1S + "\n" + c2S;
        case Loop(invs, body) =>
          var i := 0;
          var invS := "";
          while i < |invs| {
            var eS := invs[i].ToString();
            invS := invS + "\n invariant "  + eS;
            i := i+1;
          }
          var bodyS := body.ToString(indent+2);
          s := IndentString("loop", indent) + invS + "\n" + 
               IndentString("{ \n", indent) +
               bodyS + 
               IndentString("}", indent);
        case If(optCond, thn, els) =>
          var condS := "*";
          if optCond.Some? {
            condS := optCond.value.ToString();
          }
          var thnS := thn.ToString(indent+2);
          var elsS := els.ToString(indent+2);

          s := IndentString("if(", indent) + condS + ") { \n" +
               thnS + "\n" +
               IndentString("}", indent) + " else { \n" +
               elsS + "\n" +
               IndentString("}", indent);
          
          return s;
      }
    }
  }

  datatype Val<A> = LitV(Lit) | AbsV(A)

  type absval_interp<!A> = A -> tcon_name 
  /* unclear if can represent absval_interp as a partial map due to the VC generation implementation. For the Boogie 
  semantics itself there is no issue.  However, if the proof of the VC generation implementation correctness requires one 
  to represent a Dafny type T_all that represents precisely all Values in Boogie, then one would need dependent types to 
  represent this T_all (since T_all would depend on the abstract Value interpretation, taking only those abstract Values 
  into account that map to some Value) */

  function TypeOfVal<A>(a: absval_interp<A>, v: Val<A>) : Ty
  {
    match v
    case LitV(lit) => TPrim(TypeOfLit(lit))
    case AbsV(abs_val) => TCon(a(abs_val))
  }

  function TypeOfValues<A>(a: absval_interp<A>, vs: seq<Val<A>>) : seq<Ty>
  {
    seq(|vs|, i requires 0 <= i < |vs| => TypeOfVal(a, vs[i]))
  }

  type state<A> = map<var_name, Val<A>>

  //while loop without break in body
  function WhileLoop(fresh_name: string, cond: Expr, invs: seq<Expr>, body: Cmd) : Cmd
  {
    Scope(Some(fresh_name), [], Loop(invs, If(Some(cond), body, Break(Some(fresh_name)))))
  }

  function method SeqToCmd(cmds: seq<Cmd>) : Cmd
    requires |cmds| > 0
  {
    if |cmds| == 1 then 
      cmds[0]
    else 
      Seq(cmds[0], SeqToCmd(cmds[1..]))
  }

  //e[x |-> e']
  function SubstExpr(e: Expr, x: var_name, esub: Expr): Expr
  {
    match e
    case Var(x') => if x == x' then esub else e
    case ELit(_) => e
    case UnOp(uop, e') => UnOp(uop, SubstExpr(e', x, esub))
    case BinOp(e1, bop, e2) => BinOp(SubstExpr(e1, x, esub), bop, SubstExpr(e2, x, esub))
    case Old(Expr) => Old(Expr) //TODO 

    //we ignore variable capturing: need side conditions that capturing can't occur
    case Binder(binderKind, x, ty, ebody) => Binder(binderKind, x, ty, SubstExpr(ebody, x, esub)) 
  }

  function NAryBinOp(bop: Binop, exprIfEmpty: Expr, es: seq<Expr>): Expr
  {
    if |es| == 0 then
      exprIfEmpty
    else 
      BinOp(es[0], bop, NAryBinOp(bop, exprIfEmpty, es[1..]))
  }

  function method GetVarNames(vs: seq<(var_name,Ty)>):set<var_name>
  {
    //if |vs| == 0 then {} else {vs[0].0} + GetVarNames(vs[1..])
    set varDecl | varDecl in vs :: varDecl.0
  }

  function method GetVarNamesSeq(vs: seq<(var_name,Ty)>):seq<var_name>
  {
    seq(|vs|, i requires 0 <= i < |vs| => vs[i].0)
  }

  lemma GetVarNamesContainedSeq(v: var_name, vs: seq<(var_name,Ty)>)
    requires v in GetVarNames(vs)  
    ensures v in GetVarNamesSeq(vs)
  {
    var varDecl :| varDecl in vs && varDecl.0 == v;
    var i :| 0 <= i < |vs| && varDecl == vs[i];

    assert GetVarNamesSeq(vs)[i] == vs[i].0;
  }

  function ModifiedVars(c: Cmd): seq<(var_name, Ty)>
  {
    RemoveDuplicates(ModifiedVarsAux(c, {}))
  }

  function ModifiedVarDecls(decls: seq<(var_name, Ty)>, exclude: set<var_name>) : seq<(var_name, Ty)>
  {
    if |decls| == 0 then []
    else (if decls[0].0 in exclude then [] else [decls[0]]) + ModifiedVarDecls(decls[1..], exclude)
  }

  function ModifiedVarsAux(c: Cmd, exclude: set<var_name>): seq<(var_name, Ty)>
  {
    match c 
    case SimpleCmd(Assign(x,t,_)) => if x in exclude then [] else [(x,t)]
    case SimpleCmd(Havoc(decls)) => ModifiedVarDecls(decls, exclude)
    case Scope(_, decls, c) => ModifiedVarsAux(c, exclude + GetVarNames(decls))
    case Seq(c1, c2) => ModifiedVarsAux(c1, exclude) + ModifiedVarsAux(c2, exclude)
    case Loop(_, body) => ModifiedVarsAux(body, exclude)
    case If(_, c1, c2) => ModifiedVarsAux(c1, exclude) + ModifiedVarsAux(c2, exclude)
    case _ => []
  }

  function LabelsWellDef(c: Cmd): bool
  {
    LabelsWellDefAux(c, {})
  }

  function LabelsWellDefAux(c: Cmd, activeLabels: set<lbl_name>): bool
  {
    match c
    case Break(optLabel) => if optLabel.Some? then optLabel.value in activeLabels else true
    case Seq(c1, c2) => LabelsWellDefAux(c1, activeLabels) && LabelsWellDefAux(c2, activeLabels)
    case Scope(optLabel, _, c) =>
      match optLabel {
        case Some(lbl) => LabelsWellDefAux(c, {lbl} + activeLabels)
        case None => LabelsWellDefAux(c, activeLabels)
      }
    case If(_, thn, els) => LabelsWellDefAux(thn, activeLabels) && LabelsWellDefAux(els, activeLabels)
    case Loop(_, body) => LabelsWellDefAux(body, activeLabels)
    case SimpleCmd(_) => true
  }
}