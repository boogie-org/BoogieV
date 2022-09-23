include "../dafny-libraries/src/Wrappers.dfy"
include "../util/Util.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"
include "../dafny-libraries/src/Collections/Maps/Maps.dfy"

module BoogieLang {
  import opened Wrappers 
  import opened Util
  import Sequences = Seq
  import Maps


  datatype Lit = LitInt(int) | LitBool(bool)
  {

    static const TrueLit: Lit := LitBool(true);

    static const FalseLit: Lit := LitBool(false);

    function method ToString() : string {
      match this {
        case LitInt(i) => 
          IntToString(i)
        case LitBool(b) => 
          BoolToString(b)
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
    | TPrim(primType: PrimTy)
    | TCon(constrName: tcon_name)
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
      case Let => "let"
      //case ForallQ => "forall"
      //case ExistsQ => "exists"
    }
  }
    
  datatype Expr = 
    | Var(var_name) 
    | ELit(Lit)
    | UnOp(Unop, Expr)
    | BinOp(Expr, Binop, Expr)
    | Let(var_name, Expr, Expr)
    //| Binder(BinderKind, var_name, Ty, Expr) //switch to DeBruijn?
  /** TODO 
    | Old(Expr)
    | FunCall(fun_name, List<Expr>)
  */
  {
    function method ToString() : string {
      match this {
        case Var(x) => x
        case ELit(lit) => lit.ToString()
        case UnOp(uop, e) =>
          var uopS := uop.ToString();
          var eS := e.ToString();
          "(" + uopS + eS + ")"
        case BinOp(e1, bop, e2) => 
          var e1S := e1.ToString();
          var bopS := bop.ToString();
          var e2S := e2.ToString();
          "(" + e1S + " " + bopS + " " + e2S + ")"
        case Let(x, e1, e2) =>
          var e1S := e1.ToString();
          var e2S := e2.ToString();
          "(let " + x + " = " + e1S + " in " + e2S + ")"
        /*
        case Binder(binderKind, x, t, e) => 
          var tS := t.ToString();
          var eS := e.ToString();
          var binderKindS := binderKind.ToString();
          return "(" + binderKindS + " " + x + ":" + tS + " :: " + eS + ")";
        */
      }
    }

    function method FreeVars(): set<var_name>
    {
      match this {
        case Var(x) => {x}
        case ELit(lit) => {}
        case UnOp(uop, e) => e.FreeVars()
        case BinOp(e1, bop, e2) => e1.FreeVars() + e2.FreeVars()
        case Let(x, e, body) => e.FreeVars() + (body.FreeVars() - {x})
        /*
          case Binder(binderKind, x, t, e) => 
          e.FreeVars() - {x} */
      }
    }

    static const TrueExpr: Expr := ELit(LitBool(true));

    static const FalseExpr: Expr := ELit(LitBool(false));

    predicate method PredicateRec(pred: Expr -> bool)
    {
      pred(this) &&
      match this
      case Var(x) => true
      case ELit(_) => true
      case UnOp(uop, e') => e'.PredicateRec(pred)
      case BinOp(e1, bop, e2) => e1.PredicateRec(pred) && e2.PredicateRec(pred)
      case Let(x, e, body) => e.PredicateRec(pred) && body.PredicateRec(pred)
    }

    predicate method NoBinders()
    {
      PredicateRec((e:Expr) => !e.Let?)
    }

    function method MultiSubstExpr(varMapping: map<var_name, var_name>): Expr
    {
      match this
      case Var(x) => if x in varMapping.Keys then Var(varMapping[x]) else Var(x)
      case ELit(_) => this
      case UnOp(uop, e') => UnOp(uop, e'.MultiSubstExpr(varMapping))
      case BinOp(e1, bop, e2) => BinOp(e1.MultiSubstExpr(varMapping), bop, e2.MultiSubstExpr(varMapping))
      case Let(x, e, body) => Let(x, e, body.MultiSubstExpr(varMapping-{x})) //TODO: does not take variable capturing into account
    }
  }

  datatype SimpleCmd =
    | Skip //one reason to add Skip instead of using Assert/Assume true: make explicit that the command does nothing
    | Assert(Expr)
    | Assume(Expr)
    | Assign(var_name, Ty, Expr) 
    | Havoc(varDecls: seq<VarDecl>)
    | SeqSimple(SimpleCmd, SimpleCmd) 
    /* The reason for adding a separate sequential composition for simple commands is to be able to transform the AST
       into a form that more directly represents the desired CFG block structure.
       Moreover, if we did not add such a constructor, then we would define a basic block as seq<SimpleCmd> 
       (instead of SimpleCmd). As a result, one would have to define various operations on seq<SimpleCmd> that are
       defined on SimpleCmd. This means a lot of the extra work imposed by adding a separate sequential composition
       constructor for SimpleCmd would have to be done anyway. */
  {
    function method ToString(indent: nat) : string {
      match this {
        case Skip => IndentString("skip;", indent)
        case Assert(e) =>
          var eS := e.ToString();
          IndentString("assert " + eS + ";", indent)
        case Assume(e) =>
          var eS := e.ToString();
          IndentString("assume " + eS + ";", indent)
        case Assign(x, _, e) =>
          var eS := e.ToString();
          IndentString(x + " := " + eS + ";", indent)
        case Havoc(xs) =>
          var declS := Sequences.FoldLeft((s, decl : VarDecl) => s+", "+decl.0, "", xs);
          IndentString("havoc " + declS + ";", indent)
        case SeqSimple(sc1, sc2) => 
          sc1.ToString(indent)+"\n"+
          sc2.ToString(indent)
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

    predicate WellFormedTypes(tcons: set<tcon_name>)
    {
      PredicateRec(
        (sc : SimpleCmd) => (sc.Havoc? ==> GetTypeConstr(sc.varDecls) <= tcons), e => true
      )
    }

    predicate method PredicateRec(pred: SimpleCmd -> bool, predE: Expr -> bool)
    {
      pred(this) &&
      match this
      case Skip => true
      case Assert(e) => predE(e)
      case Assume(e) => predE(e)
      case Assign(x, t, e) => predE(e)
      case Havoc(varDecls) => true
      case SeqSimple(sc1, sc2) => sc1.PredicateRec(pred, predE) && sc2.PredicateRec(pred, predE)
    }

    predicate method NoBinders()
    {
      PredicateRec((sc: SimpleCmd) => true, (e: Expr) => e.NoBinders())
    }

    function method SubstSimpleCmd(varMapping: map<var_name, var_name>) : SimpleCmd
    {
      match this
      case Skip => Skip 
      case Assert(e) => Assert(e.MultiSubstExpr(varMapping))
      case Assume(e) => Assume(e.MultiSubstExpr(varMapping))
      case Assign(x, t, e) =>
        var newLHS := if x in varMapping.Keys then varMapping[x] else x;
        var newRHS := e.MultiSubstExpr(varMapping);
        Assign(newLHS, t, newRHS)
      case Havoc(varDecls) =>
        var f := (vDecl : (var_name, Ty)) => 
            if vDecl.0 in varMapping.Keys then (varMapping[vDecl.0], vDecl.1) else vDecl;
        var varDecls' := Sequences.Map(f, varDecls);
        Havoc(varDecls')
      case SeqSimple(c1, c2)  =>
        SeqSimple(c1.SubstSimpleCmd(varMapping), c2.SubstSimpleCmd(varMapping))
    }
  }

  function method VarDeclToString(d: VarDecl) : string
  {
    "var " + d.0 + ":" + d.1.ToString()
  }

/** TODO: add return */
  datatype Cmd =
    | SimpleCmd(SimpleCmd)
    | Break(Option<lbl_name>)
    | Seq(Cmd, Cmd)
    | Scope(labelName: Option<lbl_name>, varDecls: seq<VarDecl>, body: Cmd)
    | Loop(invariants: seq<Expr>, body: Cmd) 
    //guard = None represents a non-deterministic if-statement (if(*) {...} else {...})
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
        //&& Sequences.HasNoDuplicates(varDecls)
        body.WellFormedVars(xs+GetVarNames(varDecls))
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

    predicate WellFormedTypes(tcons: set<tcon_name>)
    {
      this.PredicateRec(
        (c : Cmd) => c.Scope? && GetTypeConstr(c.varDecls) <= tcons,
        (sc : SimpleCmd) => sc.WellFormedTypes(tcons), 
        e => true
      )
    }

    function method ToString(indent: nat) : string {
      match this {
        case SimpleCmd(simpleC) => simpleC.ToString(indent)
        case Break(optLbl) =>
          IndentString("break" + (if optLbl.Some? then " " + optLbl.value else "") + ";", indent)
        case Scope(optLbl, xs, c) =>
          var declS := 
            if |xs| == 0 then ""
            else Sequences.FoldLeft((s, decl : VarDecl) => s+", "+VarDeclToString(decl), VarDeclToString(xs[0]), xs[1..]);
          var cS := c.ToString(indent+2);
          IndentString("scope ", indent) + (if optLbl.Some? then optLbl.value else "") + "{ \n" +
          IndentString(declS, indent+2) + "\n" + 
          cS + "\n" +
          IndentString("}", indent)
        case Seq(c1, c2) =>
          var c1S := c1.ToString(indent);
          var c2S := c2.ToString(indent);
          c1S + "\n" + c2S
        case Loop(invs, body) =>
          var i := 0;
          var invS := Sequences.FoldLeft((s, inv: Expr) => s+"\n invariant "+ inv.ToString(), "", invs);
          var bodyS := body.ToString(indent+2);
          IndentString("loop", indent) + invS + "\n" + 
          IndentString("{ \n", indent) +
          bodyS + 
          IndentString("}", indent)
        case If(optCond, thn, els) =>
          var condS := 
            if optCond.Some? then
              optCond.value.ToString()
            else 
              "*";
          var thnS := thn.ToString(indent+2);
          var elsS := els.ToString(indent+2);

          IndentString("if(", indent) + condS + ") { \n" +
          thnS + "\n" +
          IndentString("}", indent) + " else { \n" +
          elsS + "\n" +
          IndentString("}", indent)
      }
    }

    predicate method PredicateRec(pred: Cmd -> bool, predSimple: SimpleCmd -> bool, predE: Expr -> bool)
    {
      pred(this)
      &&
      match this
      case SimpleCmd(sc) => predSimple(sc) 
      case Break(optLbl) => true
      case Seq(c1, c2) => c1.PredicateRec(pred, predSimple, predE) && c2.PredicateRec(pred, predSimple, predE)
      case Loop(invs, body) => (forall inv | inv in invs :: predE(inv)) && body.PredicateRec(pred, predSimple, predE)
      case Scope(_, varDecls, body) => body.PredicateRec(pred, predSimple, predE)
      case If(guardOpt, thn, els) => 
        && (guardOpt.Some? ==> predE(guardOpt.value))
        && thn.PredicateRec(pred, predSimple, predE) 
        && els.PredicateRec(pred, predSimple, predE)
    }

    predicate method NoBinders() {
      PredicateRec( (c: Cmd) => true, (sc: SimpleCmd) => sc.NoBinders(), (e: Expr) => e.NoBinders() )
    }
  }

  lemma SimpleCmdWellFormedVarsLarger(sc: SimpleCmd, vars: set<var_name>, vars': set<var_name>)
    requires vars <= vars'
    requires sc.WellFormedVars(vars)
    ensures sc.WellFormedVars(vars')
  { }

  lemma CmdWellFormedVarsLarger(c: Cmd, vars: set<var_name>, vars': set<var_name>)
    requires vars <= vars'
    requires c.WellFormedVars(vars)
    ensures c.WellFormedVars(vars')
  { 
    match c
    case SimpleCmd(simpleCmd) => SimpleCmdWellFormedVarsLarger(simpleCmd, vars, vars');
    case Scope(_, varDecls, body) =>
      calc {
        vars+GetVarNames(varDecls);
      <=
        vars'+GetVarNames(varDecls);
      }
    case _ =>
  }

  datatype Val<A> = LitV(Lit) | AbsV(A)

  type absval_interp<!A> = A -> tcon_name 
  /* unclear if can represent absval_interp as a partial map due to the VC generation implementation. For the Boogie 
  semantics itself there is no issue.  However, if the proof of the VC generation implementation correctness requires one 
  to represent a Dafny type T_all that represents precisely all Values in Boogie, then one would need dependent types to 
  represent this T_all (since T_all would depend on the abstract Value interpretation, taking only those abstract Values 
  into account that map to some Value) */

  /** an abstract value interpretation is well formed w.r.t. a set of type constructors,
    if each type constructor in the given set is inhabited by at least one abstract value  */
  predicate {:opaque} WfAbsvalInterp<A(!new)>(a: absval_interp<A>, tcons: set<tcon_name>)
  {
    forall t | t in tcons :: exists absVal :: t == a(absVal) 
  } 

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

  function method SeqToSimpleCmd(simpleCmds: seq<SimpleCmd>) : SimpleCmd
    requires |simpleCmds| > 0
  {
    if |simpleCmds| == 1 then 
      simpleCmds[0]
    else 
      SeqSimple(simpleCmds[0], SeqToSimpleCmd(simpleCmds[1..]))
  }

  function method NAryBinOp(bop: Binop, exprIfEmpty: Expr, es: seq<Expr>): Expr
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

  function method GetTypes(vs: seq<VarDecl>) : set<Ty>
  {
    set varDecl | varDecl in vs :: varDecl.1
  }

  function method GetTypeConstr(vs: seq<VarDecl>) : set<tcon_name>
  {
    set varDecl | varDecl in vs && varDecl.1.TCon? :: varDecl.1.constrName
  }

  lemma GetVarNamesContainedSeq(v: var_name, vs: seq<(var_name,Ty)>)
    requires v in GetVarNames(vs)  
    ensures v in GetVarNamesSeq(vs)
  {
    var varDecl :| varDecl in vs && varDecl.0 == v;
    var i :| 0 <= i < |vs| && varDecl == vs[i];

    assert GetVarNamesSeq(vs)[i] == vs[i].0;
  }

  function method ModifiedVars(c: Cmd): seq<(var_name, Ty)>
  {
    RemoveDuplicates(ModifiedVarsAux(c, {}))
  }

  function method ModifiedVarDecls(decls: seq<(var_name, Ty)>, exclude: set<var_name>) : seq<(var_name, Ty)>
  {
    if |decls| == 0 then []
    else (if decls[0].0 in exclude then [] else [decls[0]]) + ModifiedVarDecls(decls[1..], exclude)
  }

  function method ModifiedVarsAux(c: Cmd, exclude: set<var_name>): seq<(var_name, Ty)>
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