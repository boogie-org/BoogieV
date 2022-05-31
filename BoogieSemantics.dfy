include "BoogieLang.dfy"
include "BoogieOp.dfy"

module BoogieSemantics {
  import opened BoogieLang
  import opened Wrappers
  import opened Util
  import opened BoogieOp

  function EvalExpr<A(!new)>(a: absval_interp<A>, e: Expr, s: state<A>) : Option<Val<A>>
  {
    match e
    case Var(x) => if x in s.Keys then Some(s[x]) else None
    case ELit(lit) => Some(LitV(lit))
    case UnOp(uop, e') => 
      var v :- EvalExpr(a, e', s);
      EvalUop(uop, v)
    case BinOp(e1, bop, e2) =>
      var v1 :- EvalExpr(a, e1, s);
      var v2 :- EvalExpr(a, e2, s);
      EvalBinop(v1, bop, v2)
    case Old(e) => None //TODO
    case Binder(ForallQ, x, ty, e) =>  if forall v :: TypeOfVal(a,v) == ty ==> EvalExpr(a, e, s[x := v]) == Some(LitV(LitBool(true))) then 
                                  Some(LitV(LitBool(true))) 
                              else if forall v :: TypeOfVal(a,v) == ty ==> //TODO: Potential trigger issue (see Dafny warning)
                                              var res := EvalExpr(a, e, s[x := v]); 
                                              res.Some? && TypeOfVal(a, res.value) == TPrim (TBool) then
                                  Some(LitV(LitBool(false)))
                              else 
                                  None //ill-typed
    case Binder(ExistsQ, x, ty, e) => None //TODO
  }

  function ExprEvalBoolOpt<A(!new)>(a: absval_interp<A>, e: Expr, s: state<A>) : Option<bool>
  {
    match EvalExpr(a, e, s)
    case Some(LitV(LitBool(b))) => Some(b)
    case _ => None
  }

  function ExprEvalTy<A(!new)>(a: absval_interp<A>, e: Expr, s: state<A>, t: Ty) : bool
  {
    var v := EvalExpr(a, e, s);
    v.Some? && TypeOfVal(a, v.value) == t
  }

  datatype WpPost = WpPost(normal: Expr, currentScope: Expr, scopes: map<lbl_name, Expr>)

  function ForallVarDecls(varDecls: seq<(var_name, Ty)>, e: Expr) : Expr
  {
    if |varDecls| == 0 then e 
    else var (x,t) := varDecls[0]; Binder(ForallQ, x, t, ForallVarDecls(varDecls[1..], e))
  }

  function NumScopesAndLoops(c: Cmd) : nat
  {
    match c
    case Seq(c1, c2) => NumScopesAndLoops(c1) + NumScopesAndLoops(c2)
    case Scope(_, _, body) => 1 + NumScopesAndLoops(body)
    case Loop(_, body) => 1 + NumScopesAndLoops(body)
    case If(_, thn, els) => NumScopesAndLoops(thn) + NumScopesAndLoops(els)
    case _ => 0
  }

  function LoopDesugaring(invs: seq<Expr>, loopBody: Cmd) : Cmd
  {
      var loopTargets := ModifiedVars(loopBody);
      var invsConj := NAryBinOp(And, ELit(Lit.TrueLit), invs);

      var body' := [
        SimpleCmd(Assert(invsConj)), 
        SimpleCmd(Havoc(loopTargets)), 
        SimpleCmd(Assume(invsConj)), 
        loopBody,  
        SimpleCmd(Assert(invsConj)), 
        SimpleCmd(Assume(ELit(Lit.FalseLit)))
      ];

      SeqToCmd(body')
  }

  lemma LoopDesugaringLabelsWellDef(invs: seq<Expr>, loopBody: Cmd, activeLabels: set<lbl_name>)
    requires LabelsWellDefAux(loopBody, activeLabels)
    ensures LabelsWellDefAux(LoopDesugaring(invs, loopBody), activeLabels)
  {
      var body' := LoopDesugaring(invs, loopBody);
      var loopTargets := ModifiedVars(loopBody);
      var invsConj := NAryBinOp(And, ELit(Lit.TrueLit), invs);

      calc {
        LabelsWellDefAux(body', activeLabels);
        LabelsWellDefAux(SeqToCmd([SimpleCmd(Havoc(loopTargets)), SimpleCmd(Assume(invsConj)), loopBody,  SimpleCmd(Assert(invsConj)), SimpleCmd(Assume(ELit(Lit.FalseLit)))]), activeLabels);
        LabelsWellDefAux(SeqToCmd([SimpleCmd(Assume(invsConj)), loopBody,  SimpleCmd(Assert(invsConj)), SimpleCmd(Assume(ELit(Lit.FalseLit)))]), activeLabels);
        LabelsWellDefAux(SeqToCmd([loopBody,  SimpleCmd(Assert(invsConj)), SimpleCmd(Assume(ELit(Lit.FalseLit)))]), activeLabels);
        LabelsWellDefAux(loopBody, activeLabels) && LabelsWellDefAux(SeqToCmd([SimpleCmd(Assert(invsConj)), SimpleCmd(Assume(ELit(Lit.FalseLit)))]), activeLabels);
        LabelsWellDefAux(loopBody, activeLabels);
      }
  }

  lemma LoopDesugaringNumScopesAndLoops(invs: seq<Expr>, loopBody: Cmd)
    ensures NumScopesAndLoops(loopBody) == NumScopesAndLoops(LoopDesugaring(invs, loopBody))
  {
      var body' := LoopDesugaring(invs, loopBody);
      var loopTargets := ModifiedVars(loopBody);
      var invsConj := NAryBinOp(And, ELit(Lit.TrueLit), invs);

      calc {
        NumScopesAndLoops(body');
        NumScopesAndLoops(SeqToCmd([SimpleCmd(Havoc(loopTargets)), SimpleCmd(Assume(invsConj)), loopBody,  SimpleCmd(Assert(invsConj)), SimpleCmd(Assume(ELit(Lit.FalseLit)))]));
        NumScopesAndLoops(SeqToCmd([SimpleCmd(Assume(invsConj)), loopBody,  SimpleCmd(Assert(invsConj)), SimpleCmd(Assume(ELit(Lit.FalseLit)))]));
        NumScopesAndLoops(SeqToCmd([loopBody,  SimpleCmd(Assert(invsConj)), SimpleCmd(Assume(ELit(Lit.FalseLit)))]));
        NumScopesAndLoops(loopBody) + NumScopesAndLoops(SeqToCmd([SimpleCmd(Assert(invsConj)), SimpleCmd(Assume(ELit(Lit.FalseLit)))]));
        NumScopesAndLoops(loopBody);
      }
  }

  function WpDeep(c: Cmd, post: WpPost): Expr
    requires LabelsWellDefAux(c, post.scopes.Keys)
    decreases NumScopesAndLoops(c), c
  {
    match c 
    case SimpleCmd(Skip) => post.normal
    case SimpleCmd(Assert(e)) => BinOp(e, And, post.normal)
    case SimpleCmd(Assume(e)) => BinOp(e, Imp, post.normal)
    case SimpleCmd(Assign(x, _, e)) => SubstExpr(post.normal, x, e)
    case SimpleCmd(Havoc(vdecls)) => ForallVarDecls(vdecls, post.normal)
    case Break(optLabel) => if optLabel.Some? then post.scopes[optLabel.value] else post.currentScope 
    case Seq(c1, c2) => WpDeep(c1, WpPost(WpDeep(c2, post), post.currentScope, post.scopes)) 
    case Scope(optLabel, varDecls, body) => 
      var updatedScopes := 
        if optLabel.Some? then 
          post.scopes[optLabel.value := post.normal]
        else post.scopes;
      
      assert updatedScopes.Keys == if optLabel.Some? then {optLabel.value} + post.scopes.Keys else post.scopes.Keys;
      assert NumScopesAndLoops(Seq(SimpleCmd(Havoc(varDecls)), body)) == NumScopesAndLoops(body);
      WpDeep(Seq(SimpleCmd(Havoc(varDecls)), body), WpPost(post.normal, post.normal, updatedScopes))
    case If(condOpt, thn, els) => 
      match condOpt {
        case Some(cond) => 
          BinOp(BinOp(cond, Imp, WpDeep(thn, post)), 
                And,
                BinOp(cond, Imp, WpDeep(els, post)))
        case None =>
          BinOp(WpDeep(thn, post), 
                And,
                WpDeep(els, post))
      }
    case Loop(invs, body) => 
      var loopTargets := ModifiedVars(body);
      var invsConj := NAryBinOp(And, ELit(Lit.TrueLit), invs);
      /*BinOp(invsConj, And, 
            ForallVarDecls(loopTargets, 
              BinOp(invsConj, Imp, WpDeep(body, WpPost(invsConj, post.currentScope, post.scopes))))
      )*/

      assert LabelsWellDefAux(body, post.scopes.Keys);

      var body' := [SimpleCmd(Assert(invsConj)), SimpleCmd(Havoc(loopTargets)), SimpleCmd(Assume(invsConj)), body,  SimpleCmd(Assert(invsConj)), SimpleCmd(Assume(ELit(Lit.FalseLit)))];

      
      LoopDesugaringNumScopesAndLoops(invs, body);
      LoopDesugaringLabelsWellDef(invs, body, post.scopes.Keys);

      WpDeep(SeqToCmd(body'), post)
  }

  type Predicate<!A> = state<A> -> Option<bool>
  datatype WpPostShallow<!A> = WpPostShallow(normal: Predicate<A>, currentScope: Predicate<A>, scopes: map<lbl_name, Predicate<A>>)

  function WpShallowSimpleCmd<A(!new)>(a: absval_interp<A>, sc: SimpleCmd, post: Predicate<A>) : Predicate<A>
  {
    match sc
    case Skip => post
    case Assume(e) => 
      s => 
        var postEval :- post(s); 
        var eEval :- ExprEvalBoolOpt(a, e, s); 
        Some(eEval ==> postEval)
    case Assert(e) =>
      s => 
        var postEval :- post(s); 
        var eEval :- ExprEvalBoolOpt(a, e, s); 
        Some(eEval && postEval) 
    case Havoc(varDecls) =>
      ForallVarDeclsShallow(a, varDecls, post)
    case Assign(x, t, e) => 
      s => 
        var eEval :- EvalExpr(a, e, s); 
        post(s[x := eEval])
  }

  function WpShallowSimpleCmdConj<A(!new)>(a: absval_interp<A>, simpleCmds: seq<SimpleCmd>, post: Predicate<A>) : Predicate<A>
  {
    if |simpleCmds| == 0 then post
    else
      s =>
        var res1 :- WpShallowSimpleCmd(a, simpleCmds[0], post)(s);
        var res2 :- WpShallowSimpleCmdConj(a, simpleCmds[1..], post)(s);
        Some(res1 && res2)
  }

  function WpShallow<A(!new)>(a: absval_interp<A>, c: Cmd, post: WpPostShallow<A>) : Predicate<A>
    requires LabelsWellDefAux(c, post.scopes.Keys)
    decreases NumScopesAndLoops(c), c
  {
    match c
    case SimpleCmd(sc) => WpShallowSimpleCmd(a, sc, post.normal)
    case Break(optLabel) => if optLabel.Some? then post.scopes[optLabel.value] else post.currentScope 
    case Seq(c1, c2) => WpShallow(a, c1, WpPostShallow(WpShallow(a, c2, post), post.currentScope, post.scopes))
    case Scope(optLabel, varDecls, body) => 
      var updatedScopes := 
        if optLabel.Some? then 
          post.scopes[optLabel.value := post.normal]
        else post.scopes;
      var unquantifiedScopes := 
        assert updatedScopes.Keys == if optLabel.Some? then {optLabel.value} + post.scopes.Keys else post.scopes.Keys;
        WpShallow(a, body, WpPostShallow(post.normal, post.normal, updatedScopes));
        /* note that this is correct only if scopes do not share variables (otherwise it could happen that the forall 
          quantifier binds variables of the same beyond the current scope) */
        ForallVarDeclsShallow(a, varDecls, unquantifiedScopes)
    case If(optCond, thn, els) =>
      match optCond {
        case Some(cond) => 
          s => 
            var condEval :- ExprEvalBoolOpt(a, cond, s);
            if(condEval) then
                WpShallow(a, thn, post)(s)
              else 
                WpShallow(a, els, post)(s)
        case None =>
          s => 
            var thnRes :- WpShallow(a, thn, post)(s);
            var elsRes :- WpShallow(a, els, post)(s);
            Some(thnRes && elsRes)
      }
    case Loop(invs, body) => 
      var loopTargets := ModifiedVars(body);
      var invsConj := NAryBinOp(And, ELit(Lit.TrueLit), invs);

      var body' := [SimpleCmd(Assert(invsConj)), SimpleCmd(Havoc(loopTargets)), SimpleCmd(Assume(invsConj)), body,  SimpleCmd(Assert(invsConj)), SimpleCmd(Assume(ELit(Lit.FalseLit)))];

      LoopDesugaringNumScopesAndLoops(invs, body);
      LoopDesugaringLabelsWellDef(invs, body, post.scopes.Keys);

      WpShallow(a, SeqToCmd(body'), post)
  }

  function ForallVarDeclsShallow<A(!new)>(a: absval_interp<A>, varDecls: seq<(var_name, Ty)>, p: Predicate<A>) : Predicate<A>
  {
    if |varDecls| == 0 then (s => p(s))
    else var (x,t) := varDecls[0]; 
         s => 
            if (forall v: Val<A> :: TypeOfVal(a, v) == t ==> ForallVarDeclsShallow(a, varDecls[1..], p)(s[x := v]) == Some(true)) then
              Some(true)
            else if (exists v: Val<A> :: TypeOfVal(a, v) == t &&
                        ForallVarDeclsShallow(a, varDecls[1..], p)(s[x := v]) == None) then
              None
            else
              Some(false)
  }

  lemma ForallVarDeclsPointwise<A(!new)>(a: absval_interp<A>, varDecls: seq<(var_name, Ty)>, P: Predicate<A>, Q: Predicate<A>, s: state<A>)
  requires forall s: state<A> :: P(s) == Q(s)
  ensures ForallVarDeclsShallow(a, varDecls, P)(s) == ForallVarDeclsShallow(a, varDecls, Q)(s)
  {
      if |varDecls| == 0 {
          //trivial from precondition P(s) == Q(s)
      } else {
          var (x,t) := varDecls[0];
          forall v: Val<A> | true
              ensures ForallVarDeclsShallow(a, varDecls[1..], P)(s[x := v]) == ForallVarDeclsShallow(a, varDecls[1..], Q)(s[x := v])
          {
              ForallVarDeclsPointwise(a, varDecls[1..], P, Q, s[x := v]);
          }
      }
  }

  lemma WpShallowPointwise<A(!new)>(a: absval_interp<A>, c: Cmd, P: WpPostShallow, Q: WpPostShallow, s: state<A>)
  requires LabelsWellDefAux(c, P.scopes.Keys) && LabelsWellDefAux(c, Q.scopes.Keys)
  requires (forall s' :: P.normal(s') == Q.normal(s'))
  requires (forall s' :: P.currentScope(s') == Q.currentScope(s'))
  requires (forall lbl, s' :: lbl in P.scopes.Keys && lbl in Q.scopes.Keys ==> P.scopes[lbl](s') == Q.scopes[lbl](s'))
  ensures WpShallow(a, c, P)(s) == WpShallow(a, c, Q)(s)
  decreases NumScopesAndLoops(c), c
  {
      match c
      case Seq(c1, c2) =>
        forall s':state<A> | true
            ensures WpShallow(a, c2, P)(s') == WpShallow(a, c2, Q)(s')
        {
            WpShallowPointwise(a, c2, P, Q, s');
        }
      case If(optCond, thn, els) => 
        WpShallowPointwise(a, thn, P, Q, s); //why does Dafny not infer these calls automatically
        WpShallowPointwise(a, els, P, Q, s);
      case Scope(optLabel, varDecls, body) => 
        var updatedScopesP := if optLabel.Some? then P.scopes[optLabel.value := P.normal] else P.scopes;
        assert updatedScopesP.Keys == if optLabel.Some? then {optLabel.value} + P.scopes.Keys else P.scopes.Keys;

        var updatedScopesQ := if optLabel.Some? then Q.scopes[optLabel.value := Q.normal] else Q.scopes;
        assert updatedScopesQ.Keys == if optLabel.Some? then {optLabel.value} + Q.scopes.Keys else Q.scopes.Keys;

        var P' := WpPostShallow(P.normal, P.normal, updatedScopesP);
        var Q' := WpPostShallow(Q.normal, Q.normal, updatedScopesQ);

        forall s' | true
        ensures WpShallow(a, body, P')(s') == WpShallow(a, body, Q')(s')
        {
            WpShallowPointwise(a, body, P', Q', s');
        }

        calc {
            WpShallow(a, c, P)(s); 
            ForallVarDeclsShallow(a, varDecls, WpShallow(a, body, P'))(s);
            { ForallVarDeclsPointwise(a, varDecls, WpShallow(a, body, P'), WpShallow(a, body, Q'), s); }
            ForallVarDeclsShallow(a, varDecls, WpShallow(a, body, Q'))(s);
            WpShallow(a, c, Q)(s);
        }
      case Loop(invs, body) => 
        var body' := LoopDesugaring(invs, body);
        LoopDesugaringLabelsWellDef(invs, body, P.scopes.Keys); //needed to prove precondition of recursive call
        LoopDesugaringLabelsWellDef(invs, body, Q.scopes.Keys); //needed to prove precondition of recursive call
        LoopDesugaringNumScopesAndLoops(invs, body); //needed for termination
        assert NumScopesAndLoops(body) == NumScopesAndLoops(body'); //needed for termination
        //WpShallowPointwise(a, body', P, Q, s); //this call is inferred by Dafny, which surprises me
      case SimpleCmd(Havoc(varDecls)) =>
        ForallVarDeclsPointwise(a, varDecls, P.normal, Q.normal, s);
      case _ => 
  }

  /* TODO
    function ImpliesOpt<A(!new)>(a: Option<bool>, b: Option<bool>):bool
    {
        a.None? || (a.Some? && b.Some? && a.value ==> b.value)
    }

    lemma WpShallowNormalMono<A(!new)>(a: absval_interp<A>, c: Cmd, s: state<A>, P: WpPostShallow, Q: WpPostShallow)
    requires LabelsWellDefAux(c, P.scopes.Keys) && LabelsWellDefAux(c, Q.scopes.Keys)
    requires (forall s' :: ImpliesOpt<A>(P.normal(s'), Q.normal(s'))) && P.currentScope == Q.currentScope && P.scopes == Q.scopes
    ensures ImpliesOpt<A>(WpShallow(a, c, P)(s), WpShallow(a, c, Q)(s))
  */
}
