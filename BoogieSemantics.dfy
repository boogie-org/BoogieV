include "BoogieLang.dfy"
include "BoogieOp.dfy"
include "dafny-libraries/src/Collections/Sequences/Seq.dfy"
include "dafny-libraries/src/Collections/Maps/Maps.dfy"

module BoogieSemantics {
  import opened BoogieLang
  import opened Wrappers
  import opened Util
  import opened BoogieOp

  import Sequences = Seq
  import Maps

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
    case Binder(ForallQ, x, ty, e) =>  
    if forall v :: TypeOfVal(a,v) == ty ==> EvalExpr(a, e, s[x := v]) == Some(LitV(LitBool(true))) then 
                                  Some(LitV(LitBool(true))) 
                              else if forall v {:trigger s[x := v]} :: TypeOfVal(a,v) == ty ==> //TODO: Potential trigger issue (see Dafny warning)
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

  function ForallVarDeclsExpr(varDecls: seq<(var_name, Ty)>, e: Expr) : Expr
  {
    if |varDecls| == 0 then e 
    else var (x,t) := varDecls[0]; Binder(ForallQ, x, t, ForallVarDeclsExpr(varDecls[1..], e))
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

  type Predicate<!A> = state<A> -> Option<bool>
  datatype WpPost<!A> = WpPost(normal: Predicate<A>, currentScope: Predicate<A>, scopes: map<lbl_name, Predicate<A>>)

  /** Note that for the weakest precondition definition making changes such as rewriting a predicate P
      to "s => P(s)" can have an impact on proofs. The reason is that in Dafny P and "s => P(s)" are not 
      necessarily the same predicate. Some lemmas aim to show that a predicate computed by the weakest precondition
      is actually the same as some other predicate (instead of just showing pointwise equality), 
      which relies on the fact on the syntactic expression used to express a predicate. */
  function WpSimpleCmd<A(!new)>(a: absval_interp<A>, sc: SimpleCmd, post: Predicate<A>) : Predicate<A>
  {
    match sc
    case Skip => post
    case Assume(e) => 
      s => 
        var eEval := ExprEvalBoolOpt(a, e, s); 
        /* We make sure that if e evaluates to false, then the weakest precondition is always true.
           An alternative would be to evaluate to None if the postcondition evaluates to None.
           One reason for choosing to evaluate to true is that in an operational semantics, the part
           after the assume command would never be evaluated. Also one obtains more direct 
           equalities such as the Wps of if(b) { thn } else { els } being pointwise equal to 
           If(*) {Assume(guard);thn} else { Assume(!guard), els }.
        */
           
        if eEval == None then
          None
        else if eEval == Some(false) then
          Some(true)
        else 
          var postEval :- post(s); 
          Some(postEval)
    case Assert(e) =>
      s => 
        /* If e evaluates to false, then the Wp is directly false reflecting 
        that if an assertion fails, then the remainder of the program is irrelevant
        (in particular, if the remainder is not well-typed does not matter),
        which is analogous to how we treat Assume(false). */ 
        var eEval := ExprEvalBoolOpt(a, e, s); 
        if eEval == None then
          None
        else if eEval == Some(false) then
          Some(false)
        else 
          var postEval :- post(s); 
          Some(postEval) 
    case Havoc(varDecls) =>
      ForallVarDecls(a, varDecls, post)
    case Assign(x, t, e) => 
      s => 
        var eEval :- EvalExpr(a, e, s); 
        post(s[x := eEval])
    case SeqSimple(sc1, sc2) =>
      WpSimpleCmd(a, sc1, WpSimpleCmd(a, sc2, post))
  }

  function WpShallowSimpleCmdSeq<A(!new)>(a: absval_interp<A>, simpleCmds: seq<SimpleCmd>, post: Predicate<A>) : Predicate<A>
  {
    if |simpleCmds| == 0 then post
    else
      s =>
        var res2 := WpShallowSimpleCmdSeq(a, simpleCmds[1..], post);
        WpSimpleCmd(a, simpleCmds[0], res2)(s)
  }

  function {:opaque} WpCmd<A(!new)>(a: absval_interp<A>, c: Cmd, post: WpPost<A>) : Predicate<A>
    requires LabelsWellDefAux(c, post.scopes.Keys)
    decreases NumScopesAndLoops(c), c
  {
    match c
    case SimpleCmd(sc) => WpSimpleCmd(a, sc, post.normal)
    case Break(optLabel) => if optLabel.Some? then post.scopes[optLabel.value] else post.currentScope 
    case Seq(c1, c2) => WpCmd(a, c1, WpPost(WpCmd(a, c2, post), post.currentScope, post.scopes))
    case Scope(optLabel, varDecls, body) => 
      var updatedScopes := 
        if optLabel.Some? then 
          post.scopes[optLabel.value := post.normal]
        else post.scopes;

      assert updatedScopes.Keys == if optLabel.Some? then {optLabel.value} + post.scopes.Keys else post.scopes.Keys;
      var post' := WpPost(post.normal, post.normal, updatedScopes);
      
      s => ForallVarDecls( a, varDecls, WpCmd(a, body, ResetVarsPost(varDecls, post', s)) )(s)
    case If(optCond, thn, els) =>
      match optCond {
        case Some(cond) => 
          s => 
            var condEval :- ExprEvalBoolOpt(a, cond, s);
            if(condEval) then
                WpCmd(a, thn, post)(s)
              else 
                WpCmd(a, els, post)(s)
        case None =>
          s => 
            var thnRes :- WpCmd(a, thn, post)(s);
            var elsRes :- WpCmd(a, els, post)(s);
            Some(thnRes && elsRes)
      }
    case Loop(invs, body) => 
      var loopTargets := ModifiedVars(body);
      var invsConj := NAryBinOp(And, ELit(Lit.TrueLit), invs);

      var body' := [SimpleCmd(Assert(invsConj)), SimpleCmd(Havoc(loopTargets)), SimpleCmd(Assume(invsConj)), body,  SimpleCmd(Assert(invsConj)), SimpleCmd(Assume(ELit(Lit.FalseLit)))];

      LoopDesugaringNumScopesAndLoops(invs, body);
      LoopDesugaringLabelsWellDef(invs, body, post.scopes.Keys);

      WpCmd(a, SeqToCmd(body'), post)
  }


  predicate ValuesRespectDecls<A>(a: absval_interp<A>, vs: seq<Val<A>>, varDecls: seq<(var_name, Ty)>)
  {
    TypeOfValues(a, vs) == seq(|varDecls|, i requires 0 <= i < |varDecls| => varDecls[i].1)
  }

  function StateUpdVarDecls<A>(s: state<A>, varDecls: seq<(var_name, Ty)>, vs: seq<Val<A>>) : state<A>
    requires |varDecls| == |vs|
    ensures StateUpdVarDecls(s, varDecls, vs).Keys == s.Keys + GetVarNames(varDecls)
  {
    if |varDecls| == 0 then 
      s
    else 
      var s' := StateUpdVarDecls(s, varDecls[1..], vs[1..]);
      var res := s'[varDecls[0].0 := vs[0]];
      res
  }

  lemma StateUpdVarDeclsLookup1<A>(s: state<A>, varDecls: seq<(var_name, Ty)>, vs: seq<Val<A>>, k: var_name)
    requires |varDecls| == |vs|
    requires k !in GetVarNames(varDecls)
    ensures Maps.Get(StateUpdVarDecls(s, varDecls, vs), k) == Maps.Get(s, k)
  { }

  function {:opaque} ForallVarDecls<A(!new)>(a: absval_interp<A>, varDecls: seq<(var_name, Ty)>, p: Predicate<A>) : Predicate<A>
  {
    if |varDecls| == 0 then p
    else 
      s => 
        if forall vs | ValuesRespectDecls(a, vs, varDecls) :: p(StateUpdVarDecls(s, varDecls, vs)).Some? then
          Some(forall vs | ValuesRespectDecls(a, vs, varDecls) :: p(StateUpdVarDecls(s, varDecls, vs)) == Some(true))
        else
          None
  }

  function {:opaque} ForallVarDeclsOld<A(!new)>(a: absval_interp<A>, varDecls: seq<(var_name, Ty)>, p: Predicate<A>) : Predicate<A>
  {
    if |varDecls| == 0 then p
    else var (x,t) := varDecls[0]; 
         s => 
          if (forall v: Val<A> | TypeOfVal(a, v) == t :: ForallVarDeclsOld(a, varDecls[1..], p)(s[x := v]).Some?) then
            Some((forall v: Val<A> | TypeOfVal(a, v) == t :: ForallVarDeclsOld(a, varDecls[1..], p)(s[x := v]) == Some(true)))
          else
            None
  }
  /*
  predicate StateUpdVarDecls2<A>(s: state<A>, s': state<A>, varDecls: seq<(var_name, Ty)>, vs: seq<Val<A>>)
    requires |varDecls| == |vs|
  {
    && (forall i | 0 <= i < |varDecls| :: varDecls[i].0 in s'.Keys && s'[varDecls[i].0] == vs[i])
    && (forall k | k !in GetVarNames(varDecls) :: Maps.Get(s, k) == Maps.Get(s', k))
  }

  lemma StateUpdVarDeclsEquiv<A>(s: state<A>, varDecls: seq<(var_name, Ty)>, vs: seq<Val<A>>)
  requires |varDecls| == |vs|
  requires Sequences.HasNoDuplicates(varDecls)
  ensures StateUpdVarDecls2(s, StateUpdVarDecls(s, varDecls, vs), varDecls, vs)
  {
    if (|varDecls| == 0) {

    } else {
      var s' := StateUpdVarDecls(s, varDecls[1..], vs[1..]);

      assert StateUpdVarDecls2()
    }
  }
  */

  lemma ForallVarDeclsEmpty<A(!new)>(a: absval_interp<A>, p: Predicate<A>)
    ensures ForallVarDecls(a, [], p) == p
  {
    reveal ForallVarDecls();
  }


  lemma SomeForallVarDecls<A(!new)>(a: absval_interp<A>, varDecls: seq<(var_name, Ty)>, p: Predicate<A>, s: state<A>)
    requires ForallVarDecls(a, varDecls, p)(s) != None
    requires |varDecls| > 0
    ensures 
      var (x,t) := varDecls[0];
      ForallVarDecls(a, varDecls, p)(s) ==
      Some(forall vs | ValuesRespectDecls(a, vs, varDecls) :: p(StateUpdVarDecls(s, varDecls, vs)) == Some(true))
  {
    reveal ForallVarDecls();
  }

  lemma SomeForallVarDecls2<A(!new)>(a: absval_interp<A>, varDecls: seq<(var_name, Ty)>, p: Predicate<A>, s: state<A>,
    vs: seq<Val<A>>)
    requires ForallVarDecls(a, varDecls, p)(s) != None
    requires ValuesRespectDecls(a, vs, varDecls)
    requires |varDecls| > 0
    ensures 
      p(StateUpdVarDecls(s, varDecls, vs)).Some?
  {
    reveal ForallVarDecls();
  }

  lemma  ForallVarDeclsEquiv<A(!new)>(
      a: absval_interp<A>, 
      varDecls: seq<VarDecl>, 
      varDecls': seq<VarDecl>, 
      p1: Predicate<A>, 
      p2: Predicate<A>,
      s1: state<A>,
      s2: state<A>)
    requires 
      && |varDecls| == |varDecls'|
      && (forall vs :: ValuesRespectDecls(a, vs, varDecls) == ValuesRespectDecls(a, vs, varDecls'))
      && (forall vs | ValuesRespectDecls(a, vs, varDecls) :: 
          p1(StateUpdVarDecls(s1, varDecls, vs)) == p2(StateUpdVarDecls(s2, varDecls', vs)))
    ensures 
      ForallVarDecls(a, varDecls, p1)(s1) == ForallVarDecls(a, varDecls', p2)(s2)
    {
      reveal ForallVarDecls();
      if |varDecls| == 0 {
        assert p1(s1) == p2(s2) by {
          //need this for Dafny to trigger the quantifier
          assert ValuesRespectDecls(a, [], []);  
        }
      }
    }

  function ResetVarsPost<A(!new)>(varDecls: seq<(var_name,Ty)>, p: WpPost<A>, s: state<A>) : WpPost<A>
    ensures p.scopes.Keys == ResetVarsPost(varDecls, p, s).scopes.Keys
  {
    var newScopes := map lbl | lbl in p.scopes.Keys :: ResetVarsPred(varDecls, p.scopes[lbl], s);
    WpPost(ResetVarsPred(varDecls, p.normal, s), ResetVarsPred(varDecls, p.currentScope, s), newScopes)
  }

  function ResetVarsState<A(!new)>(varDecls: seq<(var_name,Ty)>, s: state<A>, sOrig: state<A>) : state<A>
  {
    if |varDecls| == 0 then 
      s
    else
      var x := varDecls[0].0;
      var s' := ResetVarsState(varDecls[1..], s, sOrig);
      if x in sOrig.Keys then
        s'[x := sOrig[x]]
      else
        s'-{x}
  }

  function ResetVarsPred<A(!new)>(varDecls: seq<(var_name,Ty)>, p: Predicate<A>, s: state<A>) : Predicate<A>
  {
    /* then-branch is used to keep the exact same predicate in the empty case 
       (the else branch would work for the empty case, but then one only gets 
       pointwise equality to p) */
    if |varDecls| == 0 then p else s' => p(ResetVarsState(varDecls, s', s))
  }

  //earlier resets override later resets
  lemma ResetVarsPredOverwrite<A(!new)>(x: var_name, t: Ty, sOrig1: state<A>, sOrig2: state<A>, sNew: state<A>, pred: Predicate<A>)
    requires forall s' :: Maps.Get(s', x) == Maps.Get(sOrig1, x) ==> pred(s') == Some(true)
    ensures ResetVarsPred([(x,t)], ResetVarsPred([(x,t)], pred, sOrig1), sOrig2)(sNew) == Some(true)
  {
    calc {
      ResetVarsPred([(x,t)], ResetVarsPred([(x,t)], pred, sOrig1), sOrig2)(sNew);
      ResetVarsPred([(x,t)], pred, sOrig1)(ResetVarsState([(x,t)], sNew, sOrig2));
      pred(ResetVarsState([(x,t)], ResetVarsState([(x,t)], sNew, sOrig2), sOrig1));
    }
  }

  lemma ResetVarsPredNoVars<A(!new)>(a: absval_interp<A>, p: Predicate<A>)
    ensures forall origState, s' :: ResetVarsPred([], p, origState)(s') == p(s')
  { }

  lemma ResetVarsPostNoVars<A(!new)>(a: absval_interp<A>, p: WpPost<A>, origState: state<A>)
    requires 
      var q := ResetVarsPost([], p, origState);
      && (forall s' :: p.normal(s') == q.normal(s'))
      && (forall s' :: p.currentScope(s') == q.currentScope(s'))
      && (forall lbl, s' :: lbl in p.scopes.Keys && lbl in q.scopes.Keys ==> p.scopes[lbl](s') == q.scopes[lbl](s'))
  { }

  lemma ResetVarsPredPointwise<A(!new)>(a: absval_interp<A>, varDecls: seq<(var_name,Ty)>, p: Predicate<A>, q: Predicate<A>, resetState: state<A>, s: state<A>) 
    requires forall s :: p(s) == q(s)
    ensures forall s :: ResetVarsPred(varDecls, p, resetState)(s) == ResetVarsPred(varDecls, q, resetState)(s)
  { }

  lemma ResetVarsPostPointwise<A(!new)>(a: absval_interp<A>, varDecls: seq<(var_name,Ty)>, post1: WpPost<A>, post2: WpPost<A>, resetState: state<A>, s: state<A>) 
    requires forall s :: post1.normal(s) == post2.normal(s)
    requires forall s :: post1.currentScope(s) == post2.currentScope(s)
    requires forall s, lbl :: lbl in post1.scopes.Keys && lbl in post2.scopes.Keys ==> post1.scopes[lbl](s) == post2.scopes[lbl](s)
    ensures 
      var post1' := ResetVarsPost(varDecls, post1, resetState);
      var post2' := ResetVarsPost(varDecls, post2, resetState);
      && (forall s :: post1'.normal(s) == post2'.normal(s))
      && (forall s :: post1'.currentScope(s) == post2'.currentScope(s))
      && (forall s, lbl :: lbl in post1'.scopes.Keys && lbl in post2'.scopes.Keys ==> post1'.scopes[lbl](s) == post2'.scopes[lbl](s))
  { 
    var post1' := ResetVarsPost(varDecls, post1, resetState);
    var post2' := ResetVarsPost(varDecls, post2, resetState);
    forall s | true 
    ensures post1'.normal(s) == post2'.normal(s)
    {
      ResetVarsPredPointwise(a, varDecls, post1.normal, post2.normal, resetState, s);
    }

    forall s | true 
    ensures post1'.currentScope(s) == post2'.currentScope(s)
    {
      ResetVarsPredPointwise(a, varDecls, post1.currentScope, post2.currentScope, resetState, s);
    }

    forall s, lbl 
    ensures lbl in post1'.scopes.Keys && lbl in post2'.scopes.Keys ==> post1'.scopes[lbl](s) == post2'.scopes[lbl](s)
    {
      if(lbl in post1.scopes.Keys && lbl in post2.scopes.Keys){
        ResetVarsPredPointwise(a, varDecls, post1.scopes[lbl], post2.scopes[lbl], resetState, s);
      }
    }
  }

  lemma ForallVarDeclsPointwise<A(!new)>(a: absval_interp<A>, varDecls: seq<(var_name, Ty)>, P: Predicate<A>, Q: Predicate<A>, s: state<A>)
  requires forall s: state<A> :: P(s) == Q(s)
  ensures ForallVarDecls(a, varDecls, P)(s) == ForallVarDecls(a, varDecls, Q)(s)
  {
    reveal ForallVarDecls();
      /* proof below needed when using the recursive version of ForallVarDecls
      reveal ForallVarDecls();
      if |varDecls| == 0 {
          //trivial from precondition P(s) == Q(s)
      } else {
          var (x,t) := varDecls[0];
          forall v: Val<A> | true
              ensures ForallVarDecls(a, varDecls[1..], P)(s[x := v]) == ForallVarDecls(a, varDecls[1..], Q)(s[x := v])
          {
              ForallVarDeclsPointwise(a, varDecls[1..], P, Q, s[x := v]);
          }
      }
      */
  }

  lemma WpSimpleCmdPointwise<A(!new)>(a: absval_interp<A>, sc: SimpleCmd, P: Predicate<A>, Q: Predicate<A>, s: state<A>)
  requires (forall s' :: P(s') == Q(s'))
  ensures WpSimpleCmd(a, sc, P)(s) == WpSimpleCmd(a, sc, Q)(s)
  {
    match sc
    case Havoc(varDecls) =>
      ForallVarDeclsPointwise(a, varDecls, P, Q, s);
    case SeqSimple(sc1, sc2) =>
      forall s':state<A> | true
        ensures WpSimpleCmd(a, sc2, P)(s') == WpSimpleCmd(a, sc2, Q)(s')
      {
        WpSimpleCmdPointwise(a, sc2, P ,Q, s');
      }
    case _ => 
  }

  lemma WpSimpleCmdPointwise2<A(!new)>(a: absval_interp<A>, sc: SimpleCmd, P: Predicate<A>, Q: Predicate<A>)
  requires (forall s' :: P(s') == Q(s'))
  ensures forall s :: WpSimpleCmd(a, sc, P)(s) == WpSimpleCmd(a, sc, Q)(s)
  {
    forall s | true 
    ensures WpSimpleCmd(a, sc, P)(s) == WpSimpleCmd(a, sc, Q)(s)
    {
      WpSimpleCmdPointwise(a, sc, P, Q, s);
    }
  }

  lemma WpCmdPointwise<A(!new)>(a: absval_interp<A>, c: Cmd, P: WpPost, Q: WpPost, s: state<A>)
  requires LabelsWellDefAux(c, P.scopes.Keys) && LabelsWellDefAux(c, Q.scopes.Keys)
  requires (forall s' :: P.normal(s') == Q.normal(s'))
  requires (forall s' :: P.currentScope(s') == Q.currentScope(s'))
  requires (forall lbl, s' :: lbl in P.scopes.Keys && lbl in Q.scopes.Keys ==> P.scopes[lbl](s') == Q.scopes[lbl](s'))
  ensures WpCmd(a, c, P)(s) == WpCmd(a, c, Q)(s)
  decreases NumScopesAndLoops(c), c
  {
      reveal WpCmd();
      match c
      case SimpleCmd(sc) => WpSimpleCmdPointwise(a, sc, P.normal, Q. normal, s);
      case Seq(c1, c2) =>
        forall s':state<A> | true
            ensures WpCmd(a, c2, P)(s') == WpCmd(a, c2, Q)(s')
        {
            WpCmdPointwise(a, c2, P, Q, s');
        }
      case If(optCond, thn, els) => 
        WpCmdPointwise(a, thn, P, Q, s); //why does Dafny not infer these calls automatically
        WpCmdPointwise(a, els, P, Q, s);
      case Scope(optLabel, varDecls, body) => 
        var updatedScopesP := if optLabel.Some? then P.scopes[optLabel.value := P.normal] else P.scopes;
        assert updatedScopesP.Keys == if optLabel.Some? then {optLabel.value} + P.scopes.Keys else P.scopes.Keys;

        var updatedScopesQ := if optLabel.Some? then Q.scopes[optLabel.value := Q.normal] else Q.scopes;
        assert updatedScopesQ.Keys == if optLabel.Some? then {optLabel.value} + Q.scopes.Keys else Q.scopes.Keys;

        var P' := ResetVarsPost(varDecls, WpPost(P.normal, P.normal, updatedScopesP), s);
        var Q' := ResetVarsPost(varDecls, WpPost(Q.normal, Q.normal, updatedScopesQ), s);

        forall s' | true
        ensures WpCmd(a, body, P')(s') == WpCmd(a, body, Q')(s')
        {
            ResetVarsPostPointwise(a, varDecls, WpPost(P.normal, P.normal, updatedScopesP), WpPost(Q.normal, Q.normal, updatedScopesQ), s, s');
            WpCmdPointwise(a, body, P', Q', s');
        }

        calc {
            WpCmd(a, c, P)(s); 
            ForallVarDecls(a, varDecls, WpCmd(a, body, P'))(s);
            { ForallVarDeclsPointwise(a, varDecls, WpCmd(a, body, P'), WpCmd(a, body, Q'), s); }
            ForallVarDecls(a, varDecls, WpCmd(a, body, Q'))(s);
            WpCmd(a, c, Q)(s);
        }
      case Loop(invs, body) => 
        var body' := LoopDesugaring(invs, body);
        LoopDesugaringLabelsWellDef(invs, body, P.scopes.Keys); //needed to prove precondition of recursive call
        LoopDesugaringLabelsWellDef(invs, body, Q.scopes.Keys); //needed to prove precondition of recursive call
        LoopDesugaringNumScopesAndLoops(invs, body); //needed for termination
        assert NumScopesAndLoops(body) == NumScopesAndLoops(body'); //needed for termination
        //WpCmdPointwise(a, body', P, Q, s); //this call is inferred by Dafny, which surprises me
      case _ =>
  }

  function ImpliesOpt(a: Option<bool>, b: Option<bool>):bool
  {
      a.None? || (a.Some? && b.Some? && (a.value ==> b.value))
  }

  /*
  lemma WpShallowSimpleCmdMono<A(!new)>(a: absval_interp<A>, c: SimpleCmd, s: state<A>, P: Predicate<A>, Q: Predicate<A>)
  requires (forall s' :: ImpliesOpt(P(s'), Q(s'))) 
  ensures ImpliesOpt(WpSimpleCmd(a, c, P)(s), WpSimpleCmd(a, c, Q)(s))

  lemma WpShallowSimpleCmdSeqMono<A(!new)>(a: absval_interp<A>, scs: seq<SimpleCmd>, s: state<A>, P: Predicate<A>, Q: Predicate<A>)
  requires (forall s' :: ImpliesOpt(P(s'), Q(s'))) 
  ensures ImpliesOpt(WpShallowSimpleCmdSeq(a, scs, P)(s), WpShallowSimpleCmdSeq(a, scs, Q)(s))
  */
  
  /*
    lemma WpShallowNormalMono<A(!new)>(a: absval_interp<A>, c: Cmd, s: state<A>, P: WpPost, Q: WpPost)
    requires LabelsWellDefAux(c, P.scopes.Keys) && LabelsWellDefAux(c, Q.scopes.Keys)
    requires (forall s' :: ImpliesOpt<A>(P.normal(s'), Q.normal(s'))) && P.currentScope == Q.currentScope && P.scopes == Q.scopes
    ensures ImpliesOpt<A>(WpCmd(a, c, P)(s), WpCmd(a, c, Q)(s))
  */

  /** operational semantics */
  datatype ExtState<A> = NormalState(state<A>) | MagicState | FailureState

  function SequentialMapUpdate<K,V>(m: map<K,V>, keys: seq<K>, values: seq<V>) : map<K,V>
    requires |keys| == |values|
    decreases keys
  {
    if |keys| == 0  
      then m
    else 
      SequentialMapUpdate(m[keys[0] := values[0]], keys[1..], values[1..])
  }

  least predicate SimpleCmdOpSem<A(!new)>(a: absval_interp<A>, sc: SimpleCmd, y: ExtState<A>, y': ExtState<A>)
  {
    match y
    case NormalState(s) => 
      match sc {
      case Skip => y == y'
      case Assume(e) => 
        if(ExprEvalBoolOpt(a, e, s) == Some(true)) then
          y' == y
        else
          y' == MagicState
      case Assert(e) =>
        if(ExprEvalBoolOpt(a, e, s) == Some(true)) then
          y' == y
        else
          y' == FailureState
      case Assign(x, _, e) =>
        var vOpt := EvalExpr(a, e, s);
        match vOpt {
          case Some(v) => y' == NormalState(s[x := v])
          case None => false
        }
      case Havoc(vDecls) =>
        var (varNames,_) := Sequences.Unzip(vDecls);
        exists vs : seq<Val<A>> :: 
          && |vs| == |vDecls|
          && (forall i :: 0 <= i < |vDecls| ==> TypeOfVal(a, vs[i]) == vDecls[i].1)
          && y' == NormalState(SequentialMapUpdate(s, varNames, vs))
      case SeqSimple(sc1, sc2) =>
        exists y'' :: SimpleCmdOpSem(a, sc1, y, y'') && SimpleCmdOpSem(a, sc2, y'', y')
      }
    case MagicState => y == y'
    case FailureState => y == y'
  }

  least predicate SimpleCmdSeqOpSem<A(!new)>(a: absval_interp<A>, scs: seq<SimpleCmd>, y: ExtState<A>, y': ExtState<A>)
  {
    if |scs| == 0 then
      y == y'
    else 
      exists y'' :: SimpleCmdOpSem(a, scs[0], y, y'') && SimpleCmdSeqOpSem(a, scs[1..], y'', y')
  }

}

