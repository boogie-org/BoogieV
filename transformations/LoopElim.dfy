include "../lang/BoogieLang.dfy"
include "../lang/BoogieSemantics.dfy"
include "../util/AstSubsetPredicates.dfy"
include "../dafny-libraries/src/Wrappers.dfy"


module LoopElim {
    import opened BoogieLang
    import opened BoogieSemantics
    import opened Wrappers
    import opened AstSubsetPredicates


    lemma LabelsWellDefSeqToCmd(cs: seq<Cmd>, lbls: set<lbl_name>)
    requires |cs| > 0
    requires LabelsWellDefAux(SeqToCmd(cs), lbls)
    ensures forall i | 0 <= i < |cs| :: LabelsWellDefAux(cs[i], lbls)
    {
        if |cs| == 1 {
        } else {
            var cs' := cs[1..];
            LabelsWellDefSeqToCmd(cs', lbls);
        }
    }

    lemma WpSeqToCmdSingleDiff<A(!new)>(a: absval_interp<A>, cs1: seq<Cmd>, cs2: seq<Cmd>, diffIdx: nat, post: WpPost<A>, s: state<A>)
        requires |cs1| == |cs2|
        requires 0 <= diffIdx < |cs1|
        requires forall i | 0 <= i < |cs1| && i != diffIdx :: cs1[i] == cs2[i] 
        requires LabelsWellDefAux(SeqToCmd(cs1), post.scopes.Keys)
        requires LabelsWellDefAux(SeqToCmd(cs2), post.scopes.Keys)
        requires forall s, post':WpPost<A> | post'.scopes.Keys == post.scopes.Keys :: 
            (LabelsWellDefSeqToCmd(cs1, post.scopes.Keys);
            LabelsWellDefSeqToCmd(cs2, post.scopes.Keys);
            WpCmd(a, cs1[diffIdx], post')(s) == WpCmd(a, cs2[diffIdx], post')(s))
        
        ensures WpCmd(a, SeqToCmd(cs1), post)(s) == WpCmd(a, SeqToCmd(cs2), post)(s)
    {
        reveal WpCmd(); //need this due to opaque bug (otherwise cannot use the quantifier in the precondition)

        if |cs1| == 1 {

        } else {
            calc {
                WpCmd(a, SeqToCmd(cs1), post)(s);
                WpCmd(a, Seq(cs1[0], SeqToCmd(cs1[1..])), post)(s);
                WpCmd(a, cs1[0], WpPost(WpCmd(a, SeqToCmd(cs1[1..]), post), post.currentScope, post.scopes))(s);
                {  
                    forall s' | true 
                    ensures WpCmd(a, SeqToCmd(cs1[1..]), post)(s') == WpCmd(a, SeqToCmd(cs2[1..]), post)(s')
                    {
                        if diffIdx != 0 {
                            WpSeqToCmdSingleDiff(a, cs1[1..], cs2[1..], diffIdx-1, post, s');
                        } else {
                            assert cs1[1..] == cs2[1..];
                        }
                    }

                    WpCmdPointwise(a, cs1[0], WpPost(WpCmd(a, SeqToCmd(cs1[1..]), post), post.currentScope, post.scopes), 
                                              WpPost(WpCmd(a, SeqToCmd(cs2[1..]), post), post.currentScope, post.scopes), s);
                }
                WpCmd(a, cs2[0], WpPost(WpCmd(a, SeqToCmd(cs2[1..]), post), post.currentScope, post.scopes))(s);
                WpCmd(a, Seq(cs2[0], SeqToCmd(cs2[1..])), post)(s);
            }
        }
    }
    
    lemma NoLoopsSeqToCmd(cs: seq<Cmd>)
      requires |cs| > 0
      requires forall c | c in cs :: NoLoops(c);
      ensures NoLoops(SeqToCmd(cs))
    { 
        if |cs| > 1 {
          calc {
            NoLoops(SeqToCmd(cs));
            NoLoops(Seq(cs[0], SeqToCmd(cs[1..])));
            && NoLoops(cs[0])
            && NoLoops(SeqToCmd(cs[1..]));
          }
        }
    }

    function method EliminateLoops(c: Cmd) : Cmd 
    ensures NoLoops(EliminateLoops(c))
    {
        match c
        case Scope(optLbl, varDecls, body) => Scope(optLbl, varDecls, EliminateLoops(body))
        case If(optCond, thn, els) => If(optCond, EliminateLoops(thn), EliminateLoops(els))
        case Loop(invs, body) =>
            var modDecls : seq<(var_name, Ty)> := ModifiedVars(body);
            var invsConj := NAryBinOp(And, Expr.TrueExpr, invs);
            var body' := EliminateLoops(body);

            var seqResult :=
                [ SimpleCmd(Assert(invsConj)),
                SimpleCmd(Havoc(modDecls)),
                SimpleCmd(Assume(invsConj)),
                body',
                SimpleCmd(Assert(invsConj)),
                SimpleCmd(Assume(Expr.FalseExpr))
                ];
            
            assert NoLoops(body');
            NoLoopsSeqToCmd(seqResult);
            
            SeqToCmd(seqResult)
        case Seq(c1, c2) =>
            Seq(EliminateLoops(c1), EliminateLoops(c2))
        case _ => c
    }

    lemma EliminateLoopsCorrect<A(!new)>(a: absval_interp<A>, c: Cmd, s: state<A>, post: WpPost)
    requires LabelsWellDefAux(c, post.scopes.Keys) && LabelsWellDefAux(EliminateLoops(c), post.scopes.Keys)
    ensures  WpCmd(a, EliminateLoops(c), post)(s) == WpCmd(a, c, post)(s)
    {
        reveal WpCmd();
        match c
        case Seq(c1, c2) => 
            var c2Post := WpCmd(a, c2, post);
            var c2ElimPost := WpCmd(a, EliminateLoops(c2), post);

            forall s':state<A> | true
                ensures c2ElimPost(s') == c2Post(s')
            {
                EliminateLoopsCorrect(a, c2, s', post);
            }

            calc {
                WpCmd(a, EliminateLoops(c), post)(s);
                WpCmd(a, c1, WpPost(c2ElimPost, post.currentScope, post.scopes))(s); 
                { 
                    WpCmdPointwise(a, c1, WpPost(c2ElimPost, post.currentScope, post.scopes), WpPost(c2Post, post.currentScope, post.scopes), s);
                }
                WpCmd(a, c1, WpPost(c2Post, post.currentScope, post.scopes))(s);
            }
        case Scope(optLabel, varDecls, body) => 
            var updatedScopes := if optLabel.Some? then post.scopes[optLabel.value := post.normal] else post.scopes;
            assert updatedScopes.Keys == if optLabel.Some? then {optLabel.value} + post.scopes.Keys else post.scopes.Keys;

            var bodyPost := ResetVarsPost(varDecls, WpPost(post.normal, post.normal, updatedScopes), s);

            forall s: state<A> | true 
                ensures WpCmd(a, EliminateLoops(body), bodyPost)(s) == 
                        WpCmd(a, body, bodyPost)(s)
            {
                calc {
                    WpCmd(a, EliminateLoops(body), bodyPost)(s); {EliminateLoopsCorrect(a, body, s, bodyPost); }
                    WpCmd(a, body, bodyPost)(s);
                }
            }
            ForallVarDeclsPointwise(a, varDecls, WpCmd(a, EliminateLoops(body), bodyPost), WpCmd(a, body, bodyPost), s);
        case Loop(invs, body) =>
            LoopDesugaringNumScopesAndLoops(invs, body);
            LoopDesugaringLabelsWellDef(invs, body, post.scopes.Keys);

            var body' := EliminateLoops(body);

            var loopTargets := ModifiedVars(body);
            var invsConj := NAryBinOp(And, Expr.TrueExpr, invs);

            var desugaredLoop := body' => [SimpleCmd(Assert(invsConj)), SimpleCmd(Havoc(loopTargets)), SimpleCmd(Assume(invsConj)), body',  SimpleCmd(Assert(invsConj)), SimpleCmd(Assume(Expr.FalseExpr))];

            assert LabelsWellDefAux(SeqToCmd(desugaredLoop(body)), post.scopes.Keys);
            assert LabelsWellDefAux(SeqToCmd(desugaredLoop(body')), post.scopes.Keys);

            forall s', post' : WpPost<A> | post'.scopes.Keys == post.scopes.Keys
            ensures WpCmd(a, body, post')(s') == WpCmd(a, body', post')(s')
            {
              assert LabelsWellDefAux(body, post.scopes.Keys) by {
                assert desugaredLoop(body)[3] == body;
                LabelsWellDefSeqToCmd(desugaredLoop(body), post.scopes.Keys);
              }

              assert LabelsWellDefAux(body', post.scopes.Keys) by {
                assert desugaredLoop(body')[3] == body';
                LabelsWellDefSeqToCmd(desugaredLoop(body'), post.scopes.Keys);
              }
              EliminateLoopsCorrect(a, body, s', post');
            }

            calc {
                WpCmd(a, Loop(invs, body), post)(s);
                WpCmd(a, SeqToCmd(desugaredLoop(body)), post)(s);
                { WpSeqToCmdSingleDiff(a, desugaredLoop(body), desugaredLoop(body'), 3, post, s); }
                WpCmd(a, SeqToCmd(desugaredLoop(body')), post)(s);
            }
        case _ => //trivial (EliminateLoops is the identity function here)
    }
}