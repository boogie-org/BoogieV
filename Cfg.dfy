
include "BoogieSemantics.dfy"

module BoogieCfg {

  import opened BoogieLang
  import opened BoogieSemantics
  import opened Wrappers

  type BasicBlock = SimpleCmd
  type BlockId = nat 

  datatype Cfg = Cfg(entry: BlockId, blocks: map<BlockId, BasicBlock>, successors: map<BlockId, seq<BlockId>>)

  function CfgWf(g: Cfg) : bool
  {
    g.blocks.Keys == g.successors.Keys &&
    g.entry in g.blocks.Keys &&
    (forall blockId :: blockId in g.successors.Keys ==> 
      (forall i :: 0 <= i < |g.successors[blockId]| ==> g.successors[blockId][i] in g.blocks.Keys))
  }

  type SuccessorRel = map<BlockId, seq<BlockId>>

  function IsAcyclicSeq(r: SuccessorRel, ns: seq<BlockId>, cover: set<BlockId>) : bool
    decreases cover, 1, ns
  {
    |ns| != 0 ==> ( IsAcyclic(r, ns[0], cover) && IsAcyclicSeq(r, ns[1..], cover) )
  }

  function IsAcyclic(r: SuccessorRel, n: BlockId, cover: set<BlockId>) : bool
    decreases cover, 0
  {
    n in r.Keys ==> ( n in cover && IsAcyclicSeq(r, r[n], cover - {n}) )
  }

  function BasicBlockToCmd(block: BasicBlock) : Cmd
  {
    SimpleCmd(block)
  }

  /*=================== Wp semantics ==========================================*/
  datatype WpPostCfg<!A> = WpPostCfg(normal: Predicate<A>, exceptional: map<BlockId, Predicate<A>>)

  function WpCfgConjunction<A(!new)>(
    a: absval_interp<A>, 
    g: Cfg, 
    ns: seq<BlockId>, 
    post: Predicate<A>, 
    cover: set<BlockId>) : Predicate<A>
    requires g.successors.Keys <= g.blocks.Keys //not being in the domain of the successor relation is the same as not having any successors
    requires IsAcyclicSeq(g.successors, ns, cover)
    decreases cover, 1, ns
  { s =>
      if |ns| == 0 then Some(true)
      else 
        var res1 :- WpCfg(a, g, ns[0], post, cover)(s);
        var res2 :- WpCfgConjunction(a, g, ns[1..], post, cover)(s);
        Some(res1 && res2)
  }

  function WpCfg<A(!new)>(a: absval_interp<A>, g: Cfg, n: BlockId, post: Predicate<A>, cover: set<BlockId>) : Predicate<A>
    requires g.successors.Keys <= g.blocks.Keys //not being in the domain of the successor relation is the same as not having any successors
    requires IsAcyclic(g.successors, n, cover)
    decreases cover, 0
  {
    if !(n in g.blocks.Keys) then
      post
    else 
      var successors := if n in g.successors.Keys then g.successors[n] else [];
      if |successors| == 0 then 
        WpShallowSimpleCmd(a, g.blocks[n], post)
      else 
        WpShallowSimpleCmd(a, g.blocks[n], WpCfgConjunction(a, g, successors, post, cover - {n}))
  }


  lemma WpCfgConjunctionPointwise<A(!new)>(a: absval_interp<A>, g: Cfg, ns: seq<BlockId>, post1: Predicate<A>, post2: Predicate<A>, cover: set<BlockId>, s: state<A>) 
    requires g.successors.Keys <= g.blocks.Keys //not being in the domain of the successor relation is the same as not having any successors
    requires IsAcyclicSeq(g.successors, ns, cover)
    requires (forall s :: post1(s) == post2(s))
    ensures WpCfgConjunction(a, g, ns, post1, cover)(s) == WpCfgConjunction(a, g, ns, post2, cover)(s)
    decreases cover, 1, ns
  {
    if |ns| > 0 {
      WpCfgPointwise(a, g, ns[0], post1, post2, cover, s);
      WpCfgConjunctionPointwise(a, g, ns[1..], post1, post2, cover, s);
    }
  }

  lemma WpCfgPointwise<A(!new)>(a: absval_interp<A>, g: Cfg, n: BlockId, post1: Predicate<A>, post2: Predicate<A>, cover: set<BlockId>, s: state<A>)
    requires g.successors.Keys <= g.blocks.Keys //not being in the domain of the successor relation is the same as not having any successors
    requires IsAcyclic(g.successors, n, cover)
    requires (forall s :: post1(s) == post2(s))
    ensures WpCfg(a, g, n, post1, cover)(s) == WpCfg(a, g, n, post2, cover)(s)
    decreases cover, 0
  {
    if n in g.blocks.Keys {
      var block := g.blocks[n];
      var successors := if n in g.successors.Keys then g.successors[n] else [];
      if |successors| == 0  {
        WpShallowSimpleCmdPointwise(a, block, post1, post2, s);
      } else {
        var successorPost1 := WpCfgConjunction(a, g, successors, post1, cover - {n});
        var successorPost2 := WpCfgConjunction(a, g, successors, post2, cover - {n});
        
        forall s' | true
          ensures successorPost1(s') == successorPost2(s')
        {
          WpCfgConjunctionPointwise(a, g, successors, post1, post2, cover - {n}, s');
        }
        WpShallowSimpleCmdPointwise(a, block, successorPost1, successorPost2, s);
      }
    }
  }

  lemma WpCfgConjunctionSingle<A(!new)>(
    a: absval_interp<A>, 
    g: Cfg, 
    ns: seq<BlockId>, 
    n: BlockId,
    post: Predicate<A>, 
    cover: set<BlockId>,
    s: state<A>) 
  requires g.blocks.Keys == g.successors.Keys
  requires IsAcyclic(g.successors, n, cover)
  requires IsAcyclicSeq(g.successors, ns, cover)
  requires n in ns
  ensures  var nPre := WpCfg(a, g, n, post, cover)(s);
           var nsPre := WpCfgConjunction(a, g, ns, post, cover)(s);
           ImpliesOpt(nsPre, nPre)
  /** TODO proof */
 
  /*============================Operational semantics========================*/

  least predicate CfgRed<A(!new)>(a: absval_interp<A>, g: Cfg, n: BlockId, s: ExtState<A>, s': ExtState<A>)
    requires g.blocks.Keys == g.successors.Keys
  {
    if n in g.blocks.Keys then
      var blocks := g.blocks[n];
      var successors := g.successors[n];

      if |successors| == 0 then
        SimpleCmdOpSem(a, blocks, s, s')
      else
        assert successors[0] in successors; //required for non-emptiness constraint in next line to go through
        var succ :| succ in successors;
        (exists s'' :: SimpleCmdOpSem(a, blocks, s, s'') && CfgRed(a, g, succ, s'' , s'))
    else 
      false
  }

/*==========Correspondence Wp and Operational Semantics===========================*/

  lemma WpSemToOpSem_SimpleCmd<A(!new)>(a: absval_interp<A>, scs: SimpleCmd, post: Predicate<A>, s: state<A>, s': ExtState<A>)
    requires WpShallowSimpleCmd(a, scs, post)(s) == Some(true)
    requires SimpleCmdOpSem(a, scs, NormalState(s), s')
    ensures s' != FailureState
    ensures forall ns' :: s' == NormalState(ns') ==> post(ns') == Some(true)
  /** TODO proof */
 
  //Note that the following lemma is trivially satisfied if CfgRed is the empty relation
  lemma WpSemToOpSem<A(!new)>(a: absval_interp<A>, g: Cfg, n: BlockId, post: Predicate<A>, cover: set<BlockId>, s: state<A>, s': ExtState<A>)
    requires IsAcyclic(g.successors, n, cover)
    requires g.successors.Keys == g.blocks.Keys
    requires WpCfg(a, g, n, post, cover)(s) == Some(true)
    requires CfgRed(a, g, n, NormalState(s), s')
    requires CfgWf(g) && n in g.blocks.Keys
    ensures s' != FailureState
    ensures forall ns' :: s' == NormalState(ns') ==> post(ns') == Some(true)
    decreases cover
  {
    var block := g.blocks[n];
    var successors := g.successors[n];

    if |successors| == 0 {
      WpSemToOpSem_SimpleCmd(a, block, post, s, s');
    } else {
      assert WpShallowSimpleCmd(a, block, WpCfgConjunction(a, g, successors, post, cover - {n}))(s) == Some(true);

      var succ, y :| succ in successors && SimpleCmdOpSem(a, block, NormalState(s), y) && CfgRed(a, g, succ, y , s');

      WpSemToOpSem_SimpleCmd(a, block, WpCfgConjunction(a, g, successors, post, cover - {n}), s, y);

      match y {
        case MagicState => assume false; //TODO magic state stays magic
        case NormalState(s'') => 
        calc {
          IsAcyclic(g.successors, n, cover);
          ==>
          IsAcyclicSeq(g.successors, successors, cover - {n});
          ==> { IsAcyclicElem(g.successors, successors, succ, cover - {n}); }
          IsAcyclic(g.successors, succ, cover - {n});
        }
        assert WpCfg(a, g, succ, post, cover - {n})(s'') == Some(true) by {
          WpCfgConjunctionSingle(a, g, successors, succ, post, cover - {n}, s'');
        }
        
        WpSemToOpSem(a, g, succ, post, cover - {n}, s'', s');
      }
    }
  }

  /** TODO OpSem to WP */
  function CfgRedSet<A(!new)>(a: absval_interp<A>, g: Cfg, n: BlockId, y: ExtState<A>) : iset<ExtState<A>>
    requires g.blocks.Keys == g.successors.Keys
  {
    iset y' | CfgRed(a, g, n, y, y')
  }

  lemma OpSemToWpSem<A(!new)>(a: absval_interp<A>, g: Cfg, n: BlockId, post: Predicate<A>, cover: set<BlockId>, s: state<A>)
    requires IsAcyclic(g.successors, n, cover)
    requires g.successors.Keys == g.blocks.Keys
    requires !(FailureState in CfgRedSet(a, g, n, NormalState(s)))
    requires CfgWf(g) && n in g.blocks.Keys
    ensures var wpRes := WpCfg(a, g, n, s' => Some(NormalState(s') in CfgRedSet(a, g, n, NormalState(s))), cover)(s);
            wpRes == Some(true) || wpRes == None
    decreases cover
  /** TODO: proof */

  /*======================Acyclicity lemmas ===================================*/

  lemma IsAcyclicElem(r: SuccessorRel, ns: seq<BlockId>, nSucc: BlockId, cover: set<BlockId>)
    requires IsAcyclicSeq(r, ns, cover)
    requires nSucc in ns
    ensures IsAcyclic(r, nSucc, cover)
  { }

  lemma IsAcyclicSeqLargerCover(r: SuccessorRel, ns: seq<BlockId>, cover1: set<BlockId>, cover2: set<BlockId>)
    requires cover1 <= cover2 && IsAcyclicSeq(r, ns, cover1)
    ensures IsAcyclicSeq(r, ns, cover2)
    decreases cover1, 1, ns
  {
    if |ns| != 0 {
      IsAcyclicLargerCover(r, ns[0], cover1, cover2); 
      IsAcyclicSeqLargerCover(r, ns[1..], cover1, cover2);
    }
  }

  lemma IsAcyclicLargerCover(r: SuccessorRel, n: BlockId, cover1: set<BlockId>, cover2: set<BlockId>)
    requires cover1 <= cover2 && IsAcyclic(r, n, cover1)
    ensures IsAcyclic(r, n, cover2)
    decreases cover1, 0
  {
    if n in r.Keys {
      IsAcyclicSeqLargerCover(r, r[n], cover1 - {n}, cover2 - {n});
    }
  }

  lemma IsAcyclicSeqMerge(
    r1: SuccessorRel, 
    r2: SuccessorRel, 
    ns1: seq<BlockId>,
    n2Entry: BlockId,
    cover1: set<BlockId>, 
    cover2: set<BlockId>)
    requires cover1 !! cover2
    requires r1.Keys !! r2.Keys
    requires IsAcyclicSeq(r1, ns1, cover1)
    requires IsAcyclic(r2, n2Entry, cover2)

    requires 
      (forall i :: 0 <= i < |ns1| ==> 
             ns1[i] in r1.Keys || ns1[i] == n2Entry)

    requires !(n2Entry in r1.Keys)

    requires 
      (forall i :: 0 <= i < |ns1| ==> 
             ns1[i] in r1.Keys || ns1[i] == n2Entry)
    // successors in r1 are either n2Entry or blocks recorded in r1
    requires 
      forall n1 :: n1 in r1.Keys ==>   
        (forall i :: 0 <= i < |r1[n1]| ==> (r1[n1][i] == n2Entry || r1[n1][i] in r1.Keys))

    // successors in r2 are not recorded in r1
    requires
      forall n2 :: n2 in r2.Keys ==>   
        (forall i :: 0 <= i < |r2[n2]| ==> !(r2[n2][i] in r1.Keys))
    ensures IsAcyclicSeq(r1 + r2, ns1, cover1 + cover2)
    decreases cover1, 1, ns1
  {
    if |ns1| != 0 {
      IsAcyclicMerge(r1, r2, ns1[0], n2Entry, cover1, cover2);
      IsAcyclicSeqMerge(r1, r2, ns1[1..], n2Entry, cover1, cover2);
    }
  }

  lemma IsAcyclicMerge(
    r1: SuccessorRel, 
    r2: SuccessorRel, 
    n1Entry: BlockId,
    n2Entry: BlockId,
    cover1: set<BlockId>, 
    cover2: set<BlockId>)
    requires cover1 !! cover2
    requires r1.Keys !! r2.Keys
    requires IsAcyclic(r1, n1Entry, cover1)
    requires IsAcyclic(r2, n2Entry, cover2)

    requires n1Entry in r1.Keys || n1Entry == n2Entry
    requires !(n2Entry in r1.Keys)

    // successors in r1 are either n2Entry or blocks recorded in r1
    requires 
      forall n1 :: n1 in r1.Keys ==>   
        (forall i :: 0 <= i < |r1[n1]| ==> (r1[n1][i] == n2Entry || r1[n1][i] in r1.Keys))

    // successors in r2 are not recorded in r1
    requires
      forall n2 :: n2 in r2.Keys ==>   
        (forall i :: 0 <= i < |r2[n2]| ==> !(r2[n2][i] in r1.Keys))
    ensures IsAcyclic(r1 + r2, n1Entry, cover1 + cover2)
    decreases cover1, 0
  {
    if n1Entry in r1.Keys {
      IsAcyclicSeqMerge(r1, r2, r1[n1Entry], n2Entry, cover1 - {n1Entry}, cover2);
      calc {
        IsAcyclicSeq(r1 + r2, r1[n1Entry], (cover1 - {n1Entry}) + cover2); 
      == { assert (cover1 - {n1Entry}) + cover2 == (cover1 + cover2) - {n1Entry}; }
        IsAcyclicSeq(r1 + r2, r1[n1Entry], (cover1 + cover2) - {n1Entry});
      }
    } else {
      IsAcyclicExtend(r1, r2, n2Entry, cover2);
      IsAcyclicLargerCover(r1+r2, n2Entry, cover2, cover1 + cover2);
    }
  }

  lemma WpCfgConjunctionMerge<A(!new)>(
    a: absval_interp<A>, 
    g1: Cfg,
    g2: Cfg,
    exit1: BlockId, 
    post: Predicate<A>, 
    cover1: set<BlockId>, 
    cover2: set<BlockId>, 
    s: state<A>)

  lemma WpCfgMerge<A(!new)>(
    a: absval_interp<A>, 
    g1: Cfg,
    g2: Cfg,
    g1Entry: BlockId,
    exit1: BlockId, 
    post: Predicate<A>, 
    cover1: set<BlockId>, 
    cover2: set<BlockId>, 
    s: state<A>)
    requires g1.successors.Keys <= g1.blocks.Keys
    requires g2.successors.Keys <= g2.blocks.Keys
    requires exit1 in g1.blocks.Keys
    requires exit1 !in g1.successors.Keys
    requires g1.blocks.Keys !! g2.blocks.Keys
    requires IsAcyclic(g1.successors, g1Entry, cover1)
    requires IsAcyclic(g2.successors, g2.entry, cover2)
    requires IsAcyclic(g1.successors[exit1 := [g2.entry]] + g2.successors, g1Entry, cover1+cover2+{exit1})

    requires !(g2.entry in g1.successors.Keys)

    // successors in g1.successors are either g2.entry or blocks recorded in g1.successors
    requires 
      forall n1 :: n1 in g1.successors.Keys ==>   
        (forall i :: 0 <= i < |g1.successors[n1]| ==> (g1.successors[n1][i] in g1.successors.Keys || 
                                                         g1.successors[n1][i] == exit1))

    requires g1Entry in g1.blocks.Keys

    // successors in g2.successors are not recorded in g1.successors
    requires
      forall n2 :: n2 in g2.successors.Keys ==>   
        (forall i :: 0 <= i < |g2.successors[n2]| ==> !(g2.successors[n2][i] in g1.successors.Keys))
    ensures 
      var successors' := (g1.successors[exit1 := [g2.entry]] + g2.successors);
      var mergedCfg := Cfg(g1Entry, g1.blocks + g2.blocks, successors');
      WpCfg(a, g1, g1Entry, WpCfg(a, g2, g2.entry, post, cover2), cover1)(s) ==
      WpCfg(a, mergedCfg, g1Entry, post, cover1+cover2+{exit1})(s)
    /*{
      assert g1Entry in g1.blocks.Keys;
      assert g1.successors.Keys <= g1.blocks.Keys;

      var block := g1.blocks[g1Entry];
      var successors := if g1Entry in g1.successors.Keys then g1.successors[g1Entry] else [];

      var successors' := (g1.successors + g2.successors)[exit1 := [g2.entry]];
      var mergedCfg := Cfg(g1Entry, g1.blocks + g2.blocks, successors');
      assume IsAcyclic(mergedCfg.successors, g1Entry, cover1+cover2);

      if |successors| == 0 {
        assert g1Entry == exit1;
        calc {
          WpCfg(a, g1, g1Entry, WpCfg(a, g2, g2.entry, post, cover2), cover1)(s);
          WpShallowSimpleCmd(a, block, WpCfg(a, g2, g2.entry, post, cover2))(s);
          WpCfg(a, mergedCfg, g1Entry, WpCfg(a, mergedCfg, g2.entry, post, cover2), cover1)(s);
          WpCfg(a, mergedCfg, g1Entry, post, cover1)(s);
        }
      } else {
        assume false;  
      }
    }*/


  lemma WpCfgExtend<A(!new)>(
    a: absval_interp<A>, 
    g1: Cfg,
    g2: Cfg,
    exit1: BlockId, 
    post: Predicate<A>, 
    cover1: set<BlockId>, 
    cover2: set<BlockId>) 
    requires g1.successors.Keys <= g1.blocks.Keys
    requires g2.successors.Keys <= g2.blocks.Keys
    requires IsAcyclic(g2.successors, g2.entry, cover2)
    requires exit1 in g1.blocks.Keys
    ensures 
      var successors' := (g1.successors + g2.successors)[exit1 := [g2.entry]];
      var mergedCfg := Cfg(g1.entry, g1.blocks + g2.blocks, successors');
      assume IsAcyclic(mergedCfg.successors, g2.entry, cover1+cover2);

      WpCfg(a, g2, g2.entry, post, cover2) ==
      WpCfg(a, mergedCfg, g2.entry, post, cover1+cover2)

  lemma IsAcyclicExtendSeq(r1: SuccessorRel, r2: SuccessorRel, ns: seq<BlockId>, cover: set<BlockId>)
    requires IsAcyclicSeq(r2, ns, cover)
    requires (forall i :: 0 <= i < |ns| ==> !(ns[i] in r1.Keys))
    requires 
      forall n2 :: n2 in r2.Keys ==>   
        (forall i :: 0 <= i < |r2[n2]| ==> !(r2[n2][i] in r1.Keys))
    ensures IsAcyclicSeq(r1+r2, ns, cover)
    decreases cover, 1, ns
  {
    if |ns| != 0 {
      IsAcyclicExtend(r1, r2, ns[0], cover);
      IsAcyclicExtendSeq(r1, r2, ns[1..], cover);
    }
  }
 
  lemma IsAcyclicExtend(r1: SuccessorRel, r2: SuccessorRel, n2Entry: BlockId, cover: set<BlockId>)
    requires IsAcyclic(r2, n2Entry, cover)
    requires !(n2Entry in r1.Keys)
    requires 
      forall n2 :: n2 in r2.Keys ==>   
        (forall i :: 0 <= i < |r2[n2]| ==> !(r2[n2][i] in r1.Keys))
    ensures IsAcyclic(r1+r2, n2Entry, cover)
    decreases cover, 0
  {
    var r := r1 + r2;
    if(n2Entry in r.Keys) {
      assert n2Entry in r2.Keys;
      assert IsAcyclicSeq(r2, r2[n2Entry], cover - {n2Entry});

      IsAcyclicExtendSeq(r1, r2, r2[n2Entry], cover - {n2Entry});
    }
  }

  lemma IsAcyclicExtend2(r1: SuccessorRel, r2: SuccessorRel, n1Entry: BlockId, cover: set<BlockId>)
    requires IsAcyclic(r1, n1Entry, cover)
    requires !(n1Entry in r2.Keys)
    requires 
      forall n1 :: n1 in r1.Keys ==>   
        (forall i :: 0 <= i < |r1[n1]| ==> !(r1[n1][i] in r2.Keys))
    requires r1.Keys !! r2.Keys
    ensures IsAcyclic(r1+r2, n1Entry, cover)
  {
    IsAcyclicExtend(r2, r1, n1Entry, cover);
    assert r2 + r1 == r1 + r2;
  }

  lemma IsAcyclicUpdate(r: SuccessorRel, entry: BlockId, n: BlockId, m: seq<BlockId>, cover: set<BlockId>)
    requires IsAcyclic(r, entry, cover)
    requires !(n in r.Keys)
    requires entry != n;
    requires 
      forall n1 :: n1 in r.Keys ==>   
        (forall i :: 0 <= i < |r[n1]| ==> r[n1][i] != n)
    ensures IsAcyclic(r[n := m], entry, cover)
  {
    IsAcyclicExtend2(r, map[n := m], entry, cover);
    assert r+map[n := m] == r[n := m];
  }

  lemma IsAcyclicSeqOneStep(r: SuccessorRel, ns: seq<BlockId>, cover: set<BlockId>)
    requires (forall i :: 0 <= i < |ns| ==> ! (ns[i] in r.Keys))
    ensures IsAcyclicSeq(r, ns, cover)
  {
  }

  lemma IsAcyclicSeqUpdate2(r: SuccessorRel, ns: seq<BlockId>, n: BlockId, m: seq<BlockId>, cover: set<BlockId>)
    requires IsAcyclicSeq(r, ns, cover)
    requires !(n in r.Keys)
    requires (forall i :: 0 <= i < |m| ==> ! (m[i] in r.Keys) && !(m[i] == n))
    ensures IsAcyclicSeq(r[n := m], ns, cover + {n})
    decreases cover, 1, ns
  {
    if |ns| != 0 {
      IsAcyclicUpdate2(r, ns[0], n, m, cover);
      IsAcyclicSeqUpdate2(r, ns[1..], n, m, cover);
    }
  }

  lemma IsAcyclicUpdate2(r: SuccessorRel, entry: BlockId, n: BlockId, m: seq<BlockId>, cover: set<BlockId>)
    requires IsAcyclic(r, entry, cover)
    requires !(n in r.Keys)
    requires (forall i :: 0 <= i < |m| ==> ! (m[i] in r.Keys) && !(m[i] ==n))
    ensures IsAcyclic(r[n := m], entry, cover + {n})
    decreases cover, 0
  {
    if(entry == n) {
      assert IsAcyclic(r[n := m], entry, cover + {n}) by {
          IsAcyclicSeqOneStep(r[n := m], m, (cover + {n}) - {n});
      }
    }

    if entry in r.Keys {
        IsAcyclicSeqUpdate2(r, r[entry], n, m, cover - {entry}); 
        assert (cover - {entry}) + {n} == (cover + {n}) - {entry};
    }
  }
}