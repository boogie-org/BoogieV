
include "BoogieSemantics.dfy"

module BoogieCfg {

  import opened BoogieLang
  import opened BoogieSemantics
  import opened Wrappers

  type BasicBlock = seq<SimpleCmd>
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

  /*=================== Wp semantics ==========================================*/
  datatype WpPostCfg<!A> = WpPostCfg(normal: Predicate<A>, exceptional: map<BlockId, Predicate<A>>)

  function WpCfgConjunction<A(!new)>(
    a: absval_interp<A>, 
    g: Cfg, 
    ns: seq<BlockId>, 
    post: Predicate<A>, 
    cover: set<BlockId>) : Predicate<A>
    requires g.blocks.Keys == g.successors.Keys
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
    requires g.blocks.Keys == g.successors.Keys
    requires IsAcyclic(g.successors, n, cover)
    decreases cover, 0
  {
    if !(n in g.blocks.Keys) then
      post
    else 
      var successors := g.successors[n];
      if |successors| == 0 then 
        WpShallowSimpleCmdSeq(a, g.blocks[n], post)
      else 
        WpShallowSimpleCmdSeq(a, g.blocks[n], WpCfgConjunction(a, g, successors, post, cover - {n}))
  }

  lemma IsAcyclicElem(r: SuccessorRel, ns: seq<BlockId>, nSucc: BlockId, cover: set<BlockId>)
    requires IsAcyclicSeq(r, ns, cover)
    requires nSucc in ns
    ensures IsAcyclic(r, nSucc, cover)
  /** TODO proof */

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
        SimpleCmdSeqOpSem(a, blocks, s, s')
      else
        //DISCUSS
        assert successors[0] in successors; //required for non-emptiness constraint in next line to go through
        var succ :| succ in successors;
        (exists s'' :: SimpleCmdSeqOpSem(a, blocks, s, s'') && CfgRed(a, g, succ, s'' , s'))
    else 
      false
  }

/*==========Correspondence Wp and Operational Semantics===========================*/

  lemma WpSemToOpSem_SimpleCmdSeq<A(!new)>(a: absval_interp<A>, scs: seq<SimpleCmd>, post: Predicate<A>, s: state<A>, s': ExtState<A>)
    requires WpShallowSimpleCmdSeq(a, scs, post)(s) == Some(true)
    requires SimpleCmdSeqOpSem(a, scs, NormalState(s), s')
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
      WpSemToOpSem_SimpleCmdSeq(a, block, post, s, s');
    } else {
      assert WpShallowSimpleCmdSeq(a, block, WpCfgConjunction(a, g, successors, post, cover - {n}))(s) == Some(true);

      var succ, y :| succ in successors && SimpleCmdSeqOpSem(a, block, NormalState(s), y) && CfgRed(a, g, succ, y , s');

      WpSemToOpSem_SimpleCmdSeq(a, block, WpCfgConjunction(a, g, successors, post, cover - {n}), s, y);

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

  /** Lemmas */
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