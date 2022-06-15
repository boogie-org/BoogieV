
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
    requires |ns| >= 1
    decreases cover, 1, ns
  {   //this definition allows one to deduce that WpCfgConjunction and WpCfg coincide for singleton sequences (instead of just being pointwise equal)
      if |ns| == 1 then WpCfg(a, g, ns[0], post, cover) 
      else 
        s => 
          var res1 :- WpCfg(a, g, ns[0], post, cover)(s);
          var res2 :- WpCfgConjunction(a, g, ns[1..], post, cover)(s);
          Some(res1 && res2)
  }

  function WpCfg<A(!new)>(a: absval_interp<A>, g: Cfg, n: BlockId, post: Predicate<A>, cover: set<BlockId>) : Predicate<A>
    requires g.successors.Keys <= g.blocks.Keys //not being in the domain of the successor relation is the same as not having any successors
    decreases cover, 0
  {
    if IsAcyclic(g.successors, n, cover) then
      if n !in g.blocks.Keys then
        post
      else 
        var successors := if n in g.successors.Keys then g.successors[n] else [];
        if |successors| == 0 then 
          WpShallowSimpleCmd(a, g.blocks[n], post)
        else 
          WpShallowSimpleCmd(a, g.blocks[n], WpCfgConjunction(a, g, successors, post, cover - {n}))
    else 
      s => None
  }

  lemma WpCfgConjunctionPointwise<A(!new)>(a: absval_interp<A>, g: Cfg, ns: seq<BlockId>, post1: Predicate<A>, post2: Predicate<A>, cover: set<BlockId>, s: state<A>) 
    requires g.successors.Keys <= g.blocks.Keys //not being in the domain of the successor relation is the same as not having any successors
    //requires IsAcyclicSeq(g.successors, ns, cover)
    requires (forall s :: post1(s) == post2(s))
    requires |ns| >= 1
    ensures WpCfgConjunction(a, g, ns, post1, cover)(s) == WpCfgConjunction(a, g, ns, post2, cover)(s)
    decreases cover, 1, ns
  {
    WpCfgPointwise(a, g, ns[0], post1, post2, cover, s);
    if |ns| > 1 {
      WpCfgConjunctionPointwise(a, g, ns[1..], post1, post2, cover, s);
    }
  }

  lemma WpCfgPointwise<A(!new)>(a: absval_interp<A>, g: Cfg, n: BlockId, post1: Predicate<A>, post2: Predicate<A>, cover: set<BlockId>, s: state<A>)
    requires g.successors.Keys <= g.blocks.Keys //not being in the domain of the successor relation is the same as not having any successors
    //requires IsAcyclic(g.successors, n, cover)
    requires (forall s :: post1(s) == post2(s))
    ensures WpCfg(a, g, n, post1, cover)(s) == WpCfg(a, g, n, post2, cover)(s)
    decreases cover, 0
  {
    if IsAcyclic(g.successors, n, cover) {
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
    cover2: set<BlockId>)

  lemma WpCfgMerge<A(!new)>(
    a: absval_interp<A>, 
    g1: Cfg,
    g2: Cfg,
    g1Entry: BlockId,
    exit1: BlockId, 
    post: Predicate<A>, 
    cover1: set<BlockId>, 
    cover2: set<BlockId>)
    requires g1.successors.Keys <= g1.blocks.Keys
    requires g2.successors.Keys <= g2.blocks.Keys
    requires exit1 in g1.blocks.Keys && exit1 !in g1.successors.Keys
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

    requires g1Entry in g1.successors.Keys || g1Entry == exit1
    requires g2.entry != exit1

    requires forall n1 :: n1 in g1.successors.Keys ==> g1.successors[n1] != []

    // successors in g2.successors are not recorded in g1.successors
    requires
      forall n2 :: n2 in g2.successors.Keys ==>   
        (forall i :: 0 <= i < |g2.successors[n2]| ==> !(g2.successors[n2][i] in g1.successors.Keys + {exit1}))
    ensures 
      var successors' := (g1.successors[exit1 := [g2.entry]] + g2.successors);
      var mergedCfg := Cfg(g1Entry, g1.blocks + g2.blocks, successors');
      WpCfg(a, g1, g1Entry, WpCfg(a, g2, g2.entry, post, cover2), cover1) ==
      WpCfg(a, mergedCfg, g1Entry, post, cover1+cover2+{exit1})
    {
      var cover3 := cover1+cover2+{exit1};
      var block := g1.blocks[g1Entry];
      var successors := if g1Entry in g1.successors.Keys then g1.successors[g1Entry] else [];

      var successors' := (g1.successors[exit1 := [g2.entry]] + g2.successors);
      var mergedCfg := Cfg(g1Entry, g1.blocks + g2.blocks, successors');

      calc {
        WpCfg(a, g2, g2.entry, post, cover2);
          { WpCfgLargerCover(a, g2, g2.entry, post, cover2, cover3); }
        WpCfg(a, g2, g2.entry, post, cover3);
          { IsAcyclicLargerCover(g2.successors, g2.entry, cover2, cover3);
            WpCfgExtend(a, mergedCfg, g2, g1.successors[exit1 := [g2.entry]], g2.entry, post, cover3); }
        WpCfg(a, mergedCfg, g2.entry, post, cover3);
      }

      if |successors| == 0 {
        assert g1Entry == exit1;

        calc {
          WpCfg(a, mergedCfg, g1Entry, post, cover3);
          WpShallowSimpleCmd(a, block, WpCfgConjunction(a, mergedCfg, [g2.entry], post, cover3 - {g1Entry}));
          WpShallowSimpleCmd(a, block, WpCfg(a, mergedCfg, g2.entry, post, cover3 - {g1Entry})); 
            { WpCfgLargerCover(a, mergedCfg, g2.entry, post, cover3 - {g1Entry}, cover3); }
          WpShallowSimpleCmd(a, block, WpCfg(a, mergedCfg, g2.entry, post, cover3));
            { assert WpCfg(a, mergedCfg, g2.entry, post, cover3) == WpCfg(a, g2, g2.entry, post, cover2); }
          WpShallowSimpleCmd(a, block, WpCfg(a, g2, g2.entry, post, cover2));
          WpCfg(a, g1, g1Entry, WpCfg(a, g2, g2.entry, post, cover2), cover1);
        }
      } else {
        assert g1.blocks[g1Entry] == mergedCfg.blocks[g1Entry];
        calc {
          WpCfg(a, mergedCfg, g1Entry, post, cover3);
          WpShallowSimpleCmd(a, block, WpCfgConjunction(a, mergedCfg, successors, post, cover3-{g1Entry}));
            { assume false; }
          WpShallowSimpleCmd(a, block, WpCfgConjunction(a, g1, successors, WpCfg(a, g2, g2.entry, post, cover2), cover1-{g1Entry}));
          WpCfg(a, g1, g1Entry, WpCfg(a, g2, g2.entry, post, cover2), cover1);
        }
      }
    }

  
  lemma WpCfgConjunctionLargerCover<A(!new)>(
    a: absval_interp<A>, 
    g: Cfg,
    ns: seq<BlockId>,
    post: Predicate<A>, 
    cover1: set<BlockId>, 
    cover2: set<BlockId>)
  requires g.successors.Keys <= g.blocks.Keys
  requires |ns| >= 1
  requires cover1 <= cover2
  requires IsAcyclicSeq(g.successors, ns, cover1)
  ensures WpCfgConjunction(a, g, ns, post, cover1) == WpCfgConjunction(a, g, ns, post, cover2)
  decreases cover1, 1, ns
  {
    WpCfgLargerCover(a, g, ns[0], post, cover1, cover2);
  }

  lemma WpCfgLargerCover<A(!new)>(
    a: absval_interp<A>, 
    g: Cfg,
    n: BlockId,
    post: Predicate<A>, 
    cover1: set<BlockId>, 
    cover2: set<BlockId>) 
  requires g.successors.Keys <= g.blocks.Keys
  requires cover1 <= cover2
  requires IsAcyclic(g.successors, n, cover1)
  ensures WpCfg(a, g, n, post, cover1) == WpCfg(a, g, n, post, cover2)
  decreases cover1, 0
  {
    IsAcyclicLargerCover(g.successors, n, cover1, cover2);
    
    var successors := if n in g.successors.Keys then g.successors[n] else [];

    if |successors| > 0 {
      WpCfgConjunctionLargerCover(a, g, successors, post, cover1-{n}, cover2-{n});
    }
  }

  lemma WpCfgConjunctionExtend<A(!new)>(a: absval_interp<A>, cfgMerged: Cfg, cfg2: Cfg, r1: SuccessorRel, ns: seq<BlockId>, post: Predicate<A>, cover: set<BlockId>)
    requires 
      var r2 := cfg2.successors;
      && |ns| >= 1
      && cfgMerged.successors == r1 + r2
      && r1.Keys !! r2.Keys
      && (forall n :: n in cfg2.blocks.Keys ==> n in cfgMerged.blocks.Keys && cfgMerged.blocks[n] == cfg2.blocks[n])
      && cfgMerged.successors.Keys <= cfgMerged.blocks.Keys
      && cfg2.successors.Keys <= cfg2.blocks.Keys
      && IsAcyclicSeq(r2, ns, cover)
      && (forall n :: n in ns ==> n !in r1.Keys && (n !in r2.Keys ==> n !in cfgMerged.blocks.Keys))
      && (forall n2 :: n2 in r2.Keys ==>   
           (forall i :: 0 <= i < |r2[n2]| ==> r2[n2][i] in r2.Keys || r2[n2][i] !in cfgMerged.blocks.Keys))
    ensures WpCfgConjunction(a, cfgMerged, ns, post, cover) == WpCfgConjunction(a, cfg2, ns, post, cover)
    decreases cover, 1, ns
  {
    WpCfgExtend(a, cfgMerged, cfg2, r1, ns[0], post, cover);
  }

  lemma WpCfgExtend<A(!new)>(a: absval_interp<A>, cfgMerged: Cfg, cfg2: Cfg, r1: SuccessorRel, n2Entry: BlockId, post: Predicate<A>, cover: set<BlockId>)
    requires 
      var r2 := cfg2.successors;
      && cfgMerged.successors == r1 + r2
      && r1.Keys !! r2.Keys
      && (forall n :: n in cfg2.blocks.Keys ==> n in cfgMerged.blocks.Keys && cfgMerged.blocks[n] == cfg2.blocks[n])
      && cfgMerged.successors.Keys <= cfgMerged.blocks.Keys
      && cfg2.successors.Keys <= cfg2.blocks.Keys
      && IsAcyclic(r2, n2Entry, cover)
      && n2Entry !in r1.Keys && (n2Entry !in r2.Keys ==> n2Entry !in cfgMerged.blocks.Keys)
      && (forall n2 :: n2 in r2.Keys ==>   
           (forall i :: 0 <= i < |r2[n2]| ==> r2[n2][i] in r2.Keys || r2[n2][i] !in cfgMerged.blocks.Keys))
    ensures WpCfg(a, cfgMerged, n2Entry, post, cover) == WpCfg(a, cfg2, n2Entry, post, cover)
    decreases cover, 0
  {
    var successors := if n2Entry in cfg2.successors.Keys then cfg2.successors[n2Entry] else [];
    IsAcyclicExtend(r1, cfg2.successors, n2Entry, cover);
    assert IsAcyclic(cfgMerged.successors, n2Entry, cover);

    if n2Entry in cfg2.blocks.Keys {
      var block := cfg2.blocks[n2Entry];
      assert n2Entry in cfgMerged.blocks.Keys;
      if |successors| > 0 {
        WpCfgConjunctionExtend(a, cfgMerged, cfg2, r1, successors, post, cover - {n2Entry});
      }
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