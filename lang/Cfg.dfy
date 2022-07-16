
include "BoogieSemantics.dfy"

module BoogieCfg {

  import opened BoogieLang
  import opened BoogieSemantics
  import opened Wrappers

  type BasicBlock = SimpleCmd
  type BlockId = nat 

  datatype Cfg = Cfg(entry: BlockId, blocks: map<BlockId, BasicBlock>, successors: map<BlockId, seq<BlockId>>)

  predicate GraphWf<T>(succRel: map<T, seq<T>>)
  {
    (forall blockId :: blockId in succRel.Keys ==> 
      (forall i :: 0 <= i < |succRel[blockId]| ==> succRel[blockId][i] in succRel.Keys))
  }

  predicate CfgWf(g: Cfg)
  {
    && g.blocks.Keys == g.successors.Keys
    && g.entry in g.blocks.Keys
    && GraphWf(g.successors)
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
          WpSimpleCmd(a, g.blocks[n], post)
        else 
          WpSimpleCmd(a, g.blocks[n], WpCfgConjunction(a, g, successors, post, cover - {n}))
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
          WpSimpleCmdPointwise(a, block, post1, post2, s);
        } else {
          var successorPost1 := WpCfgConjunction(a, g, successors, post1, cover - {n});
          var successorPost2 := WpCfgConjunction(a, g, successors, post2, cover - {n});
          
          forall s' | true
            ensures successorPost1(s') == successorPost2(s')
          {
            WpCfgConjunctionPointwise(a, g, successors, post1, post2, cover - {n}, s');
          }
          WpSimpleCmdPointwise(a, block, successorPost1, successorPost2, s);
        }
      }
    }
  }

  lemma WpCfgConjunctionEntryIndep<A(!new)>(a: absval_interp<A>, cfg: Cfg, entryOther: BlockId, ns: seq<BlockId>, post: Predicate<A>, cover: set<BlockId>)
    requires |ns| > 0
    requires cfg.successors.Keys <= cfg.blocks.Keys
    ensures WpCfgConjunction(a, cfg, ns, post, cover) == WpCfgConjunction(a, Cfg(entryOther, cfg.blocks, cfg.successors), ns, post, cover)
    decreases cover, 1, |ns|
  {
    WpCfgEntryIndep(a, cfg, entryOther, ns[0], post, cover);
  }
  
  lemma WpCfgEntryIndep<A(!new)>(a: absval_interp<A>, cfg: Cfg, entryOther: BlockId, n: BlockId, post: Predicate<A>, cover: set<BlockId>)
    requires cfg.successors.Keys <= cfg.blocks.Keys
    ensures WpCfg(a, cfg, n, post, cover) == WpCfg(a, Cfg(entryOther, cfg.blocks, cfg.successors), n, post, cover)
    decreases cover, 0
  {
    var successors := if n in cfg.successors.Keys then cfg.successors[n] else [];

    if IsAcyclic(cfg.successors, n, cover) {
      if |successors| > 0 {
        WpCfgConjunctionEntryIndep(a, cfg, entryOther, successors, post, cover - {n});
      }
    }  
  }

  /*======================Acyclicity lemmas ===================================*/

  lemma IsAcyclicSeqForall(r: SuccessorRel, ns: seq<BlockId>, cover: set<BlockId>)
    requires IsAcyclicSeq(r, ns, cover)
    ensures forall n :: n in ns ==> IsAcyclic(r, n, cover)
  { }

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
    ns: seq<BlockId>,
    exit1: BlockId, 
    post: Predicate<A>, 
    cover1: set<BlockId>, 
    cover2: set<BlockId>)
    requires |ns| >= 1
    requires g1.successors.Keys <= g1.blocks.Keys
    requires g2.successors.Keys <= g2.blocks.Keys
    requires exit1 in g1.blocks.Keys && exit1 !in g1.successors.Keys
    requires g1.blocks.Keys !! g2.blocks.Keys
    requires IsAcyclicSeq(g1.successors, ns, cover1)
    requires IsAcyclic(g2.successors, g2.entry, cover2)
    requires IsAcyclicSeq(g1.successors[exit1 := [g2.entry]] + g2.successors, ns, cover1+cover2+{exit1})

    requires cover2 !! g1.blocks.Keys

    requires !(g2.entry in g1.blocks.Keys)

    // successors in g1.successors are either g2.entry or blocks recorded in g1.successors
    requires 
      forall n1 :: n1 in g1.successors.Keys ==>   
        (forall i :: 0 <= i < |g1.successors[n1]| ==> (g1.successors[n1][i] in g1.successors.Keys || 
                                                         g1.successors[n1][i] == exit1))

    requires (forall n :: n in ns ==> n in g1.successors.Keys || n == exit1)
    requires g2.entry != exit1

    requires forall n1 :: n1 in g1.successors.Keys ==> g1.successors[n1] != []

    // successors in g2.successors are not recorded in g1.blocks
    requires
      forall n2 :: n2 in g2.successors.Keys ==>   
        (forall i :: 0 <= i < |g2.successors[n2]| ==> g2.successors[n2][i] !in g1.blocks.Keys)
    ensures 
      var successors' := (g1.successors[exit1 := [g2.entry]] + g2.successors);
      var mergedCfg := Cfg(g1.entry, g1.blocks + g2.blocks, successors');
      WpCfgConjunction(a, g1, ns, WpCfg(a, g2, g2.entry, post, cover2), cover1) ==
      WpCfgConjunction(a, mergedCfg, ns, post, cover1+cover2+{exit1})
    decreases cover1, 1, ns
  {
    WpCfgMerge(a, g1, g2, ns[0], exit1, post, cover1, cover2);
  }

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

    requires cover2 !! g1.blocks.Keys

    requires !(g2.entry in g1.blocks.Keys)

    // successors in g1.successors are either g2.entry or blocks recorded in g1.successors
    requires 
      forall n1 :: n1 in g1.successors.Keys ==>   
        (forall i :: 0 <= i < |g1.successors[n1]| ==> (g1.successors[n1][i] in g1.successors.Keys || 
                                                         g1.successors[n1][i] == exit1))

    requires g1Entry in g1.successors.Keys || g1Entry == exit1
    requires g2.entry != exit1

    requires forall n1 :: n1 in g1.successors.Keys ==> g1.successors[n1] != []

    // successors in g2.successors are not recorded in g1.blocks
    requires
      forall n2 :: n2 in g2.successors.Keys ==>   
        (forall i :: 0 <= i < |g2.successors[n2]| ==> g2.successors[n2][i] !in g1.blocks.Keys)
    ensures 
      var successors' := (g1.successors[exit1 := [g2.entry]] + g2.successors);
      var mergedCfg := Cfg(g1.entry, g1.blocks + g2.blocks, successors');
      WpCfg(a, g1, g1Entry, WpCfg(a, g2, g2.entry, post, cover2), cover1) ==
      WpCfg(a, mergedCfg, g1Entry, post, cover1+cover2+{exit1})
    decreases cover1, 0
    {
      var cover3 := cover1+cover2+{exit1};
      var block := g1.blocks[g1Entry];
      var successors := if g1Entry in g1.successors.Keys then g1.successors[g1Entry] else [];

      var successors' := (g1.successors[exit1 := [g2.entry]] + g2.successors);
      var mergedCfg := Cfg(g1.entry, g1.blocks + g2.blocks, successors');

      calc {
        WpCfg(a, g2, g2.entry, post, cover2);
          { WpCfgLargerCover(a, g2, g2.entry, post, cover2, cover3); }
        WpCfg(a, g2, g2.entry, post, cover3);
          { IsAcyclicLargerCover(g2.successors, g2.entry, cover2, cover3);

            WpCfgExtend(a, mergedCfg, g2, g1.blocks, g1.successors[exit1 := [g2.entry]], g2.entry, post, cover3); }
        WpCfg(a, mergedCfg, g2.entry, post, cover3);
      }

      if |successors| == 0 {
        assert g1Entry == exit1;

        calc {
          WpCfg(a, mergedCfg, g1Entry, post, cover3);
          WpSimpleCmd(a, block, WpCfgConjunction(a, mergedCfg, [g2.entry], post, cover3 - {g1Entry}));
          WpSimpleCmd(a, block, WpCfg(a, mergedCfg, g2.entry, post, cover3 - {g1Entry})); 
            { WpCfgLargerCover(a, mergedCfg, g2.entry, post, cover3 - {g1Entry}, cover3); }
          WpSimpleCmd(a, block, WpCfg(a, mergedCfg, g2.entry, post, cover3));
            { assert WpCfg(a, mergedCfg, g2.entry, post, cover3) == WpCfg(a, g2, g2.entry, post, cover2); }
          WpSimpleCmd(a, block, WpCfg(a, g2, g2.entry, post, cover2));
          WpCfg(a, g1, g1Entry, WpCfg(a, g2, g2.entry, post, cover2), cover1);
        }
      } else {
        assert g1.blocks[g1Entry] == mergedCfg.blocks[g1Entry];
        assert g1Entry != exit1;
        calc {
          WpCfg(a, mergedCfg, g1Entry, post, cover3);
          WpSimpleCmd(a, block, WpCfgConjunction(a, mergedCfg, successors, post, cover3-{g1Entry}));
            { 
              assert cover3-{g1Entry} == (cover1-{g1Entry})+cover2+{exit1};

              WpCfgConjunctionMerge(a, g1, g2, successors, exit1, post, cover1-{g1Entry}, cover2);
            }
          WpSimpleCmd(a, block, WpCfgConjunction(a, g1, successors, WpCfg(a, g2, g2.entry, post, cover2), cover1-{g1Entry}));
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

  lemma WpCfgConjunctionExtend<A(!new)>(a: absval_interp<A>, cfgMerged: Cfg, cfg2: Cfg, b1: map<BlockId, BasicBlock>, r1: SuccessorRel, ns: seq<BlockId>, post: Predicate<A>, cover: set<BlockId>)
    requires 
      var r2 := cfg2.successors;
      && |ns| >= 1
      && cfgMerged.successors == r1 + r2
      && cfgMerged.blocks == b1 + cfg2.blocks
      && r1.Keys !! r2.Keys
      && b1.Keys !! cfg2.blocks.Keys
      && cfgMerged.successors.Keys <= cfgMerged.blocks.Keys
      && cfg2.successors.Keys <= cfg2.blocks.Keys
      && IsAcyclicSeq(r2, ns, cover)
      && r1.Keys <= b1.Keys
      && (forall n :: n in ns ==> n !in b1.Keys)
      && (forall n2 :: n2 in r2.Keys ==>   
           (forall i :: 0 <= i < |r2[n2]| ==> r2[n2][i] !in b1))
    ensures WpCfgConjunction(a, cfgMerged, ns, post, cover) == WpCfgConjunction(a, cfg2, ns, post, cover)
    decreases cover, 1, ns
  {
    WpCfgExtend(a, cfgMerged, cfg2, b1, r1, ns[0], post, cover);
  }

  lemma WpCfgExtend2<A(!new)>(a: absval_interp<A>, cfgMerged: Cfg, cfg1: Cfg, b2: map<BlockId, BasicBlock>, r2: SuccessorRel, n1Entry: BlockId, post: Predicate<A>, cover: set<BlockId>)
    requires 
      var r1 := cfg1.successors;
      && cfgMerged.successors == r1 + r2
      && cfgMerged.blocks == cfg1.blocks + b2
      && r1.Keys !! r2.Keys
      && cfg1.blocks.Keys !! b2.Keys
      && cfgMerged.successors.Keys <= cfgMerged.blocks.Keys
      && cfg1.successors.Keys <= cfg1.blocks.Keys
      && IsAcyclic(r1, n1Entry, cover)
      && r2.Keys <= b2.Keys
      && n1Entry !in b2.Keys   
      && (forall n2 :: n2 in r1.Keys ==>   
           (forall i :: 0 <= i < |r1[n2]| ==> r1[n2][i] !in b2.Keys))
    ensures WpCfg(a, cfgMerged, n1Entry, post, cover) == WpCfg(a, cfg1, n1Entry, post, cover)
  {
    assert cfg1.successors + r2 == r2 + cfg1.successors;
    assert cfg1.blocks + b2 == b2 + cfg1.blocks;
    WpCfgExtend(a, cfgMerged, cfg1, b2, r2, n1Entry, post, cover);
  }
  
  lemma WpCfgExtend<A(!new)>(a: absval_interp<A>, cfgMerged: Cfg, cfg2: Cfg, b1: map<BlockId, BasicBlock>, r1: SuccessorRel, n2Entry: BlockId, post: Predicate<A>, cover: set<BlockId>)
    requires 
      var r2 := cfg2.successors;
      && cfgMerged.successors == r1 + r2
      && cfgMerged.blocks == b1 + cfg2.blocks
      && r1.Keys !! r2.Keys
      && b1.Keys !! cfg2.blocks.Keys
      && cfgMerged.successors.Keys <= cfgMerged.blocks.Keys
      && cfg2.successors.Keys <= cfg2.blocks.Keys
      && IsAcyclic(r2, n2Entry, cover)
      && r1.Keys <= b1.Keys
      && n2Entry !in b1.Keys   
      && (forall n2 :: n2 in r2.Keys ==>   
           (forall i :: 0 <= i < |r2[n2]| ==> r2[n2][i] !in b1.Keys))
    ensures WpCfg(a, cfgMerged, n2Entry, post, cover) == WpCfg(a, cfg2, n2Entry, post, cover)
    decreases cover, 0
  {
    var successors := if n2Entry in cfg2.successors.Keys then cfg2.successors[n2Entry] else [];
    var successorsMerged := if n2Entry in cfgMerged.successors.Keys then cfgMerged.successors[n2Entry] else [];

    assert successors == successorsMerged;

    IsAcyclicExtend(r1, cfg2.successors, n2Entry, cover);
    assert IsAcyclic(cfgMerged.successors, n2Entry, cover);

    if n2Entry in cfg2.blocks.Keys {
      var block := cfg2.blocks[n2Entry];
      assert cfgMerged.blocks[n2Entry] == block;
      assert n2Entry in cfgMerged.blocks.Keys;
      if |successors| > 0 {
        assert |successorsMerged| > 0;
        WpCfgConjunctionExtend(a, cfgMerged, cfg2, b1, r1, successors, post, cover - {n2Entry});
        calc {
          WpCfg(a, cfg2, n2Entry, post, cover);
          WpSimpleCmd(a, block, WpCfgConjunction(a, cfg2, successors, post, cover-{n2Entry}));
          WpSimpleCmd(a, block, WpCfgConjunction(a, cfgMerged, successors, post, cover-{n2Entry}));
          WpSimpleCmd(a, block, WpCfgConjunction(a, cfgMerged, successorsMerged, post, cover-{n2Entry}));
          WpCfg(a, cfgMerged, n2Entry, post, cover);
        }
      }
    } 
  }
  /*
  lemma IsAcyclicUpdate(r: SuccessorRel, entry: BlockId, n: BlockId, m: seq<BlockId>, cover: set<BlockId>)
    requires IsAcyclic(r, entry, cover)
    requires !(n in r.Keys)
    requires entry != n;
    requires 
      forall n1 :: n1 in r.Keys ==>   
        (forall i :: 0 <= i < |r[n1]| ==> r[n1][i] != n)
    ensures IsAcyclic(r[n := m], entry, cover)
  */

  lemma WpCfgUpdate<A(!new)>(a: absval_interp<A>, cfg: Cfg, n: BlockId, source: (BlockId, SimpleCmd), target: seq<BlockId>, post: Predicate<A>, cover: set<BlockId>)
    requires IsAcyclic(cfg.successors, n, cover)
    requires cfg.successors.Keys <= cfg.blocks.Keys
    requires source.0 !in cfg.blocks.Keys
    requires n != source.0;
    requires 
      forall n1 :: n1 in cfg.successors.Keys ==>   
        (forall i :: 0 <= i < |cfg.successors[n1]| ==> cfg.successors[n1][i] != source.0)
    ensures 
      var cfg' := Cfg(cfg.entry, cfg.blocks[source.0 := source.1], cfg.successors[source.0 := target]);
      WpCfg(a, cfg, n, post, cover) == WpCfg(a, cfg', n, post, cover)
    {
      var cfg' := Cfg(cfg.entry, cfg.blocks[source.0 := source.1], cfg.successors[source.0 := target]);
      var (sourceId, sourceBlock) := source;

      WpCfgExtend2(a, cfg', cfg, map[source.0 := source.1], map[source.0 := target], n, post, cover);
    }


  /*

  lemma IsAcyclicUpdate2(r: SuccessorRel, entry: BlockId, n: BlockId, m: seq<BlockId>, cover: set<BlockId>)
    requires IsAcyclic(r, entry, cover)
    requires !(n in r.Keys)
    requires (forall i :: 0 <= i < |m| ==> ! (m[i] in r.Keys) && !(m[i] ==n))
    ensures IsAcyclic(r[n := m], entry, cover + {n})
  */

  lemma WpCfgConjunctionUpdate2<A(!new)>(a: absval_interp<A>, cfg: Cfg, ns: seq<BlockId>, source: BlockId, target: BlockId, post: Predicate<A>, cover: set<BlockId>)
    requires IsAcyclicSeq(cfg.successors, ns, cover)
    requires |ns| > 0
    requires cfg.successors.Keys <= cfg.blocks.Keys
    requires source in cfg.blocks.Keys
    requires source !in cfg.successors.Keys
    requires target !in cfg.blocks.Keys || cfg.blocks[target] == Skip
    requires target !in cfg.successors.Keys && source != target
    ensures  WpCfgConjunction(a, cfg, ns, post, cover) ==
             WpCfgConjunction(a, Cfg(cfg.entry, cfg.blocks[target := Skip], cfg.successors[source := [target]]), ns, post, cover + {source})
    decreases cover, 1, ns
    {
      WpCfgUpdate2(a, cfg, ns[0], source, target, post, cover);
    }

  lemma WpCfgUpdate2<A(!new)>(a: absval_interp<A>, cfg: Cfg, n: BlockId, source: BlockId, target: BlockId, post: Predicate<A>, cover: set<BlockId>)
    requires IsAcyclic(cfg.successors, n, cover)
    requires cfg.successors.Keys <= cfg.blocks.Keys
    requires source in cfg.blocks.Keys
    requires source !in cfg.successors.Keys
    requires target !in cfg.blocks.Keys || cfg.blocks[target] == Skip
    requires target !in cfg.successors.Keys && source != target
    ensures  WpCfg(a, cfg, n, post, cover) ==
             WpCfg(a, Cfg(cfg.entry, cfg.blocks[target := Skip], cfg.successors[source := [target]]), n, post, cover+{source})
    decreases cover, 0
  {
    var cfg' := Cfg(cfg.entry, cfg.blocks[target := Skip], cfg.successors[source := [target]]);

    assert IsAcyclic(cfg'.successors, n, cover + {source}) by {
      IsAcyclicUpdate2(cfg.successors, n, source, [target], cover);
    }


    if n in cfg.blocks.Keys {
      var block := cfg.blocks[n];
      assert block == cfg'.blocks[n];

      if n == source {
        calc {
          WpCfg(a, cfg', source, post, cover + {source});
          WpSimpleCmd(a, block, WpCfgConjunction(a, cfg', [target], post, (cover + {source}) - {source}));
          WpSimpleCmd(a, block, WpCfg(a, cfg', target, post, (cover + {source}) - {source}));
          WpSimpleCmd(a, block, post);
          WpCfg(a, cfg, source, post, cover + {source});
        }
      } else {
        var successors := if n in cfg.successors.Keys then cfg.successors[n] else [];

        if |successors| == 0 {

        } else {
          WpCfgConjunctionUpdate2(a, cfg, successors, source, target, post, cover - {n});
          assert (cover-{n})+{source} == (cover+{source})-{n};
        } 
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
    requires (forall i :: 0 <= i < |m| ==> ! (m[i] in r.Keys) && !(m[i] ==n))
    ensures IsAcyclic(r[n := m], entry, cover + {n})
    decreases cover, 0
  {
    if(entry == n) {
      assert IsAcyclic(r[n := m], entry, cover + {n}) by {
          IsAcyclicSeqOneStep(r[n := m], m, (cover + {n}) - {n});
      }
    } else {
      if entry in r.Keys {
          IsAcyclicSeqUpdate2(r, r[entry], n, m, cover - {entry}); 
          assert n != entry;
          assert (cover - {entry}) + {n} == (cover + {n}) - {entry};
      }
    }
  }
}