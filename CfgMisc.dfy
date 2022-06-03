
  include "Cfg.dfy"

  module CfgMisc {
    import opened BoogieLang
    import opened BoogieSemantics
    import opened Wrappers
    import opened BoogieCfg


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

  /*============================Wp with acyclicity============================*/
  function WpCfgConjunctionAcyclic<A(!new)>(
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

  function WpCfgAcyclic<A(!new)>(a: absval_interp<A>, g: Cfg, n: BlockId, post: Predicate<A>, cover: set<BlockId>) : Predicate<A>
    requires g.successors.Keys <= g.blocks.Keys //not being in the domain of the successor relation is the same as not having any successors
    requires IsAcyclic(g.successors, n, cover)
    decreases cover, 0
  {
    if n !in g.blocks.Keys then
      post
    else 
      var successors := if n in g.successors.Keys then g.successors[n] else [];
      if |successors| == 0 then 
        WpShallowSimpleCmd(a, g.blocks[n], post)
      else 
        WpShallowSimpleCmd(a, g.blocks[n], WpCfgConjunction(a, g, successors, post, cover - {n}))
  }

  lemma WpCfgConjunctionAcyclicEquiv<A(!new)>(a: absval_interp<A>, g: Cfg, ns: seq<BlockId>, post: Predicate<A>, cover: set<BlockId>)
    requires g.successors.Keys <= g.blocks.Keys 
    requires IsAcyclicSeq(g.successors, ns, cover)
    ensures WpCfgConjunction(a, g, ns, post, cover) == WpCfgConjunctionAcyclic(a, g, ns, post, cover)
    decreases cover, 1, ns

  lemma WpCfgAcyclicEquiv<A(!new)>(a: absval_interp<A>, g: Cfg, n: BlockId, post: Predicate<A>, cover: set<BlockId>)
    requires g.successors.Keys <= g.blocks.Keys //not being in the domain of the successor relation is the same as not having any successors
    requires IsAcyclic(g.successors, n, cover)
    ensures WpCfg(a, g, n, post, cover) == WpCfgAcyclic(a, g, n, post, cover)
    decreases cover, 0
  {
    var successors := if n in g.successors.Keys then g.successors[n] else [];
    if |successors| != 0 {
      WpCfgConjunctionAcyclicEquiv(a, g, successors, post, cover - {n});
    }
  }

    
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
}
