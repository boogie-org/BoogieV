include "../lang/Cfg.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"

module CfgHelper {
  import opened BoogieCfg
  import Sequences = Seq

  type Graph<T> = map<T, seq<T>>

  /** Topological order */

  function method TopologicalOrderAuxSeq<T>(
    succ: Graph<T>, 
    ns: seq<T>, 
    visitedAndStack: (set<T>, seq<T>)
    ) : (set<T>, seq<T>)
    requires GraphWf(succ)
    requires (forall n | n in ns :: n in succ.Keys)
    requires (forall n | n in visitedAndStack.1 :: n in succ.Keys)
    decreases succ.Keys - visitedAndStack.0, 1, ns
    ensures
      var res := TopologicalOrderAuxSeq(succ, ns, visitedAndStack);

      && (forall n | n in res.1 :: n in succ.Keys)
      && visitedAndStack.0 <= res.0      
      //&& (forall n | n in ns :: n !in visitedAndStack.0 ==> n in res.1)
  {
    if |ns| == 0 then visitedAndStack
    else
      var visitedAndStack' := TopologicalOrderAux(succ, ns[0], visitedAndStack);
      TopologicalOrderAuxSeq(succ, ns[1..], visitedAndStack')
  }

  function method TopologicalOrderAux<T>(
    succ: Graph<T>, 
    n: T, 
    visitedAndStack: (set<T>, seq<T>)
    ) : (set<T>, seq<T>)
    requires GraphWf(succ)
    requires n in succ.Keys
    requires (forall n | n in visitedAndStack.1 :: n in succ.Keys)
    ensures
      var (visited', stack'):= TopologicalOrderAux(succ, n, visitedAndStack);
      && (forall n | n in stack' :: n in succ.Keys)
      && visitedAndStack.0 <= visited'      
      && ((n !in visitedAndStack.0) ==> 
              && n in visited'
              && stack'[0] == n) 
    decreases succ.Keys - visitedAndStack.0, 0
  {
    var (visited, stack) := visitedAndStack;
    if n in visited then
      (visited, stack)
    else 
      var visited' := visited + {n};
      var successors : seq<T> := if n in succ.Keys then succ[n] else [];
      assert n in succ.Keys;
      var (visitedRes, stackRes) :=
        if n in succ.Keys then
          TopologicalOrderAuxSeq(succ, succ[n], (visited', stack))
        else 
          (visited', stack);

      (visitedRes, [n]+stackRes)
  }

  function method TopologicalOrder(cfg: Cfg) : seq<BlockId>
    requires CfgWf(cfg)
    //&& forall n | n in blocksSeq :: n in cfg.successors.Keys
    ensures
      var res := TopologicalOrder(cfg);
      (forall n | n in res :: n in cfg.successors.Keys)
  {
    //TopologicalOrderAuxSeq(cfg.successors, blocksSeq, ({}, [])).1
    TopologicalOrderAux(cfg.successors, cfg.entry, ({}, [])).1
  }

  /*
  lemma TopologicalOrderAuxSeqCorrect(
    succ: Graph<BlockId>, 
    ns: seq<BlockId>, 
    visitedAndStack: (set<BlockId>, seq<BlockId>),
    cover: set<BlockId>
  )
    requires IsAcyclicSeq(succ, ns, cover)
    requires GraphWf(succ)
    requires n in succ.Keys
    requires (forall n | n in visitedAndStack.1 :: n in succ.Keys)
    ensures
      var (visited', stack'):= TopologicalOrderAux(succ, n, visitedAndStack);
      forall i | 0 <= i < |stack'| :: (set nSucc | nSucc in succ[stack'[i]]) <=  (set j | 0 < j < |stack'| :: stack'[j]) 
    */

  lemma TopologicalOrderAuxCorrect(
    succ: Graph<BlockId>, 
    n: BlockId, 
    visitedAndStack: (set<BlockId>, seq<BlockId>),
    cover: set<BlockId>
  )
    requires IsAcyclic(succ, n, cover)
    requires GraphWf(succ)
    requires n in succ.Keys
    requires (forall n | n in visitedAndStack.1 :: n in succ.Keys)
    ensures
      var (visited', stack'):= TopologicalOrderAux(succ, n, visitedAndStack);
      forall i | 0 <= i < |stack'| :: (set nSucc | nSucc in succ[stack'[i]]) <=  (set j | i < j < |stack'| :: stack'[j]) 
  
  
  lemma TopologicalOrderCorrect(
    cfg: Cfg, 
    cover: set<BlockId>
  )
    requires CfgWf(cfg)
    requires
      var succ := cfg.successors;
      && IsAcyclic(succ, cfg.entry, cover)
      && GraphWf(succ)
      && cfg.entry in succ.Keys
    ensures
      var succ := cfg.successors;
      var topo := TopologicalOrder(cfg);
      forall i | 0 <= i < |topo| :: (set nSucc | nSucc in succ[topo[i]]) <=  (set j | i < j < |topo| :: topo[j]) 
  {
    var (_, topo):= TopologicalOrderAux(cfg.successors, cfg.entry, ({}, []));
    TopologicalOrderAuxCorrect(cfg.successors, cfg.entry, ({}, []), cover);
    assume forall i | 0 <= i < |topo| :: (set nSucc | nSucc in cfg.successors[topo[i]]) <=  (set j | i < j < |topo| :: topo[j]);
  }

  
  /** Predecessor map */
  function method PredecessorMap<T>(succ: Graph<T>, ns: seq<T>) : Graph<T>
  {
    var f := (predMap: Graph<T>, n: T) => 
      if n in succ.Keys then
        predMap + map s | s in succ[n] :: if s in predMap.Keys then predMap[s]+[n] else [n]
      else 
        predMap;

    Sequences.FoldLeft(f, map[], ns)
  }

  lemma PredecessorMapCorrect<T>(succ: Graph<T>, ns: seq<T>)
    requires succ.Keys <= set n | n in ns :: n
    requires GraphWf(succ)
    ensures
      var pred := PredecessorMap(succ, ns);

    && pred.Keys <= succ.Keys
    /** only predecessors are recorded  */
    && (forall n | n in pred.Keys :: forall p | p in pred[n] :: p in succ.Keys && n in succ[p])
    /** every predecessor is recorded */
    && (forall n | n in succ.Keys :: forall s | s in succ[n] :: s in pred.Keys && n in pred[s])
  {
    var f := (predMap: Graph<T>, n: T) => 
      if n in succ.Keys then
        predMap + map s | s in succ[n] :: if s in predMap.Keys then predMap[s]+[n] else [n]
      else 
        predMap;
    var stp := (g: Graph<T>, n: T, g': Graph<T>) => g' == f(g,n);
    
    var inv := (pred: Graph<T>, ns: seq<T>) => 
      (forall n | n in pred.Keys :: forall p | p in pred[n] :: p in succ.Keys && n in succ[p]);
    Sequences.LemmaInvFoldLeft(inv, stp, f, map [], ns);
    

    var inv2 := (pred: Graph<T>, ns: seq<T>) => 
      (forall n | n in succ.Keys && n !in ns :: forall s | s in succ[n] :: s in pred.Keys && n in pred[s]);
    Sequences.LemmaInvFoldLeft(inv2, stp, f, map [], ns);


    var inv3 := (pred: Graph<T>, ns: seq<T>) => pred.Keys <= succ.Keys;
    Sequences.LemmaInvFoldLeft(inv3, stp, f, map [], ns);
  }

}