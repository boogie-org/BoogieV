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
    decreases succ.Keys - visitedAndStack.0, 1, ns
    ensures
      var res := TopologicalOrderAuxSeq(succ, ns, visitedAndStack);
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
    ensures
      var (visited', stack'):= TopologicalOrderAux(succ, n, visitedAndStack);
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
      var (visitedRes, stackRes) :=
        if n in succ.Keys then
          TopologicalOrderAuxSeq(succ, succ[n], (visited', stack))
        else 
          (visited', stack);

      (visitedRes, [n]+stackRes)
  }

  function method TopologicalOrder(cfg: Cfg, blocksSeq: seq<BlockId>) : seq<BlockId>
  {
    TopologicalOrderAuxSeq(cfg.successors, blocksSeq, ({}, [])).1
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
  ensures
    var pred := PredecessorMap(succ, ns);

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
  }

}