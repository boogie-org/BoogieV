include "../lang/Cfg.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"

module CfgHelper {
  import opened BoogieCfg
  import Sequences = Seq

  /** Topological order */

  /** would like to use Sequences.FoldLeft instead of a separate method here,
  but not sure how to get the termination constraints right */
  function method TopologicalOrderAuxSeq<T>(
    succ: map<T, seq<T>>, 
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
    succ: map<T, seq<T>>, 
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
  function method PredecessorMap<T>(succ: map<T, seq<T>>, ns: seq<T>) : map<T, seq<T>>
  {
    var f := (predMap: map<T, seq<T>>, n: T) => 
      if n in succ.Keys then
        predMap + map s | s in succ[n] :: if s in predMap.Keys then predMap[s]+[n] else [n]
      else 
        predMap;

    Sequences.FoldLeft(f, map[], ns)
  }

}