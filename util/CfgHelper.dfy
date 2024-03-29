include "../lang/Cfg.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"
include "Util.dfy"

module CfgHelper {
  import opened BoogieCfg
  import Sequences = Seq
  import Util

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
      //&& Sequences.HasNoDuplicates(stack')
      //&& visitedStack.1 <= 
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

  /*
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
      //forall i | 0 <= i < |stack'| :: (set nSucc | nSucc in succ[stack'[i]]) <=  (set j | i < j < |stack'| :: stack'[j]) 
      forall i | 0 <= i < |stack'| :: test(succ[stack'[i]]) <=  test(stack'[i+1..|stack'|])

  function test<T>(xs: seq<T>) : set<T>
  {
    set x | x in xs
  }

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
      forall i 
        | 0 <= i < |topo| 
        :: test(succ[topo[i]]) <=  test(topo[i+1..|topo|]) 
  {
    var (_, topo):= TopologicalOrderAux(cfg.successors, cfg.entry, ({}, []));
    TopologicalOrderAuxCorrect(cfg.successors, cfg.entry, ({}, []), cover);
  }
  */
  
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

  lemma ConvertTopo(succ: map<BlockId, seq<BlockId>>, pred: map<BlockId, seq<BlockId>>, topo: seq<BlockId>)
    requires forall n | n in topo :: n in succ.Keys
    requires forall n | n in succ.Keys :: n in topo
    requires forall i | 0 <= i < |topo| :: (set nSucc | nSucc in succ[topo[i]]) <=  (set j | i < j < |topo| :: topo[j]) 
    requires Sequences.HasNoDuplicates(topo)
    requires
      && pred.Keys <= succ.Keys
      /** only predecessors are recorded  */
      && (forall n | n in pred.Keys :: forall p | p in pred[n] :: p in succ.Keys && n in succ[p])
      /** every predecessor is recorded */
      && (forall n | n in succ.Keys :: forall s | s in succ[n] :: s in pred.Keys && n in pred[s])
    ensures forall i | 0 <= i < |topo| :: topo[i] in pred.Keys ==> (set x | x in pred[topo[i]]) <= (set j | 0 <= j < i :: topo[j])
  {
    forall i | 0 <= i < |topo| && topo[i] in pred.Keys
    ensures (set x | x in pred[topo[i]]) <= (set j | 0 <= j < i :: topo[j])
    {
      forall x | x in pred[topo[i]]
      ensures x in (set j | 0 <= j < i :: topo[j])
      {

        if x !in (set j | 0 <= j < i :: topo[j]) {
          var xIdx :| i <= xIdx < |topo| && topo[xIdx] == x;
          assert topo[i] in succ[topo[xIdx]];

          var xs := (set nSucc | nSucc in succ[topo[xIdx]]);
          var ys := (set j | xIdx < j < |topo| :: topo[j]);

          assert xs <= ys;
          assert topo[i] in xs;
          assert topo[i] in ys;

          assert false by {
            var k :| xIdx < k < |topo| && topo[i] == topo[k];
            reveal Sequences.HasNoDuplicates();
          }
        }
      }
    }
  }

  function method PrintCfgAux(cfg: Cfg, blockIds: seq<BlockId>, idx: BlockId) : string
    requires CfgWf(cfg)
    requires forall id | id in blockIds :: id in cfg.blocks.Keys && id in cfg.successors.Keys
    decreases |blockIds|-idx
  {
    if idx >= |blockIds| then
      ""
    else
      var bId := blockIds[idx];
      var blockName := "B"+Util.NatToString(bId);
      var blockString := cfg.blocks[bId].ToString(0);
      var successors := cfg.successors[bId];

      "\n"+blockName+":\n"+
      blockString+"\n"+
      (
      if successors == [] then 
        "return;\n"
      else
        Sequences.FoldLeft( 
            (s: string, bSucc: BlockId) => 
              if bSucc in cfg.blocks.Keys then s+", B"+ Util.NatToString(bSucc) else "block not in successors",
              "targets: " + "B"+ Util.NatToString(successors[0]),
              successors[1..])+"\n"
      ) +
      PrintCfgAux(cfg, blockIds, idx+1)
  }

  function method PrintCfg(cfg: Cfg, blockIds: seq<BlockId>) : string
    requires CfgWf(cfg)
    requires forall id | id in blockIds :: id in cfg.blocks.Keys
  {
    PrintCfgAux(cfg, blockIds, 0)
  }

}