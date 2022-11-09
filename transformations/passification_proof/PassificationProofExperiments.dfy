/**
This file contains experiments towards developing a proof for the passification phase.
There are various assume statements and the lemmas may not yet have the right specifications.
*/

include "../Passification.dfy"
include "../MakeScopedVarsUniqueProof.dfy" //for RelPred (TODO move to a better place)
include "../RemoveScopedVarsAuxProof.dfy" //for ForallVarDecls lemmas 
include "../../util/Naming.dfy"
include "../../util/SemanticsUtil.dfy"
include "../../util/AstSubsetPredicates.dfy"
include "../../util/ForallAppend.dfy"


module SSAProof {
    import opened Passification
    import opened BoogieLang
    import opened BoogieCfg
    import opened BoogieSemantics
    import opened MakeScopedVarsUniqueProof
    import RemoveScopedVarsAuxProof
    import opened Naming
    import opened SemanticsUtil
    import opened AstSubsetPredicates
    import Sequences = Seq
    import ForallAppend

    lemma SSACorrect<A>(
        a: absval_interp<A>,
        g: Cfg, 
        topo: seq<BlockId>, 
        predecessors: map<BlockId, seq<BlockId>>, 
        prevResult: SSAResult,
        cover: set<BlockId>) 
    requires 
      && g.successors.Keys <= g.blocks.Keys
      && predecessors.Keys <= g.blocks.Keys
      && (forall id | id in topo :: id in g.blocks.Keys)
         /** topo is a topological order w.r.t. predecessors */
      && (forall i | 0 <= i < |topo| :: topo[i] in predecessors.Keys ==> (set x | x in predecessors[topo[i]]) <= (set j | 0 <= j < i :: topo[j]))
         /** successors contained in blocks */
      && (forall blockId | blockId in g.successors.Keys ::
          (forall i :: 0 <= i < |g.successors[blockId]| ==> g.successors[blockId][i] in g.blocks.Keys))
          /** predecessors contained in blocks */
      && (forall blockId | blockId in predecessors.Keys ::
          (forall i | 0 <= i < |predecessors[blockId]| :: predecessors[blockId][i] in g.blocks.Keys))
      && (forall id | id in predecessors.Keys :: forall p | p in predecessors[id] :: p in g.blocks.Keys )
      && var g' := SSA(g, topo, predecessors); g'.successors.Keys <= g'.blocks.Keys
    ensures
      var g' := SSA(g, topo, predecessors);
      WpCfg(a, g, g.entry, TruePred(), cover) == WpCfg(a, g', g'.entry, TruePred(), cover)

  lemma SSAAuxCorrect<A>(
    a: absval_interp<A>, 
    cfg: Cfg, 
    idTopo: nat, 
    topo: seq<BlockId>, 
    pred: map<BlockId, seq<BlockId>>, 
    prevResult: SSAResult)
    requires 0 <= idTopo < |topo|
    requires forall i | 0 <= i < |topo| :: topo[i] in pred.Keys ==> (set x | x in pred[topo[i]]) <= (set j | 0 <= j < i :: topo[j])
    requires forall id | id in topo :: id in cfg.blocks.Keys
    requires forall id | id in pred.Keys :: forall p | p in pred[id] :: p in cfg.blocks.Keys 
    requires forall block | block in prevResult.incMaps.Keys :: prevResult.incMaps[block].Keys <= prevResult.globalIncMap.Keys
    requires prevResult.incMaps.Keys == set i | 0 <= i < idTopo :: topo[i]
    requires prevResult.blocks.Keys == set i | 0 <= i < idTopo :: topo[i]
    requires cfg.successors.Keys <= cfg.blocks.Keys 
    requires cfg.blocks.Keys == set i | i in topo
    ensures   
      var res := SSAAux(cfg, idTopo, topo, pred, prevResult);
      var curId := topo[idTopo];
      var preds := if curId in pred.Keys then pred[curId] else [];
      var predIncs := seq(|preds|, i requires 0 <= i < |preds| => if preds[i] in prevResult.incMaps.Keys then prevResult.incMaps[preds[i]] else map[]);
      var incRes := InputIncarnation(prevResult.globalIncMap, predIncs).localIncMap;
      forall i, cover | idTopo <= i < |topo| :: 
        IsAcyclic(cfg.successors, topo[idTopo], cover) ==>
          var cfg' := Cfg(cfg.entry, res.blocks, cfg.successors); //entry block irrelevant here
          var modVars := ModifiedVarsCfg(cfg.successors, res.blocks, topo[idTopo], cover);
          RelPred(incRes,
                  WpCfg(a, cfg, topo[idTopo], TruePred(), cover), 
                  ForallVarDecls(a, modVars, WpCfg(a, cfg', topo[idTopo], TruePred(), cover)),
                  map[])

  function ModifiedVarsSeqCfgAux(r: SuccessorRel, blocks: map<BlockId, BasicBlock>, ns: seq<BlockId>, cover: set<BlockId>) : (res: seq<(var_name, Ty)>)
    requires IsAcyclicSeq(r, ns, cover)
    decreases cover, 1, ns

  function ModifiedVarsCfgAux(r: SuccessorRel, blocks: map<BlockId, BasicBlock>, n: BlockId, cover: set<BlockId>) : (res: seq<(var_name, Ty)>)
    requires IsAcyclic(r, n, cover) && r.Keys <= blocks.Keys
    decreases cover, 0
  {
    if n in r.Keys then
      ModifiedVars(SimpleCmd(blocks[n])) + ModifiedVarsSeqCfgAux(r, blocks, r[n], cover - {n})
    else
      []
  }

  function ModifiedVarsCfg(r: SuccessorRel, blocks: map<BlockId, BasicBlock>, n: BlockId, cover: set<BlockId>) : (res: seq<(var_name, Ty)>)
  requires IsAcyclic(r, n, cover) && r.Keys <= blocks.Keys
  {
    Util.RemoveDuplicates(ModifiedVarsCfgAux(r, blocks, n, cover))
  }

  function PassifiedBlocks(blocks: map<BlockId, BasicBlock>): map<BlockId, BasicBlock>
  {
    map blockId | blockId in blocks.Keys :: PassifySimpleCmd(blocks[blockId])
  }
  
  lemma PassifyCfgSeqCorrect<A(!new)>(a: absval_interp<A>, g: Cfg, ns: seq<BlockId>, pred: map<BlockId, seq<BlockId>>, cover: set<BlockId>, s: state<A>)
    requires 
      && IsAcyclicSeq(g.successors, ns, cover)
      && g.successors.Keys <= g.blocks.Keys
    ensures 
      var blocks' := PassifiedBlocks(g.blocks); //If inline PassifiedBlocks, in this lemma, then verification fails
      var g' := Cfg(g.entry, blocks', g.successors);

      forall n | n in ns ::
        var modVars := (IsAcyclicElem(g.successors, ns, n, cover); ModifiedVarsCfg(g.successors, g.blocks, n, cover));
        WpCfg(a, g, n, TruePred(), cover)(s) == 
        ForallVarDecls(a, modVars, WpCfg(a, g', n, TruePred(), cover))(s)
    decreases cover, 1, ns
  {
    var blocks' := PassifiedBlocks(g.blocks);
    var g' := Cfg(g.entry, blocks', g.successors);

    forall n | n in ns 
    ensures
      var modVars := (IsAcyclicElem(g.successors, ns, n, cover); ModifiedVarsCfg(g.successors, g.blocks, n, cover));
      WpCfg(a, g, n, TruePred(), cover)(s) == 
      ForallVarDecls(a, modVars, WpCfg(a, g', n, TruePred(), cover))(s)
    {
      IsAcyclicElem(g.successors, ns, n, cover);
      PassifyCfgCorrect(a, g, n, pred, cover, s);
    }
  }

  predicate UseAfterDef(sc: SimpleCmd, defVars: set<var_name>)
  {
    match sc {
      case Skip => true
      case Assert(e) => e.FreeVars() <= defVars
      case Assume(e) => e.FreeVars() <= defVars
      case Assign(x, t, e) => e.FreeVars() <= defVars
      case Havoc(varDecls) => true
      case SeqSimple(sc1, sc2) => 
        && UseAfterDef(sc1, defVars) 
        && (var defVars' := defVars + GetVarNames(ModifiedVars(SimpleCmd(sc1)));
            UseAfterDef(sc2, defVars'))
    }
  }

  lemma GetVarNamesRemoveDuplicates(d: seq<(var_name, Ty)>)
    ensures GetVarNames(Util.RemoveDuplicates(d)) == GetVarNames(d)
  {
    assert GetVarNames(Util.RemoveDuplicates(d)) <= GetVarNames(d) by {
      forall x | x in Util.RemoveDuplicates(d)
      ensures x in d
      {
        Util.RemoveDuplicatesAuxSubset1(d, {}, x);
      }
    }

    assert GetVarNames(d) <= GetVarNames(Util.RemoveDuplicates(d))  by {
      forall x | x in d
      ensures x in Util.RemoveDuplicates(d)
      {
        Util.RemoveDuplicatesAuxSubset2(d, {}, x);
      }
    }
  }

  lemma GetTypeConstrRemoveDuplicates(d: seq<(var_name, Ty)>)
    ensures GetTypeConstr(Util.RemoveDuplicates(d)) == GetTypeConstr(d)
  {
    assert GetTypeConstr(Util.RemoveDuplicates(d)) <= GetTypeConstr(d) by {
      forall x | x in Util.RemoveDuplicates(d)
      ensures x in d
      {
        Util.RemoveDuplicatesAuxSubset1(d, {}, x);
      }
    }

    assert GetTypeConstr(d) <= GetTypeConstr(Util.RemoveDuplicates(d))  by {
      forall x | x in d
      ensures x in Util.RemoveDuplicates(d)
      {
        Util.RemoveDuplicatesAuxSubset2(d, {}, x);
      }
    }
  }

  lemma GetVarNamesModVarsAppend(sc1: SimpleCmd, sc2: SimpleCmd)
    ensures GetVarNames(ModifiedVars(SimpleCmd(sc1))) + GetVarNames(ModifiedVars(SimpleCmd(sc2))) ==
            GetVarNames(ModifiedVars(SimpleCmd(SeqSimple(sc1, sc2))))
  {
    calc {
      GetVarNames(Util.RemoveDuplicates(ModifiedVarsAuxSimpleCmd(sc1, {}) + ModifiedVarsAuxSimpleCmd(sc2, {})));
      { GetVarNamesRemoveDuplicates(ModifiedVarsAuxSimpleCmd(sc1, {}) + ModifiedVarsAuxSimpleCmd(sc2, {}));}
      GetVarNames(ModifiedVarsAuxSimpleCmd(sc1, {}) + ModifiedVarsAuxSimpleCmd(sc2, {}));
    }

    GetVarNamesRemoveDuplicates(ModifiedVarsAux(SimpleCmd(sc1), {}));
    GetVarNamesRemoveDuplicates(ModifiedVarsAux(SimpleCmd(sc2), {}));
  }

  lemma GetTypeConstrModVarsAppend(sc1: SimpleCmd, sc2: SimpleCmd)
    ensures GetTypeConstr(ModifiedVars(SimpleCmd(sc1))) + GetTypeConstr(ModifiedVars(SimpleCmd(sc2))) ==
            GetTypeConstr(ModifiedVars(SimpleCmd(SeqSimple(sc1, sc2)))) 
  {
    calc {
      GetTypeConstr(Util.RemoveDuplicates(ModifiedVarsAuxSimpleCmd(sc1, {}) + ModifiedVarsAuxSimpleCmd(sc2, {})));
      { GetTypeConstrRemoveDuplicates(ModifiedVarsAuxSimpleCmd(sc1, {}) + ModifiedVarsAuxSimpleCmd(sc2, {}));}
      GetTypeConstr(ModifiedVarsAuxSimpleCmd(sc1, {}) + ModifiedVarsAuxSimpleCmd(sc2, {}));
    }

    GetTypeConstrRemoveDuplicates(ModifiedVarsAux(SimpleCmd(sc1), {}));
    GetTypeConstrRemoveDuplicates(ModifiedVarsAux(SimpleCmd(sc2), {}));
  }

  lemma WellFormedTypesModVars(sc: SimpleCmd, tcons: set<tcon_name>)
    requires 
      && sc.WellFormedTypes(tcons)
      && sc.PredicateRec((sc1: SimpleCmd) => !sc1.Havoc?, e => true) 
      /* "no havoc assumption" should not be required to prove the postcondition
         but sufficient for this file for now */
    ensures GetTypeConstr(ModifiedVars(SimpleCmd(sc))) <= tcons;
  {
    match sc
    case Assign(x, t, e) => 
      calc {
        ModifiedVars(SimpleCmd(sc));
        Util.RemoveDuplicates(ModifiedVarsAux(SimpleCmd(sc), {}));
        Util.RemoveDuplicates([(x,t)]);
        { assert [(x,t)] + [] == [(x,t)]; }
        [(x,t)] + Util.RemoveDuplicatesAux([], {(x,t)}+{});
        [(x,t)];
      }
    case SeqSimple(sc1, sc2) => 
      assert GetTypeConstr(ModifiedVars(SimpleCmd(sc1))) <= tcons;
      assert GetTypeConstr(ModifiedVars(SimpleCmd(sc2))) <= tcons;
      GetTypeConstrModVarsAppend(sc1, sc2);
    case _ => 
  }

  lemma UseAfterDefWellFormed(sc: SimpleCmd, defVars: set<var_name>)
    requires 
      && UseAfterDef(sc, defVars)
      && sc.PredicateRec((sc1: SimpleCmd) => !sc1.Havoc?, e => true) 
      /* "no havoc assumption" should not be required to prove the postcondition
         but sufficient for this file for now */
    ensures sc.WellFormedVars(defVars+GetVarNames(ModifiedVars(SimpleCmd(sc))))
  {
    match sc
    case Assign(x, t, e) => 
    case SeqSimple(sc1, sc2) =>
      assert sc1.WellFormedVars(defVars+GetVarNames(ModifiedVars(SimpleCmd(sc1)))) by {
        UseAfterDefWellFormed(sc1, defVars);
      }
      var defVars' := defVars + GetVarNames(ModifiedVars(SimpleCmd(sc1)));
      assert UseAfterDef(sc2, defVars');
      assert sc2.WellFormedVars(defVars'+GetVarNames(ModifiedVars(SimpleCmd(sc2))));
      assert GetVarNames(ModifiedVars(SimpleCmd(sc))) == GetVarNames(ModifiedVars(SimpleCmd(sc1))) + GetVarNames(ModifiedVars(SimpleCmd(sc2))) by {
        GetVarNamesModVarsAppend(sc1, sc2);
      }

      assert defVars+GetVarNames(ModifiedVars(SimpleCmd(sc))) == defVars'+GetVarNames(ModifiedVars(SimpleCmd(sc2)));
      assert sc2.WellFormedVars(defVars+GetVarNames(ModifiedVars(SimpleCmd(sc))));

      assert sc1.WellFormedVars(defVars+GetVarNames(ModifiedVars(SimpleCmd(sc)))) by {
        SimpleCmdWellFormedVarsLarger(sc1, defVars+GetVarNames(ModifiedVars(SimpleCmd(sc1))), defVars'+GetVarNames(ModifiedVars(SimpleCmd(sc2))));
      }
    case _ =>
  }

  lemma PassifyPreservesWellFormedVars(sc: SimpleCmd, xs: set<var_name>)
    requires sc.WellFormedVars(xs)
    ensures PassifySimpleCmd(sc).WellFormedVars(xs)
  { }

  /** The following lemma captures the assumification step for a single basic block */
  lemma PassifyLocalLemma<A(!new)>(a: absval_interp<A>, sc: SimpleCmd, post: Predicate<A>, defVars: set<var_name>, tcons: set<tcon_name>)
    requires 
      && Sequences.HasNoDuplicates(GetVarNamesSeq(ModifiedVarsAux(SimpleCmd(sc), {})))
      && UseAfterDef(sc, defVars)
      && defVars !! GetVarNames(ModifiedVars(SimpleCmd(sc)))
      && sc.PredicateRec((sc1: SimpleCmd) => !sc1.Havoc?, e => true)
      && WfAbsvalInterp(a, tcons)
      && sc.WellFormedTypes(tcons)
    ensures 
      var passiveSc := PassifySimpleCmd(sc);
      var modVars := ModifiedVars(SimpleCmd(sc));
      forall s :: WpSimpleCmd(a, sc, post)(s) == ForallVarDecls(a, modVars, WpSimpleCmd(a, passiveSc, post))(s)
  {
    var passiveSc := PassifySimpleCmd(sc);
    var modVars := ModifiedVars(SimpleCmd(sc));

    forall s 
    ensures WpSimpleCmd(a, sc, post)(s) == ForallVarDecls(a, modVars, WpSimpleCmd(a, passiveSc, post))(s)
    {
        match sc {
          case Assign(x, t, e) => assume false;  
          case SeqSimple(sc1, sc2) => 
            var defVars2 := defVars + GetVarNames(ModifiedVars(SimpleCmd(sc1)));
            var modVars2 := ModifiedVars(SimpleCmd(sc2));
            var modVars1 := ModifiedVars(SimpleCmd(sc1));
            var passiveSc2 := PassifySimpleCmd(sc2);
            var passiveSc1 := PassifySimpleCmd(sc1);
            var forallSc2Post := ForallVarDecls(a, modVars2, WpSimpleCmd(a, passiveSc2, post));
            calc {
              WpSimpleCmd(a, sc, post)(s);
              WpSimpleCmd(a, sc1, WpSimpleCmd(a, sc2, post))(s);
              {
                assume Sequences.HasNoDuplicates(GetVarNamesSeq(ModifiedVarsAux(SimpleCmd(sc2), {})));
                assume defVars2 !! GetVarNames(ModifiedVars(SimpleCmd(sc2)));
                PassifyLocalLemma(a, sc2, post, defVars2, tcons);
                WpSimpleCmdPointwise2(a, sc1, WpSimpleCmd(a, sc2, post), forallSc2Post);
              }
              WpSimpleCmd(a, sc1, forallSc2Post)(s);
              {
                assume Sequences.HasNoDuplicates(GetVarNamesSeq(ModifiedVarsAux(SimpleCmd(sc1), {})));
                assume defVars !! GetVarNames(ModifiedVars(SimpleCmd(sc1)));
                PassifyLocalLemma(a, sc1, post, defVars, tcons);
              }
              ForallVarDecls(a, modVars1, WpSimpleCmd(a, passiveSc1, forallSc2Post))(s);
              { 
                //using that modVars2 does not appear in passiveSc1
                forall s'
                ensures WpSimpleCmd(a, passiveSc1, forallSc2Post)(s') ==
                        ForallVarDecls(a, modVars2, WpSimpleCmd(a, passiveSc1, WpSimpleCmd(a, passiveSc2, post)))(s')
                {
                    assert passiveSc1.WellFormedVars(defVars+GetVarNames(modVars1)) by {
                      UseAfterDefWellFormed(sc1, defVars);
                      PassifyPreservesWellFormedVars(sc1, defVars+GetVarNames(modVars1));
                    }
                    
                    assert (defVars+GetVarNames(modVars1)) !! GetVarNames(modVars2) by {
                      assume false;
                    }

                    assert GetTypeConstr(modVars2) <= tcons by {
                      WellFormedTypesModVars(sc2, tcons);
                    }

                    RemoveScopedVarsAuxProof.PullForallWpSimpleCmd(a, tcons, defVars, GetVarNames(modVars1), modVars2, passiveSc1, WpSimpleCmd(a, passiveSc2, post), s');
                }

                ForallVarDeclsPointwise(a, modVars1, 
                  WpSimpleCmd(a, passiveSc1, forallSc2Post),
                  ForallVarDecls(a, modVars2, WpSimpleCmd(a, passiveSc1, WpSimpleCmd(a, passiveSc2, post))),
                  s);
              }
              ForallVarDecls(a, modVars1, ForallVarDecls(a, modVars2, WpSimpleCmd(a, passiveSc1, WpSimpleCmd(a, passiveSc2, post))))(s);
              { 
                assert GetVarNames(modVars1) !! GetVarNames(modVars2) by {
                  assume false;
                }
                ForallAppend.ForallVarDeclsAppend(a, modVars1, modVars2, WpSimpleCmd(a, passiveSc1, WpSimpleCmd(a, passiveSc2, post)), s); 
              }
              ForallVarDecls(a, modVars1+modVars2, WpSimpleCmd(a, passiveSc1, WpSimpleCmd(a, passiveSc2, post)))(s);
              { assume false; }
              ForallVarDecls(a, modVars, WpSimpleCmd(a, passiveSc1, WpSimpleCmd(a, passiveSc2, post)))(s);
              ForallVarDecls(a, modVars, WpSimpleCmd(a, SeqSimple(passiveSc1, passiveSc2), post))(s);
            }
          case _ => 
            calc {
              ForallVarDecls(a, modVars, WpSimpleCmd(a, passiveSc, post))(s);
              ForallVarDecls(a, [], WpSimpleCmd(a, passiveSc, post))(s);
              { ForallVarDeclsEmpty(a, WpSimpleCmd(a, passiveSc, post)); }
              WpSimpleCmd(a, passiveSc, post)(s);
            }
        }
    }
  }
      

  lemma PassifyCfgCorrect<A(!new)>(a: absval_interp<A>, g: Cfg, n: BlockId, pred: map<BlockId, seq<BlockId>>, cover: set<BlockId>, s: state<A>)
    requires 
      /*
      && pred.Keys <= g.blocks.Keys
         /** successors contained in blocks */
      && (forall blockId | blockId in g.successors.Keys ::
          (forall i :: 0 <= i < |g.successors[blockId]| ==> g.successors[blockId][i] in g.blocks.Keys))
          /** predecessors contained in blocks */
      && (forall blockId | blockId in pred.Keys ::
          (forall i | 0 <= i < |pred[blockId]| :: pred[blockId][i] in g.blocks.Keys))
      && g.successors.Keys <= g.blocks.Keys
      */
      && IsAcyclic(g.successors, n, cover)
      && g.successors.Keys <= g.blocks.Keys
    ensures 
      var blocks' := PassifiedBlocks(g.blocks);
      var g' := Cfg(g.entry, blocks', g.successors);

      var modVars := ModifiedVarsCfg(g.successors, g.blocks, n, cover);
      WpCfg(a, g, n, TruePred(), cover)(s) == 
      ForallVarDecls(a, modVars, WpCfg(a, g', n, TruePred(), cover))(s)
    decreases cover, 0
    {
        var blocks' := PassifiedBlocks(g.blocks);
        var modVars := ModifiedVarsCfg(g.successors, g.blocks, n, cover);
        var g' := Cfg(g.entry, blocks', g.successors);

        if n !in g.blocks.Keys {
            assume false;
        } else {
            var successors := if n in g.successors.Keys then g.successors[n] else [];
            if |successors| == 0 {
              calc {
                WpCfg(a, g, n, TruePred(), cover);
                WpSimpleCmd(a, g.blocks[n], TruePred());
                { assume false; }
                ForallVarDecls(a, modVars, WpCfg(a, g', n, TruePred(), cover));
              }
            } else {
              assume false;
            }
        }
    }
 
}