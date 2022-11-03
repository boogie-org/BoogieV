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

  /*
  function ComputeCoverSetsSeq(r: SuccessorRel, ns: seq<BlockId>, cover: set<BlockId>) : (res: map<BlockId, set<BlockId>>)
    requires IsAcyclicSeq(r, ns, cover)
    decreases cover, 1, ns
    ensures (forall n2 | n2 in res.Keys :: IsAcyclic(r, n2, res[n2]))
  {
    if |ns| != 0 then
        ComputeCoverSets(r, ns[0], cover) + ComputeCoverSetsSeq(r, ns[1..], cover)
    else
        map[]
  }

  function ComputeCoverSets(r: SuccessorRel, n: BlockId, cover: set<BlockId>) : (res: map<BlockId, set<BlockId>>)
    requires IsAcyclic(r, n, cover)
    decreases cover, 0
    ensures (forall n2 | n2 in res.Keys :: IsAcyclic(r, n2, res[n2]))
  {
    if n in r.Keys then
        ComputeCoverSetsSeq(r, r[n], cover - {n})
    else 
        map[]
  }
  */

  function ModifiedVarsSeqCfg(r: SuccessorRel, blocks: map<BlockId, BasicBlock>, ns: seq<BlockId>, cover: set<BlockId>) : (res: seq<(var_name, Ty)>)
    requires IsAcyclicSeq(r, ns, cover)
    decreases cover, 1, ns

  function ModifiedVarsCfg(r: SuccessorRel, blocks: map<BlockId, BasicBlock>, n: BlockId, cover: set<BlockId>) : (res: seq<(var_name, Ty)>)
    requires IsAcyclic(r, n, cover) && r.Keys <= blocks.Keys
    decreases cover, 0
  {
    if n in r.Keys then
      ModifiedVars(SimpleCmd(blocks[n])) + ModifiedVarsSeqCfg(r, blocks, r[n], cover - {n})
    else
      []
  }

  function PassifiedBlocks(blocks: map<BlockId, BasicBlock>): map<BlockId, BasicBlock>
  {
    map blockId | blockId in blocks.Keys :: PassifySimpleCmd(blocks[blockId])
  }
  
  lemma {:verify false} PassifyCfgSeqCorrect<A(!new)>(a: absval_interp<A>, g: Cfg, ns: seq<BlockId>, pred: map<BlockId, seq<BlockId>>, cover: set<BlockId>, s: state<A>)
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
        && (var defVars' := GetVarNames(ModifiedVars(SimpleCmd(sc1))) + defVars;
            UseAfterDef(sc2, defVars'))
    }
  }

  lemma WellFormedTypesModVars(sc: SimpleCmd, tcons: set<tcon_name>)
    requires 
      && sc.WellFormedTypes(tcons)
      && sc.PredicateRec((sc1: SimpleCmd) => !sc1.Havoc?, e => true) 
      /* no havoc assumption is not required to prove the lemma
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
    case _ => 
  }


  lemma UseAfterDefWellFormed(sc: SimpleCmd, defVars: set<var_name>)
    requires UseAfterDef(sc, defVars)
    ensures sc.WellFormedVars(defVars+GetVarNames(ModifiedVars(SimpleCmd(sc))))
  {
    
  }


  lemma PassifyLocalLemma<A(!new)>(a: absval_interp<A>, sc: SimpleCmd, post: Predicate<A>, defVars: set<var_name>, tcons: set<tcon_name>)
    requires 
      && Sequences.HasNoDuplicates(GetVarNamesSeq(ModifiedVars(SimpleCmd(sc))))
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
            var defVars2 := GetVarNames(ModifiedVars(SimpleCmd(sc1))) + defVars;
            var modVars2 := ModifiedVars(SimpleCmd(sc2));
            var modVars1 := ModifiedVars(SimpleCmd(sc1));
            var passiveSc2 := PassifySimpleCmd(sc2);
            var passiveSc1 := PassifySimpleCmd(sc1);
            var forallSc2Post := ForallVarDecls(a, modVars2, WpSimpleCmd(a, passiveSc2, post));
            calc {
              WpSimpleCmd(a, sc, post)(s);
              WpSimpleCmd(a, sc1, WpSimpleCmd(a, sc2, post))(s);
              {
                assume Sequences.HasNoDuplicates(GetVarNamesSeq(ModifiedVars(SimpleCmd(sc2))));
                assume defVars2 !! GetVarNames(ModifiedVars(SimpleCmd(sc2)));
                PassifyLocalLemma(a, sc2, post, defVars2, tcons);
                WpSimpleCmdPointwise2(a, sc1, WpSimpleCmd(a, sc2, post), forallSc2Post);
              }
              WpSimpleCmd(a, sc1, forallSc2Post)(s);
              {
                assume Sequences.HasNoDuplicates(GetVarNamesSeq(ModifiedVars(SimpleCmd(sc1))));
                assume defVars !! GetVarNames(ModifiedVars(SimpleCmd(sc1)));
                PassifyLocalLemma(a, sc1, post, defVars, tcons);
              }
              ForallVarDecls(a, modVars1, WpSimpleCmd(a, passiveSc1, forallSc2Post))(s);
              { 
                //using htat modVars2 does not appear in passiveSc1
                forall s'
                ensures WpSimpleCmd(a, passiveSc1, forallSc2Post)(s') ==
                        ForallVarDecls(a, modVars2, WpSimpleCmd(a, passiveSc1, WpSimpleCmd(a, passiveSc2, post)))(s')
                {
                    assert passiveSc1.WellFormedVars((defVars+GetVarNames(modVars1)) + {}) by {
                      assume false;
                    }
                    
                    assert (defVars+GetVarNames(modVars1)) !! GetVarNames(modVars2) by {
                      assume false;
                    }

                    assert GetTypeConstr(modVars2) <= tcons by {
                      WellFormedTypesModVars(sc2, tcons);
                    }

                    RemoveScopedVarsAuxProof.PullForallWpSimpleCmd(a, tcons, defVars+GetVarNames(modVars1), {}, modVars2, passiveSc1, WpSimpleCmd(a, passiveSc2, post), s');
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
      

  lemma {:verify false} PassifyCfgCorrect<A(!new)>(a: absval_interp<A>, g: Cfg, n: BlockId, pred: map<BlockId, seq<BlockId>>, cover: set<BlockId>, s: state<A>)
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