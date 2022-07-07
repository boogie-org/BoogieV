include "../lang/BoogieSemantics.dfy"
include "../transformations/DesugarScopedVarsImpl.dfy"
include "../transformations/MakeScopedVarsUniqueProof.dfy"
include "Naming.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"
include "../dafny-libraries/src/Collections/Maps/Maps.dfy"

module ForallAppend {

  import opened BoogieLang
  import opened BoogieSemantics
  import Sequences = Seq
  import Maps
  import Util
  import opened Wrappers
  import opened DesugarScopedVarsImpl
  import MakeScopedVarsUniqueProof
  import opened Naming

  lemma SeqSliceAux<A>(s1: seq<A>, s2: seq<A>)
    requires |s1| > 0
    ensures (s1+s2)[1..] == s1[1..]+s2
  { }

  //relies on Dafny checking pointwise equality when checking map equality
  lemma StateUpdVarDeclsSwapAux<A(!new)>(s: state<A>, d: seq<VarDecl>, vs: seq<Val<A>>, x: var_name, v: Val<A>)
  requires x !in GetVarNames(d)
  requires |d| == |vs|
  ensures StateUpdVarDecls(s, d, vs)[x := v] == StateUpdVarDecls(s[x := v], d, vs)
  { }

  lemma StateUpdVarDeclsSwap<A(!new)>(s: state<A>, d1: seq<VarDecl>, d2: seq<VarDecl>, vs1: seq<Val<A>>, vs2: seq<Val<A>>)
    requires |d1| == |vs1| && |d2| == |vs2|
    requires GetVarNames(d1) !! GetVarNames(d2)
    ensures StateUpdVarDecls(StateUpdVarDecls(s, d1, vs1), d2, vs2) == StateUpdVarDecls(StateUpdVarDecls(s, d2, vs2), d1, vs1)
  {
    if |d1| > 0 {
      var x := d1[0].0;
      var v := vs1[0];
      calc {
        StateUpdVarDecls(StateUpdVarDecls(s, d2, vs2), d1, vs1);
        StateUpdVarDecls(StateUpdVarDecls(s, d2, vs2), d1[1..], vs1[1..])[x := v];
        { 
          //induction hypothesis 
        }
        StateUpdVarDecls(StateUpdVarDecls(s, d1[1..], vs1[1..]), d2, vs2)[x := v];
        { StateUpdVarDeclsSwapAux(StateUpdVarDecls(s, d1[1..], vs1[1..]), d2, vs2, x, v); }
        StateUpdVarDecls(StateUpdVarDecls(s, d1[1..], vs1[1..])[x := v], d2, vs2);
        StateUpdVarDecls(StateUpdVarDecls(s, d1, vs1), d2, vs2);
      }
    }
  }

  lemma StateUpdVarDeclsSplit<A(!new)>(s: state<A>, d1: seq<VarDecl>, d2: seq<VarDecl>, vs1: seq<Val<A>>, vs2: seq<Val<A>>)
    requires |d1| == |vs1| && |d2| == |vs2|
    ensures StateUpdVarDecls(s, d1+d2, vs1+vs2) == StateUpdVarDecls(StateUpdVarDecls(s, d2, vs2), d1, vs1)
  {
    if |d1| == 0 {
      calc {
        StateUpdVarDecls(s, d1+d2, vs1+vs2);
        { 
          assert d1+d2 == d2;
          assert vs1+vs2 == vs2;
        }
        StateUpdVarDecls(s, d2, vs2);
        StateUpdVarDecls(StateUpdVarDecls(s, d2, vs2), d1, vs1);
      }
    } else {
      var x := d1[0].0;
      var v := vs1[0];
      assert (d1+d2)[0].0 == x;
      assert (vs1+vs2)[0] == v;

      var sA := StateUpdVarDecls(s, (d1+d2)[1..], (vs1+vs2)[1..]);
      var sB := StateUpdVarDecls(StateUpdVarDecls(s, d2, vs2), d1[1..], vs1[1..]);

      assert sA == sB by {
        assert StateUpdVarDecls(s, d1[1..]+d2, vs1[1..]+vs2) == StateUpdVarDecls(StateUpdVarDecls(s, d2, vs2), d1[1..], vs1[1..]) by {
          StateUpdVarDeclsSplit(s, d1[1..], d2, vs1[1..], vs2);
        }
        assert (d1+d2)[1..] == d1[1..]+d2 by {
          SeqSliceAux(d1, d2); //DISCUSS (why can't Dafny prove the assertion without the helper lemma {:verify false}?)
        }
        assert (vs1+vs2)[1..] == vs1[1..]+vs2 by {
          SeqSliceAux(vs1, vs2);
        }
      }

      assert sA[x := v] == sB[x := v];

      assert StateUpdVarDecls(s, d1+d2, vs1+vs2) == sA[x := v];
      assert StateUpdVarDecls(StateUpdVarDecls(s, d2, vs2), d1, vs1) == sB[x := v];
    }
  }

  lemma StateUpdVarDeclsSplit2<A(!new)>(s: state<A>, d1: seq<VarDecl>, d2: seq<VarDecl>, vs1: seq<Val<A>>, vs2: seq<Val<A>>)
    requires |d1| == |vs1| && |d2| == |vs2|
    requires GetVarNames(d1) !! GetVarNames(d2)
    ensures StateUpdVarDecls(s, d1+d2, vs1+vs2) == StateUpdVarDecls(StateUpdVarDecls(s, d1, vs1), d2, vs2)
  {
    calc {
      StateUpdVarDecls(s, d1+d2, vs1+vs2);
      { StateUpdVarDeclsSplit(s, d1, d2, vs1, vs2); }
      StateUpdVarDecls(StateUpdVarDecls(s, d2, vs2), d1, vs1);
      { StateUpdVarDeclsSwap(s, d2, d1, vs2, vs1); }
      StateUpdVarDecls(StateUpdVarDecls(s, d1, vs1), d2, vs2);
    }
  }

  lemma ValuesRespectDeclsSlice<A(!new)>(a: absval_interp<A>, vs: seq<Val<A>>, varDecls: seq<VarDecl>, start: nat, end: nat)
  requires ValuesRespectDecls(a, vs, varDecls)
  requires 0 <= start <= end <= |varDecls|
  ensures ValuesRespectDecls(a, vs[start..end], varDecls[start..end])
  {
    forall i | 0 <= i < |vs[start..end]|
    ensures TypeOfVal(a, vs[start..end][i]) == varDecls[start..end][i].1 {
      assert vs[start..end][i] == vs[start+i];
      assert varDecls[start..end][i] == varDecls[start+i];
      assert TypeOfValues(a, vs)[start+i] == seq(|varDecls|, i requires 0 <= i < |varDecls| => varDecls[i].1)[start+i];
      assert TypeOfVal(a, vs[start+i]) == varDecls[start+i].1;
    }
  }

  lemma ValuesRespectDeclsAppend<A(!new)>(
    a: absval_interp<A>,
    varDecls1: seq<(var_name, Ty)>, 
    varDecls2: seq<(var_name, Ty)>, 
    vs1: seq<Val<A>>,
    vs2: seq<Val<A>>
  )
  requires ValuesRespectDecls(a, vs1, varDecls1)
  requires ValuesRespectDecls(a, vs2, varDecls2)
  ensures ValuesRespectDecls(a, vs1+vs2, varDecls1+varDecls2)
  {
    var vs := vs1+vs2;
    var varDecls := varDecls1+varDecls2;
    forall i | 0 <= i < |varDecls|
    ensures TypeOfVal(a, vs[i]) == varDecls[i].1
    {
      if i < |vs1| {
        assert vs[i] == vs1[i];
        assert varDecls[i] == varDecls1[i];
        assert TypeOfValues(a, vs1)[i] == seq(|varDecls|, i requires 0 <= i < |varDecls| => varDecls[i].1)[i];
      } else {
        var j := i-|vs1|;
        assert vs[i] == vs2[j];
        assert varDecls[i] == varDecls2[j];
        assert TypeOfValues(a, vs2)[j] == seq(|varDecls2|, i requires 0 <= i < |varDecls2| => varDecls2[i].1)[j];
      }
    }
  }
 
  /** This proof has lots of duplication, there should be a way to make the 
  proof shorter. */
  lemma ForallVarDeclsAppend<A(!new)>(
      a: absval_interp<A>, 
      varDecls1: seq<(var_name, Ty)>, 
      varDecls2: seq<(var_name, Ty)>, 
      p: Predicate<A>,
      s: state<A>)
    requires GetVarNames(varDecls1) !! GetVarNames(varDecls2)
    ensures    ForallVarDecls(a, varDecls1, ForallVarDecls(a, varDecls2, p))(s)
            == ForallVarDecls(a, varDecls1+varDecls2, p)(s);
    {
      var varDecls := varDecls1+varDecls2;
      if |varDecls1| == 0 {
        calc {
          ForallVarDecls(a, varDecls1, ForallVarDecls(a, varDecls2, p))(s);
          { reveal ForallVarDecls(); }
          ForallVarDecls(a, varDecls2, p)(s);
          { assert varDecls2 == varDecls1+varDecls2; }
          ForallVarDecls(a, varDecls1+varDecls2, p)(s);
        }
      } else if |varDecls2| == 0 {
        calc {
          ForallVarDecls(a, varDecls1, ForallVarDecls(a, varDecls2, p))(s);
          { reveal ForallVarDecls(); }
          ForallVarDecls(a, varDecls1, p)(s);
          { assert varDecls1 == varDecls; }
          ForallVarDecls(a, varDecls, p)(s);
        }
      } else {
        if ForallVarDecls(a, varDecls, p)(s) == None {
          NoneForallVarDecls(a, varDecls, p, s);
          var vs :| (ValuesRespectDecls(a, vs, varDecls) && p(StateUpdVarDecls(s, varDecls, vs)) == None);

          assert |vs| == |varDecls|;
          var vs1 := vs[0..|varDecls1|];
          var vs2 := vs[|varDecls1|..|varDecls|];

          assert vs1+vs2 == vs;

          assert varDecls1 == varDecls[0..|varDecls1|];
          assert varDecls2 == varDecls[|varDecls1|..|varDecls|];

          assert ValuesRespectDecls(a, vs1, varDecls1) by {
            ValuesRespectDeclsSlice(a, vs, varDecls, 0, |varDecls1|);
          }
          assert ValuesRespectDecls(a, vs2, varDecls2) by {
            ValuesRespectDeclsSlice(a, vs, varDecls, |varDecls1|, |varDecls|);
          }

          calc {
            StateUpdVarDecls(s, varDecls1+varDecls2, vs1+vs2);
            { StateUpdVarDeclsSplit2(s, varDecls1, varDecls2, vs1, vs2); }
            StateUpdVarDecls(StateUpdVarDecls(s, varDecls1, vs1), varDecls2, vs2);
          }

          var s1 := StateUpdVarDecls(s, varDecls1, vs1);

          assert ForallVarDecls(a, varDecls1, ForallVarDecls(a, varDecls2, p))(s) == None by {
            assert ForallVarDecls(a, varDecls2, p)(s1) == None by {
              assert p(StateUpdVarDecls(s1, varDecls2, vs2)) == None;
              NoneForallVarDecls2(a, varDecls2, vs2, p, s1);
            }
            
            NoneForallVarDecls2(a, varDecls1, vs1, ForallVarDecls(a, varDecls2, p), s);
          }
        } else if ForallVarDecls(a, varDecls, p)(s) == Some(true) {
          assert ForallVarDecls(a, varDecls1, ForallVarDecls(a, varDecls2, p))(s) == Some(true) by {
            forall vs1 | ValuesRespectDecls(a, vs1, varDecls1)
            ensures ForallVarDecls(a, varDecls2, p)(StateUpdVarDecls(s, varDecls1, vs1)) == Some(true)
            {
              var s1 := StateUpdVarDecls(s, varDecls1, vs1);
              forall vs2 | ValuesRespectDecls(a, vs2, varDecls2)
              ensures p(StateUpdVarDecls(s1, varDecls2, vs2)) == Some(true)
              {
                var vs := vs1+vs2;
                assert ValuesRespectDecls(a, vs, varDecls) by {
                  ValuesRespectDeclsAppend(a, varDecls1, varDecls2, vs1, vs2);
                }
                calc {
                  StateUpdVarDecls(s, varDecls1+varDecls2, vs1+vs2);
                  { StateUpdVarDeclsSplit2(s, varDecls1, varDecls2, vs1, vs2); }
                  StateUpdVarDecls(StateUpdVarDecls(s, varDecls1, vs1), varDecls2, vs2);
                }
                  
                assert p(StateUpdVarDecls(s, varDecls, vs)) == Some(true) by {
                  SomeTrueForallVarDecls2(a, varDecls, p, s, vs);
                }
              }
              SomeTrueForallVarDecls(a, varDecls2, p, s1);
            }
            SomeTrueForallVarDecls(a, varDecls1, ForallVarDecls(a, varDecls2, p), s);
          }
        } else {
          assert ForallVarDecls(a, varDecls, p)(s) == Some(false) by {
            reveal ForallVarDecls();
          }

          forall vs1 | ValuesRespectDecls(a, vs1, varDecls1)
          ensures ForallVarDecls(a, varDecls2, p)(StateUpdVarDecls(s, varDecls1, vs1)).Some?
          {
            var s1 := StateUpdVarDecls(s, varDecls1, vs1);
            forall vs2 | ValuesRespectDecls(a, vs2, varDecls2)
            ensures p(StateUpdVarDecls(s1, varDecls2, vs2)).Some?
            {
              var vs := vs1+vs2;
              assert ValuesRespectDecls(a, vs, varDecls) by {
                ValuesRespectDeclsAppend(a, varDecls1, varDecls2, vs1, vs2);
              }
              calc {
                StateUpdVarDecls(s, varDecls1+varDecls2, vs1+vs2);
                { StateUpdVarDeclsSplit2(s, varDecls1, varDecls2, vs1, vs2); }
                StateUpdVarDecls(StateUpdVarDecls(s, varDecls1, vs1), varDecls2, vs2);
              }
                
              assert p(StateUpdVarDecls(s, varDecls, vs)).Some? by {
                SomeForallVarDecls2(a, varDecls, p, s, vs);
              }
            }
            SomeForallVarDecls3(a, varDecls2, p, s1);
          }

          assert ForallVarDecls(a, varDecls1, ForallVarDecls(a, varDecls2, p))(s).Some? by {
            SomeForallVarDecls3(a, varDecls1, ForallVarDecls(a, varDecls2, p), s);
          }


          SomeFalseForallVarDecls2(a, varDecls, p, s);

          var vs :| ValuesRespectDecls(a, vs, varDecls) && p(StateUpdVarDecls(s, varDecls, vs)) == Some(false);

          assert |vs| == |varDecls|;
          var vs1 := vs[0..|varDecls1|];
          var vs2 := vs[|varDecls1|..|varDecls|];

          assert vs1+vs2 == vs;

          assert varDecls1 == varDecls[0..|varDecls1|];
          assert varDecls2 == varDecls[|varDecls1|..|varDecls|];

          assert ValuesRespectDecls(a, vs1, varDecls1) by {
            ValuesRespectDeclsSlice(a, vs, varDecls, 0, |varDecls1|);
          }
          assert ValuesRespectDecls(a, vs2, varDecls2) by {
            ValuesRespectDeclsSlice(a, vs, varDecls, |varDecls1|, |varDecls|);
          }
          
          calc {
            StateUpdVarDecls(s, varDecls1+varDecls2, vs1+vs2);
            { StateUpdVarDeclsSplit2(s, varDecls1, varDecls2, vs1, vs2); }
            StateUpdVarDecls(StateUpdVarDecls(s, varDecls1, vs1), varDecls2, vs2);
          }

          var s1 := StateUpdVarDecls(s, varDecls1, vs1);

          assert ForallVarDecls(a, varDecls2, p)(s1) == Some(false) by {
            assert p(StateUpdVarDecls(s1, varDecls2, vs2)) == Some(false);
            SomeFalseForallVarDecls(a, varDecls2, p, s1, vs2);
          }

          SomeFalseForallVarDecls(a, varDecls1, ForallVarDecls(a, varDecls2, p), s, vs1);
        }
      }
    }
}