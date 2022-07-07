include "Util.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"
include "../dafny-libraries/src/Collections/Maps/Maps.dfy"

module Naming {
  import Util
  import Sequences = Seq

  const SEP : string := "#";

  function method VersionedName(name: string, n: nat) : string
  {
    name + SEP + Util.NatToString(n)
  }

  lemma SuffixDiffSameLength(prefix1: string, prefix2: string, suffix1:string, suffix2: string)
    requires |suffix1| == |suffix2|
    requires suffix1 != suffix2
    ensures prefix1+suffix1 != prefix1+suffix2
  {
    var i :| 0 <= i < |suffix1| && suffix1[i] != suffix2[i];

    var j := |suffix1|-i-1;

    calc {
      Sequences.Reverse(suffix1)[j];
      suffix1[i];
    !=
      suffix2[i];
      Sequences.Reverse(suffix2)[j];
    }

    assert Sequences.Reverse(prefix1+suffix1)[j] == Sequences.Reverse(suffix1)[j];
    assert Sequences.Reverse(prefix2+suffix2)[j] == Sequences.Reverse(suffix2)[j];

    assert Sequences.Reverse(prefix1+suffix1) != Sequences.Reverse(prefix2+suffix2) by {
      calc {
        Sequences.Reverse(prefix1+suffix1)[j];
        Sequences.Reverse(suffix1)[j];
      !=
        Sequences.Reverse(suffix2)[j];
        Sequences.Reverse(prefix2+suffix2)[j];
      }
    }
  }

  lemma VersionedNameInjective(prefix1: string, prefix2: string, i1: nat, i2: nat)
  requires i1 != i2
  ensures VersionedName(prefix1, i1) != VersionedName(prefix2, i2)
  {
    Util.NatToStringInjective(i1, i2);

    var i1S := Util.NatToString(i1);
    var i2S := Util.NatToString(i2);

    var s1 := prefix1 + SEP + i1S;
    var s2 := prefix2 + SEP + i2S;

    if |i1S| == |i2S| {
      assert s1 != s2 by {
        SuffixDiffSameLength(prefix1+SEP, prefix2+SEP, i1S, i2S);
      }
    } else {
      if |i1S| < |i2S| {
        var suffix1 := SEP+i1S;

        var prefix2 := prefix2 + SEP + i2S[0..|i2S|-|i1S|-1];
        var suffix2 := i2S[|i2S|-|i1S|-1..];

        assert suffix1[0] != suffix2[0] by {
          Util.HashTagNotInNatString(i2);
        }

        SuffixDiffSameLength(prefix1, prefix2 + SEP + i2S[0..|i2S|-|i1S|-1], SEP + i1S, i2S[|i2S|-|i1S|-1..]);

        assert prefix1+(SEP+i1S) == prefix1+SEP+i1S;
        assert (prefix2+SEP+i2S[0..|i2S|-|i1S|-1])+i2S[|i2S|-|i1S|-1..] == prefix2+SEP+i2S;
      } else {
        //symmetric to other case
        var suffix2 := SEP+i2S;

        var prefix1' := prefix1 + SEP + i1S[0..|i1S|-|i2S|-1];
        var suffix1 := i1S[|i1S|-|i2S|-1..];

        assert suffix1[0] != suffix2[0] by {
          Util.HashTagNotInNatString(i1);
        }

        SuffixDiffSameLength(prefix1', prefix2, suffix1, suffix2);

        assert (prefix1+SEP+i1S[0..|i1S|-|i2S|-1])+i1S[|i1S|-|i2S|-1..] == prefix1+SEP+i1S;
        assert prefix2+(SEP+i2S) == prefix2+SEP+i2S;
      }
    }
  }

  function {:opaque} VarNameSet(names: set<string>, i0: nat, i1: nat) : set<string>
  {
    set prefix, i | prefix in names && i0 <= i < i1 :: VersionedName(prefix, i)
  }

  lemma VarNameSetDisjoint(names1: set<string>, names2: set<string>, i0: nat, i1: nat, i2: nat, i3: nat)
    requires i0 <= i1 <= i2 <= i3
    ensures VarNameSet(names1, i0, i1) !! VarNameSet(names2, i2, i3)
  {
    forall i,j,name1,name2 | i != j
    ensures VersionedName(name1, i) != VersionedName(name2, j)
    {
      VersionedNameInjective(name1, name2, i, j);
    }

    reveal VarNameSet();
  }

  lemma VarNameSetExtend(names: set<string>, start: nat, end1: nat, end2: nat)
    requires end1 <= end2
    ensures VarNameSet(names, start, end1) <= VarNameSet(names, start, end2)
  {
    reveal VarNameSet();
  }

  lemma VarNameSetExtend2(names1: set<string>, names2: set<string>, start: nat, end1: nat, end2: nat)
    requires end1 <= end2
    ensures VarNameSet(names1, start, end1) <= VarNameSet(names1+names2, start, end2)
  {
    reveal VarNameSet();
  }

  lemma VarNameSetAppend(names1: set<string>, names2: set<string>, start1: nat, end1: nat, start2: nat, end2: nat)
    requires 
      && start1 <= start2
      && end1 <= end2
    ensures
      VarNameSet(names1, start1, end1) + VarNameSet(names2, start2, end2) <= 
      VarNameSet(names1+names2, start1, end2)
  {
    reveal VarNameSet();
  }

}