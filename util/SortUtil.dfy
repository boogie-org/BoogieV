include "RustanMergeSort.dfy"

module StringTO refines TotalOrder {
  type T = string// the type to be compared
  predicate method Leq(a: T, b: T) {
    || a == []
    || (b != [] && a[0] < b[0]) 
    || (b != [] && a[0] == b[0] && Leq(a[1..], b[1..]))
  } // Leq(a,b) iff a <= b
  // Three properties of total orders.  Here, they are given as unproved
  // lemmas, that is, as axioms.

  lemma Antisymmetry ... { }
  lemma Transitivity ... { }
  lemma Totality ... { }
}

module StringMergeSort refines MergeSort {
  import A = StringTO 
}

module SortUtil {
  import StringTO
  import StringMergeSort

  lemma LexRelIsTotalOrder()
  ensures IsTotalOrder(StringTO.Leq)
  {
    forall s1, s2
    ensures StringTO.Leq(s1, s2) || StringTO.Leq(s2, s1)
    { StringTO.Totality(s1, s2); }

    forall s1, s2 | StringTO.Leq(s1, s2) && StringTO.Leq(s2, s1)
    ensures s1 == s2
    { StringTO.Antisymmetry(s1, s2); }

    forall s1, s2, s3 | StringTO.Leq(s1, s2) && StringTO.Leq(s2, s3)
    ensures StringTO.Leq(s1, s3)
    { StringTO.Transitivity(s1, s2, s3); }
  }

  /** 
  Various of the following definitions and lemmas are taken from http://leino.science/papers/krml275.html
  */

  predicate IsTotalOrder<A(!new)>(R: (A, A) -> bool) {
    // connexity
    && (forall a, b :: R(a, b) || R(b, a))
    // antisymmetry
    && (forall a, b :: R(a, b) && R(b, a) ==> a == b)
    // transitivity
    && (forall a, b, c :: R(a, b) && R(b, c) ==> R(a, c))
  }

  lemma ThereIsAMinimumGeneral<A>(R: (A, A) -> bool, s: set<A>)
    requires s != {}
    requires IsTotalOrder(R)
    ensures exists x :: x in s && forall y | y in s :: R(x, y)
  {
    var x :| x in s;
    if s == {x} {
      // obviously, x is the minimum
      assert x in s;
      assert forall y | y in s :: x == y;
    } else {
      // The minimum in s might be x, or it might be the minimum
      // in s - {x}. If we knew the minimum of the latter, then
      // we could compare the two.
      // Let's start by giving a name to the smaller set:
      var s' := s - {x};
      // So, s is the union of s' and {x}:
      assert s == s' + {x};
      // The following lemma call establishes that there is a
      // minimum in s'.
      ThereIsAMinimumGeneral(R, s');
      var x' :| x' in s' && forall y | y in s' :: R(x', y);

      var xMin := if R(x, x') then x else x';

      assert xMin in s;

      forall y | y in s
      ensures R(xMin, y)
      {
      }
    }
  }

  lemma ThereIsAMinimum(s: set<string>)
    requires s != {}
    ensures exists x :: x in s && forall y | y in s :: StringTO.Leq(x, y)
  {
    assert IsTotalOrder(StringTO.Leq) by {
      LexRelIsTotalOrder();
    }

    ThereIsAMinimumGeneral(StringTO.Leq, s);
  }  

  predicate SortedSeq(a: seq<string>, low: int, high: int)
    requires 0 <= low <= high <= |a|
  {
    forall i, j :: low <= i < j < high ==> StringTO.Leq(a[i], a[j])
  }

  lemma UniqueMinimum(x1: string, x2: string, s: set<string>)
  requires x1 in s && x2 in s
  requires forall x | x in s :: StringTO.Leq(x1,x)
  requires forall x | x in s :: StringTO.Leq(x2,x)
  ensures x1 == x2
  {
    assert StringTO.Leq(x1, x2) || StringTO.Leq(x2, x1) by {
      StringTO.Totality(x1, x2);
    }

    if StringTO.Leq(x1, x2) && StringTO.Leq(x2, x1) {
      assert x1 == x2 by {
        StringTO.Antisymmetry(x1, x2);
      }
    }
  }

  lemma CardMono<A>(s1: set<A>, s2: set<A>)
  requires s1 <= s2
  ensures |s1| <= |s2|
  {
    if s1 == {} {

    } else {
      var x :| x in s1;
      assert x in s2;

      assert |s1-{x}| <= |s2-{x}| by {
        CardMono(s1-{x}, s2-{x});
      }
    }
  }

  lemma CardSeqSet<A>(s: seq<A>)
  ensures |s| >= |(set x | x in s)|
  {
    if |s| == 0 {

    } else {
      var xs := set x | x in s;
      assert s[0] in xs;

      var xs' := xs-{s[0]};

      calc {
        |s|;
        |s[1..]|+1;
      >= { CardSeqSet(s[1..]); }
        |(set x | x in s[1..])|+1;
      >=
        { 
          assert (set x | x in s[1..]) >= xs';
          CardMono(xs', set x | x in s[1..]);
        }
        |xs'|+1;
      }
    }
  }

  lemma SortedUnique(s1: seq<string>, s2: seq<string>, xs: set<string>)
    requires |s1| == |s2| == |xs|
    requires (set x | x in s1) == (set x | x in s2) == xs
    requires SortedSeq(s1, 0, |s1|)
    requires SortedSeq(s2, 0, |s2|)
    ensures s1 == s2
  {
    if xs == {} {
    } else {
      assert IsTotalOrder(StringTO.Leq) by {
        LexRelIsTotalOrder();
      }

      assert forall y | y in xs :: StringTO.Leq(s1[0], y);
      assert forall y | y in xs :: StringTO.Leq(s2[0], y);

      assert s1[0] == s2[0] by {
        UniqueMinimum(s1[0], s2[0], xs);
      }

      assert s1[1..] == s2[1..] by {
        assert (set x | x in s1[1..]) + {s1[0]} == xs;
        assert |s1[1..]| == |xs|-1;

        if s1[0] in (set x | x in s1[1..]) {
          assert (set x | x in s1[1..]) == xs;
          assert |s1[1..]| >= |xs| by {
            CardSeqSet(s1[1..]);
          }
          assert false;
        }

        if s2[0] in (set x | x in s2[1..]) {
          assert (set x | x in s2[1..]) == xs;
          assert |s2[1..]| >= |xs| by {
            CardSeqSet(s2[1..]);
          }
          assert false;
        }

        SortedUnique(s1[1..], s2[1..], xs-{s1[0]});
      }
    }
  }
 
  lemma MultisetEmpty<A>(s: seq<A>)
  requires multiset(s) == multiset{};
  ensures s == []
  {
    if s != [] {
      assert s[0] in multiset(s);
      assert false;
    } 
  }

  lemma MultisetNonempty<A>(s: seq<A>)
  requires s != []
  ensures multiset(s) != multiset{}
  {
    assert s[0] in multiset(s);
  }
  
  lemma MultisetToSetSeq<A>(s1: seq<A>, s2: seq<A>)
  requires multiset(s1) == multiset(s2)
  ensures (set i | i in s1) == (set i | i in s2)
  {
    var s1Set := (set i | i in s1);
    var s2Set := (set i | i in s2);

    forall x | x in s1Set
    ensures x in s2Set
    {
      assert x in multiset(s1);
    }

    forall x | x in s2Set
    ensures x in s1Set
    {
      assert x in multiset(s2);
    }
  }

  function SetToSequenceStr(s: set<string>) : seq<string>
    ensures 
      var res := SetToSequenceStr(s);
      && (set x | x in res) == s
      && |s| == |res|
      && SortedSeq(res, 0, |res|)
  {
    if s == {} then
      []
    else
      ThereIsAMinimum(s);
      var min :| min in s && forall s' | s' in s :: StringTO.Leq(min, s');

      assert {min}+(s-{min}) == s;

      [min] + SetToSequenceStr(s-{min})
  } by method {
    var a: array<string> := new string[|s|];

    var i := 0;
    var s' := s;
    while i < |s|
      decreases s'
      invariant |s'| == |s|-i
      invariant 0 <= i <= |s|
      invariant (set j | j in a[0..i]) == s-s'
    {
      var x :| x in s';

      var a0Seq := a[..];

      a[i] := x;

      assert forall j | 0 <= j < i :: a[j] == a0Seq[j];
      assert (set j | j in a[0..i]) == s-s';

      var temp := s';
      s' := s' - {x};

      assert (set j | j in a[0..i+1]) == (s-temp)+{x};
      i := i+1;
    }

    assert i == |s|;

    assert (set j | j in a[0..i]) == s;
    assert (set j | j in a[..]) == s;
    var a0 := a[..];
    
    StringMergeSort.MergeSort(a);
    
    MultisetToSetSeq(a[..], a0);
    
    assert (set j | j in a[..]) == s;

    var res := a[..];

    assert res == SetToSequenceStr(s) by {
      SortedUnique(res, SetToSequenceStr(s), s);
    }

    return res;
  }
}