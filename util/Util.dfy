include "../dafny-libraries/src/Wrappers.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"

module Util {

  import opened Wrappers
  import Seq

  function RemoveDuplicates<T>(s: seq<T>): seq<T>
  {
    RemoveDuplicatesAux(s, {})
  }

  function RemoveDuplicatesAux<T>(s: seq<T>, alreadyIncluded: set<T>): seq<T>
  {
    if |s| == 0 then []
    else 
      if s[0] in alreadyIncluded then 
        RemoveDuplicatesAux(s[1..], alreadyIncluded) 
      else 
        [s[0]] + RemoveDuplicatesAux(s[1..], {s[0]}+alreadyIncluded)
  }

  method IntToString(i: int) returns (s: string) {
    if i == 0 {
      return "0";
    } 

    s := "";
    var j := i;

    if i < 0 {
      s := "-";
      j := -i;
    }

    while j != 0
      invariant j >= 0;
    {
      var d := j % 10;
      s := ['0' + d as char] + s;
      j := j / 10;
    }
  }

  function method IntToString2(i: int) : string {
    if i < 0 then "-"+NatToString(-i) else NatToString(i)
  }

  function method NatToString(n: nat) : string {
    if n == 0 then "0"
    else 
      var digit := n % 10;
      var digitString := ['0' + digit as char];
      digitString + NatToString(n/10)
  }

  lemma HashTagNotInNatString(n: nat)
    ensures '#' !in NatToString(n)
  { }

  lemma NatToStringInjective(n1: nat, n2: nat)
    requires n1 != n2
    ensures NatToString(n1) != NatToString(n2)
  /*
  {
    if n1 == 0 {
      //trivial
    } else {
      var digit1 := n1 % 10;
      var digitString1 := ['0' + digit1 as char];

      var digit2 := n2 % 10;
      var digitString2 := ['0' + digit2 as char];

      assert |digitString1| == |digitString2|;

      assume NatToString(n1/10) != NatToString(n2/10);

      if digit1 != digit2 {
        //assert ('0'+ digit1 as char) != ('1'+ digit2 as char);
        assume false;
      } else {
        assume n1/10 != n2/10;
        NatToStringInjective(n1/10, n2/10);

      }
    }
  }
  */

  function method BoolToString(b: bool) : string {
    if b then "true" else "false"
  }

  function method IndentString(s: string, n: nat) : string {
    seq(n, _ => ' ') + s
  }

  function AndOpt(b1Opt: Option<bool>, b2Opt: Option<bool>) : Option<bool> {
    if b1Opt.Some? && b2Opt.Some? then Some(b1Opt.value && b2Opt.value) else None
  }

  //the first occurrence for a key k in the sequence is relevant for the map
  function method {:opaque} SequenceToMap<K,V>(s: seq<(K,V)>) : map<K,V>
  {
    if |s| == 0 then map[]
    else SequenceToMap(s[1..])[s[0].0 := s[0].1]
  }

  lemma OptionBoolExhaust(a: Option<bool>)
    ensures a == None || a == Some(true) || a == Some(false)
  {
    match a
    case None => 
    case Some(true) =>
    case Some(false) =>
  }

  predicate method LexRelStr(s1: string, s2: string)
  {
    || s1 == []
    || (s2 != [] && s1[0] < s2[0]) 
    || (s2 != [] && s1[0] == s2[0] && LexRelStr(s1[1..], s2[1..]))
  }

  lemma LexRelConnex(s1: string, s2: string)
    ensures LexRelStr(s1, s2) || LexRelStr(s2, s1)
  { }

  lemma LexRelAntisym(s1: string, s2: string)
    requires LexRelStr(s1, s2)
    requires LexRelStr(s2, s1)
    ensures s1 == s2
  { }

  lemma LexRelTransitive(s1: string, s2: string, s3: string)
    requires LexRelStr(s1, s2)
    requires LexRelStr(s2, s3)
    ensures LexRelStr(s1, s3)
  { }

  lemma LexRelIsTotalOrder()
  ensures IsTotalOrder(LexRelStr)
  {
    forall s1, s2
    ensures LexRelStr(s1, s2) || LexRelStr(s2, s1)
    { LexRelConnex(s1, s2); }

    forall s1, s2 | LexRelStr(s1, s2) && LexRelStr(s2, s1)
    ensures s1 == s2
    { LexRelAntisym(s1, s2); }

    forall s1, s2, s3 | LexRelStr(s1, s2) && LexRelStr(s2, s3)
    ensures LexRelStr(s1, s3)
    { LexRelTransitive(s1, s2, s3); }
  }

  /** 
  various of the following definitions are taken from http://leino.science/papers/krml275.html
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
        if y == x {
          if xMin == x {

          }   
        } else {
        }
      }
    }
  }

  lemma ThereIsAMinimum(s: set<string>)
    requires s != {}
    ensures exists x :: x in s && forall y | y in s :: LexRelStr(x, y)
  {
    assert IsTotalOrder(LexRelStr) by {
      LexRelIsTotalOrder();
    }

    ThereIsAMinimumGeneral(LexRelStr, s);
  }  

  predicate Sorted(a: array<string>, low: int, high: int)
    requires 0 <= low <= high <= a.Length
    reads a
  {
    forall i, j :: low <= i < j < high ==> LexRelStr(a[i], a[j])
  }

  predicate SortedSeq(a: seq<string>, low: int, high: int)
    requires 0 <= low <= high <= |a|
  {
    forall i, j :: low <= i < j < high ==> LexRelStr(a[i], a[j])
  }

  lemma UniqueMinimum(x1: string, x2: string, s: set<string>)
  requires x1 in s && x2 in s
  requires forall x | x in s :: LexRelStr(x1,x)
  requires forall x | x in s :: LexRelStr(x2,x)
  ensures x1 == x2
  {
    assert LexRelStr(x1, x2) || LexRelStr(x2, x1) by {
      LexRelConnex(x1, x2);
    }

    if LexRelStr(x1, x2) && LexRelStr(x2, x1) {
      assert x1 == x2 by {
        LexRelAntisym(x1, x2);
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
      assert IsTotalOrder(LexRelStr) by {
        LexRelIsTotalOrder();
      }

      assert forall y | y in xs :: LexRelStr(s1[0], y);
      assert forall y | y in xs :: LexRelStr(s2[0], y);

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

  method Sort(a: array<string>)
    modifies a
    ensures 
      && Sorted(a, 0, a.Length)
      && multiset(a[..]) == old(multiset(a[..]))
      //DISCUSS: possible to derive conjunct below from above?
      //&& (set i | 0 <= i < a.Length :: a[i]) == old((set i | 0 <= i < a.Length :: a[i]))
      //&& (set i | i in a[..]) == old((set i | i in a[..]))
    
  lemma MultisetEmpty1<A>(s: seq<A>)
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
      var min :| min in s && forall s' | s' in s :: LexRelStr(min, s');

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
    
    Sort(a);
    
    MultisetToSetSeq(a[..], a0);
    
    assert (set j | j in a[..]) == s;

    var res := a[..];

    assert res == SetToSequenceStr(s) by {
      SortedUnique(res, SetToSequenceStr(s), s);
    }

    return res;
  }

}