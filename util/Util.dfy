include "../dafny-libraries/src/Wrappers.dfy"

module Util {

  import opened Wrappers

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

  lemma {:verify false} HashTagNotInNatString(n: nat)
    ensures '#' !in NatToString(n)
  { }

  lemma {:verify false} NatToStringInjective(n1: nat, n2: nat)
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

  lemma {:verify false} OptionBoolExhaust(a: Option<bool>)
    ensures a == None || a == Some(true) || a == Some(false)
  {
    match a
    case None => 
    case Some(true) =>
    case Some(false) =>
  }

  method Sort(a: array<string>)
    modifies a
    ensures 
      && Sorted(a, 0, a.Length)
      && multiset(a[..]) == old(multiset(a[..]))
      //DISCUSS: possible to derive conjunct below from above?
      && (set i | 0 <= i < a.Length :: a[i]) == old((set i | 0 <= i < a.Length :: a[i]))

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

  //TODO
  lemma {:verify false} SortedUnique(s1: seq<string>, s2: seq<string>, xs: set<string>)
    requires |s1| == |s2| == |xs|
    requires (set x | x in s1) == (set x | x in s2) == xs
    requires SortedSeq(s1, 0, |s1|)
    requires SortedSeq(s2, 0, |s2|)
    ensures s1 == s2
  {
    if xs == {} {
    } else {
      var x :| forall y | y in s1 :: LexRelStr(x,y);
      forall y | y in s1
      ensures LexRelStr(s1[0], y)
      {
        var i :| 0 <= i < |s1| && s1[i] == y;
        if i > 0 {
          assume false;
        } else {
          assume false;
          LexRelConnex(x, x);
        }
      }
      assume false;
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
      invariant (set j | 0 <= j < i :: a[j]) == s-s'
    {
      var x :| x in s';

      var a0Seq := a[..];

      a[i] := x;

      assert forall j | 0 <= j < i :: a[j] == a0Seq[j];
      assert (set j | 0 <= j < i :: a[j]) == s-s';

      var temp := s';
      s' := s' - {x};

      assert (set j | 0 <= j < i+1 :: a[j]) == (s-temp)+{x};
      i := i+1;
    }
    
    Sort(a);
    
    assert (set j | 0 <= j < i :: a[j]) == s;

    var res := a[..];

    assert res == SetToSequenceStr(s) by {
      SortedUnique(res, SetToSequenceStr(s), s);
    }

    return res;
  }

  predicate method LexRelStr(s1: string, s2: string)
  {
    || s1 == []
    || (s2 != [] && s1[0] < s2[0]) 
    || (s2 != [] && s1[0] == s2[0] && LexRelStr(s1[1..], s2[1..]))
  }

lemma {:verify false} LexRelConnex(s1: string, s2: string)
  ensures LexRelStr(s1, s2) || LexRelStr(s2, s1)
{ }

lemma {:verify false} LexRelAntisym(s1: string, s2: string)
  requires LexRelStr(s1, s2)
  requires LexRelStr(s2, s1)
  ensures s1 == s2
{ }

lemma {:verify false} LexRelTransitive(s1: string, s2: string, s3: string)
  requires LexRelStr(s1, s2)
  requires LexRelStr(s2, s3)
  ensures LexRelStr(s1, s3)
{ }

lemma {:verify false} LexRelIsTotalOrder()
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
following definitions taken from http://leino.science/papers/krml275.html
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
    // The following lemma {:verify false} call establishes that there is a
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

}