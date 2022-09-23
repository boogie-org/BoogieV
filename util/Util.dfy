include "../dafny-libraries/src/Wrappers.dfy"
include "../dafny-libraries/src/Collections/Sequences/Seq.dfy"

module Util {
  import opened Wrappers
  import Seq

  function method RemoveDuplicates<T(==)>(s: seq<T>): seq<T>
  {
    RemoveDuplicatesAux(s, {})
  }

  function method RemoveDuplicatesAux<T>(s: seq<T>, alreadyIncluded: set<T>): seq<T>
  {
    if |s| == 0 then []
    else 
      if s[0] in alreadyIncluded then 
        RemoveDuplicatesAux(s[1..], alreadyIncluded) 
      else 
        [s[0]] + RemoveDuplicatesAux(s[1..], {s[0]}+alreadyIncluded)
  }

  function method IntToString(i: int) : string {
    if i < 0 then "-"+NatToString(-i) else NatToString(i)
  }

  function method NatToString(n: nat) : string {
    if n == 0 then "0"
    else 
      var digit := n % 10;
      var digitString := ['0' + digit as char];
      var remainder := n/10;
      (if remainder > 0 then NatToString(n/10) else "") + digitString
  }

  lemma HashTagNotInNatString(n: nat)
    ensures '#' !in NatToString(n)
  { }

  lemma NatToStringInjective(n1: nat, n2: nat)
    requires n1 != n2
    ensures NatToString(n1) != NatToString(n2)
  {
    if n1 == 0 {
      assert n2 != 0;
      var digit2 := n2 % 10;

      var digitString2 := ['0' + digit2 as char];
      var remainder2 := n2/10;

      assert "0"[0] == '0'+ 0 as char;
    } else {
      var digit1 := n1 % 10;
      var digitString1 := ['0' + digit1 as char];
      var remainder1 := n1/10;
      var res1 := (if remainder1 > 0 then NatToString(n1/10) else "") + digitString1;

      var digit2 := n2 % 10;
      var digitString2 := ['0' + digit2 as char];
      var remainder2 := n2/10;
      var res2 := (if remainder2 > 0 then NatToString(n2/10) else "")+ digitString2;

      assert |digitString1| == |digitString2|;

      if digit1 != digit2 {
        assert ('0'+ digit1 as char) != ('0'+ digit2 as char);
        assert digitString1 != digitString2;
        assert res1[|res1|-1] != res2[|res2|-1];
      } else {
        assert NatToString(n1/10) != NatToString(n2/10) by {
          assert n1/10 != n2/10;
          NatToStringInjective(n1/10, n2/10);
        }
        assert res1[0..|res1|-1] != res2[0..|res2|-1];
      }
    }
  }

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

  lemma HasNoDuplicatesAppDisj2<T>(s1: seq<T>, s2: seq<T>)
  requires 
    && Seq.HasNoDuplicates(s1)
    && Seq.HasNoDuplicates(s2)
    && (set s | s in s1) !! (set s | s in s2)
  ensures 
    Seq.HasNoDuplicates(s1+s2)
  {
    reveal Seq.HasNoDuplicates();
    var s := s1+s2;
    forall i,j | 0 <= i < |s| && 0 <= j < |s| && i != j
    ensures s[i] != s[j]
    {
      if 0 <= i < |s1| && 0 <= j < |s1| {
        //use that s1 has no duplicates
      } else if |s1| <= i < |s| && |s1| <= j < |s| {
        //use that s2 has no duplicates
      } else {
        var (i',j') := if 0 <= i < |s1| then (i,j) else (j,i);
        assert 0 <= i' < |s1|;
        assert |s1| <= j' < |s|;
        var xs := (set s | s in s1);
        var ys := (set s | s in s2);
        assert xs !! ys;
        assert s[i'] in xs;
        assert s[j'] in ys;
      } 
    }
  }
}