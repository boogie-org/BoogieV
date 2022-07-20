/** This implementation was written by Rustan Leino (originally for integers). */

abstract module TotalOrder {
  type T(0) // the type to be compared
  predicate method Leq(a: T, b: T) // Leq(a,b) iff a <= b
  // Three properties of total orders.  Here, they are given as unproved
  // lemmas, that is, as axioms.
  lemma Antisymmetry(a: T, b: T)
    requires Leq(a, b) && Leq(b, a)
    ensures a == b
  lemma Transitivity(a: T, b: T, c: T)
    requires Leq(a, b) && Leq(b, c)
    ensures Leq(a, c)
  lemma Totality(a: T, b: T)
    ensures Leq(a, b) || Leq(b, a)
}

abstract module MergeSort {
  import A : TotalOrder  // let A denote some module that has the members of TotalOrder

  predicate IsSorted(a: array<A.T>, lo: nat, hi: nat)
    requires lo <= hi <= a.Length
    reads a
  {
    forall i, j :: lo <= i < j < hi ==> A.Leq(a[i], a[j])
  }

  method MergeSort(a: array<A.T>)
    modifies a
    ensures IsSorted(a, 0, a.Length)
    ensures multiset(a[..]) == multiset(old(a[..]))
  {
    if a.Length < 2 {
      return;
    }
    var scratch := new A.T[a.Length];
    ghost var resultInSrc := MergeSortAux(a, scratch, 0, a.Length, InSource);
    assert resultInSrc;
    calc {
      multiset(old(a[..]));
    ==  { assert old(a[..]) == old(a[0..a.Length]); }
      multiset(old(a[0..a.Length]));
    ==  // by postcondition of MergeSortAux
      multiset(a[0..a.Length]);
    ==  { assert a[..] == a[0..a.Length]; }
      multiset(a[..]);
    }
  }

  datatype ResultPlacement = InSource | InDestination | Either

  method MergeSortAux(src: array<A.T>, dst: array<A.T>, lo: nat, hi: nat, where: ResultPlacement) returns (resultInSrc: bool)
    requires lo < hi <= src.Length && hi <= dst.Length && src != dst
    modifies src, dst
    ensures where == InSource ==> resultInSrc
    ensures where == InDestination ==> !resultInSrc
    ensures src[..lo] == old(src[..lo]) && src[hi..] == old(src[hi..])
    ensures dst[..lo] == old(dst[..lo]) && dst[hi..] == old(dst[hi..])
    ensures resultInSrc ==> IsSorted(src, lo, hi) && multiset(src[lo..hi]) == multiset(old(src[lo..hi]))
    ensures !resultInSrc ==> IsSorted(dst, lo, hi) && multiset(dst[lo..hi]) == multiset(old(src[lo..hi]))
    decreases hi - lo
  {
    if hi - lo == 1 {
      if where == InDestination {
        dst[lo] := src[lo];
        return false;
      } else {
        return true;
      }
    }

    ghost var oldElements := multiset(src[lo..hi]);
    var mid := (lo + hi) / 2;
    var aInSrc := MergeSortAux(src, dst, lo, mid, Either);
    assert src[mid..hi] == old(src[mid..hi]);
    ghost var bInSrc := MergeSortAux(src, dst, mid, hi, if aInSrc then InSource else InDestination);
    assert aInSrc == bInSrc;

    ghost var w := if aInSrc then src else dst;
    calc {
      multiset(w[lo..hi]);
    ==  { assert w[lo..hi] == w[lo..mid] + w[mid..hi]; }
      multiset(w[lo..mid] + w[mid..hi]);
    ==
      multiset(old(src[lo..mid] + src[mid..hi]));
    ==  { assert old(src[lo..hi] == src[lo..mid] + src[mid..hi]); }
      oldElements;
    }

    var mergedResult;
    if aInSrc {
      Merge(src, dst, lo, mid, hi);
      resultInSrc, mergedResult := false, dst[lo..hi];
    } else {
      Merge(dst, src, lo, mid, hi);
      resultInSrc, mergedResult := true, src[lo..hi];
    }
    if resultInSrc && where == InDestination {
      forall i | lo <= i < hi {
        dst[i] := src[i];
      }
      assert dst[lo..hi] == mergedResult;
      return false;
    }
    if !resultInSrc && where == InSource {
      forall i | lo <= i < hi {
        src[i] := dst[i];
      }
      assert src[lo..hi] == mergedResult;
      return true;
    }
  }

  method Merge(src: array<A.T>, dst: array<A.T>, lo: nat, mid: nat, hi: nat)
    requires lo <= mid <= hi <= src.Length && hi <= dst.Length && src != dst
    requires IsSorted(src, lo, mid) && IsSorted(src, mid, hi)
    modifies dst
    ensures dst[..lo] == old(dst[..lo]) && dst[hi..] == old(dst[hi..])
    ensures IsSorted(dst, lo, hi) && multiset(dst[lo..hi]) == multiset(old(src[lo..hi]))
  {
    var i, j, k := lo, mid, lo;
    while k < hi
      invariant lo <= i <= mid <= j <= hi
      invariant i - lo + j - mid == k - lo
      invariant dst[..lo] == old(dst[..lo]) && dst[hi..] == old(dst[hi..])
      invariant Below(dst[lo..k], src[i..mid]) && Below(dst[lo..k], src[j..hi])
      invariant IsSorted(dst, lo, k)
      invariant multiset(dst[lo..k]) == multiset(src[lo..i]) + multiset(src[mid..j])
    {
      forall a,b | A.Leq(a,b) && A.Leq(b,a)
      {
        A.Antisymmetry(a,b);
      }

      forall a,b,c | A.Leq(a,b) && A.Leq(b,c)
      {
        A.Transitivity(a,b,c);
      }

      forall a,b
      ensures A.Leq(a,b) || A.Leq(b,a)
      {
        A.Totality(a,b);
      }

      if i == mid || (j < hi && A.Leq(src[j], src[i])) {
        dst[k] := src[j];
        j, k := j + 1, k + 1;
      } else {
        dst[k] := src[i];
        i, k := i + 1, k + 1;
      }
    }
    assert old(src[lo..hi]) == src[lo..hi] == src[lo..mid] + src[mid..hi];
  }

  predicate Below(a: seq<A.T>, b: seq<A.T>) {
    forall i, j :: 0 <= i < |a| && 0 <= j < |b| ==> A.Leq(a[i], b[j])
  }
}