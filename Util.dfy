module Util {
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

  function method BoolToString(b: bool) : string {
    if b then "true" else "false"
  }

  function method IndentString(s: string, n: nat) : string {
    seq(n, _ => ' ') + s
  }
}