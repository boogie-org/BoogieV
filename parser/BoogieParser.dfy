include "dafny-libraries/src/Wrappers.dfy"
include "BoogieLang.dfy"
 
module Environment {
  method {:extern "Shims", "GetCommandLineArguments"} GetCommandLineArguments() returns (args: seq<string>)
}
 
module IO {
  import opened Wrappers
 
  method {:extern "Shims", "ReadAllLinesFromStdin"}
    ReadAllLinesFromStdin() returns (r: Result<seq<string>, string>)
 
  method {:extern "Shims", "ReadAllLinesFromFile"}
    ReadAllLinesFromFile(filename: string) returns (r: Result<seq<string>, string>)
}
 
module Tokenizer {
  //Tokenizer adapted from Stefan Zetzsche

  import opened Wrappers
  import BoogieLang
 
  export
    reveals Tokenizer
    reveals Token, Keyword, ParseOperation
    provides Tokenizer.input, Tokenizer.pos
    provides Tokenizer.Valid, Tokenizer.AtEof 
    provides Tokenizer.GetToken, Tokenizer.TryGetToken, Tokenizer.TryGetTokenDefaultMsg
    provides Tokenizer.ExpectIdentifier, Tokenizer.ExpectSeparator, Tokenizer.ExpectKeyword
    provides Keyword.ToString
    provides Wrappers
    provides BoogieLang

  datatype Keyword =
  | OldKw
  | AssertKw
  | AssumeKw
  | HavocKw
  | ScopeKw
  | IfKw
  | ElseKw
  | LoopKw
  | InvariantKw
  | BreakKw
  {
    function method ToString() : string {
      match this
      case OldKw => "old"
      case AssertKw => "assert"
      case AssumeKw => "assume"
      case HavocKw => "havoc"
      case ScopeKw => "scope"
      case IfKw => "if"
      case ElseKw => "else"
      case LoopKw => "loop"
      case InvariantKw => "invariant"
      case BreakKw => "break"
    }
  }

  datatype ParseOperation = 
  | ParseUnop (uop: BoogieLang.Unop)
  | ParseBinop (bop: BoogieLang.Binop)
  | ParseAssignmentOp

  datatype Token = 
  | Identifier(s: string) 
  | IntToken(i: int) 
  | BoolToken(b: bool) 
  | Separator(sep: char)
  | KeywordToken(kw: Keyword)
  | ParseOp(op: ParseOperation)
 
  class Tokenizer {
    const input: string
    var pos: nat
    // line, col aren't used, but could be used for error messages
    var line: nat
    var col: nat
 
    predicate Valid()
      reads this
      ensures Valid() ==> 0 <= pos <= |input|
    {
      AlmostValid() && (pos == |input| || !IsWhitespace(input[pos]))
    }
 
    predicate AlmostValid()
      reads this
    {
      0 <= pos <= |input|
    }
 
    constructor (input: seq<string>)
      ensures Valid()
    {
      var inp := "";
      for i := 0 to |input| {
        inp := inp + input[i] + "\n";
      }
      this.input := inp;
      pos, line, col := 0, 0, 0;
      new;
      SkipWhitespace();
    }
 
    static predicate method IsWhitespace(ch: char) {
      ch == ' ' || ch == '\t' || ch == '\n'
    }

    static predicate method IsSeparator(ch: char) {
      ch == ';' || ch == ',' || ch == '{' || ch == '}' || ch == '(' || ch == ')'
    }
 
    method SkipWhitespace()
      requires AlmostValid()
      modifies this
      ensures Valid() && old(pos) <= pos
    {
      while pos < |input| && IsWhitespace(input[pos])
        invariant AlmostValid()
      {
        if input[pos] == '\n' {
          line, col := line + 1, 0;
        } else {
          col := col + 1;
        }
        pos := pos + 1;
      }
    }
 
    predicate method AtEof()
      requires Valid()
      reads this
    {
      pos == |input|
    }

    /** 
      * Gets all the characters from the current position until the 
        next whitespace or special character (if the current position is a 
        special character, then only that character is returned). 
        The current position is advanced. */
    method GetToken() returns (t: Token)
      requires Valid() && !AtEof()
      modifies this
      ensures Valid() && old(pos) < pos
    {
      var start := pos;

      if(IsSeparator(input[start])) {
        t := Separator(input[start]);
        pos, col := pos + 1, col +1;
        SkipWhitespace();
        return t;
      }

      var s := "";

      while pos < |input| && !IsWhitespace(input[pos]) && !IsSeparator(input[pos])
        invariant AlmostValid() && old(pos) <= pos
        invariant old(pos) == pos ==> !IsWhitespace(input[pos])
      {
        pos, col := pos + 1, col + 1;
      }
      s := input[start..pos];
      SkipWhitespace();

      t := ConvertWordToToken(s);
    }

    method TryGetTokenDefaultMsg() returns (r: Result<Token, string>)
      requires Valid()
      modifies this 
      ensures Valid() && (r.Success? ==> old(pos) < pos)
    {
      r := TryGetToken("Reached end of file unexpectedly");
    }

    method TryGetToken(errorMessage: string) returns (r: Result<Token, string>)
      requires Valid()
      modifies this 
      ensures Valid() && (r.Success? ==> old(pos) < pos)
    {
      if AtEof() {
        return Failure(errorMessage);
      }

      var tok := GetToken();

      return Success(tok);
    }

    method ConvertWordToToken(s: string) returns (t: Token)
    {
        if |s| == 1 && IsSeparator(s[0]) {
          return Separator(s[0]);
        } 

        /** TODO: maybe convert to if-elseif statement and instead use ToString() */
        match s {
          case "old" => return KeywordToken(OldKw);
          case "assert" => return KeywordToken(AssertKw);
          case "assume" => return KeywordToken(AssumeKw);
          case "havoc" => return KeywordToken(HavocKw);
          case "scope" => return KeywordToken(ScopeKw);
          case "loop" => return KeywordToken(LoopKw);
          case "invariant" => return KeywordToken(InvariantKw);
          case "if" => return KeywordToken(IfKw);
          case "else" => return KeywordToken(ElseKw);
          case "break" => return KeywordToken(BreakKw);
          case _ => 
        }

        match s {
          case ":=" => return ParseOp(ParseAssignmentOp);
          case "!" => return ParseOp(ParseUnop(BoogieLang.Not));
          case "<" => return ParseOp(ParseBinop(BoogieLang.Lt));
          case "<=" => return ParseOp(ParseBinop(BoogieLang.Le));
          case ">" => return ParseOp(ParseBinop(BoogieLang.Gt));
          case ">=" => return ParseOp(ParseBinop(BoogieLang.Ge));
          case "==" => return ParseOp(ParseBinop(BoogieLang.Eq));
          case "!=" => return ParseOp(ParseBinop(BoogieLang.Neq));
          case "&&" => return ParseOp(ParseBinop(BoogieLang.And));
          case "||" => return ParseOp(ParseBinop(BoogieLang.Or));
          case "==>" => return ParseOp(ParseBinop(BoogieLang.Imp));
          case "<==>" => return ParseOp(ParseBinop(BoogieLang.Iff));
          case "+" => return ParseOp(ParseBinop(BoogieLang.Add));
          case "-" => return ParseOp(ParseBinop(BoogieLang.Sub));
          case "*" => return ParseOp(ParseBinop(BoogieLang.Mul));
          case "/" => return ParseOp(ParseBinop(BoogieLang.Div));
          case "%" => return ParseOp(ParseBinop(BoogieLang.Mod));
          case _ =>
        }
        
        var optionNum := ConvertWordToNumber(s);
        if(optionNum.Some?) {
          return IntToken(optionNum.value);
        }

        var optionBool := ConvertWordToBoolean(s);
        if(optionBool.Some?) {
          return BoolToken(optionBool.value);
        }

        return Identifier(s);
    }

    method ConvertWordToNumber(s: string) returns (r: Option<nat>)
    {
      var n: nat := 0;
      for i := 0 to |s| {
        if '0' <= s[i] <= '9' {
          n := 10 * n + (s[i] - '0') as nat;
        } else {
          return None;
        }
      }
      return Some(n);
    }

    function method ConvertWordToBoolean(s: string) : Option<bool>
    {
      if s == "true" then
        Some(true)
      else if s == "false" then
        Some(false)
      else
        None
    }

    method ExpectIdentifier() returns (r: Result<string, string>)
      requires Valid()
      modifies this
      ensures Valid()
      ensures r.Success? ==> old(pos) < pos
    {
      if AtEof() {
        return Failure("expected identifier, reached EOF");
      }
      
      var nextToken := GetToken();

      match nextToken {
        case Identifier(id) => return Success(id);
        case _ => return Failure("expected identifier");
      }
    }

    method ExpectSeparator(expectedChar: char) returns (r: Result<char, string>)
      requires Valid()
      modifies this
      ensures Valid()
      ensures r.Success? ==> old(pos) < pos
    {
      var errorMsgPrefix := "expected separator [" + [expectedChar] + "]";

      if AtEof() {
        return Failure(errorMsgPrefix+" , reached EOF");
      }
      
      var nextToken :- TryGetTokenDefaultMsg();

      if nextToken == Separator(expectedChar) {
        return Success(expectedChar);
      } else {
        return Failure("expected separator [" + [expectedChar] + "]");
      }
    }

    method ExpectKeyword(expectedKw: Keyword) returns (r: Result<Keyword, string>)
      requires Valid()
      modifies this
      ensures Valid()
      ensures r.Success? ==> old(pos) < pos
    {
      var errorMsgPrefix := "Expected keyword " + expectedKw.ToString();
      var nextToken :- TryGetToken(errorMsgPrefix + ", reached EOF");

      match nextToken {
        case KeywordToken(expectedKw) => return Success(expectedKw);
        case _ => return Failure(errorMsgPrefix);
      }
    }


  }
}

module BoogieParser {
  import opened Wrappers
  import opened BoogieLang
  import opened Tokenizer

  export
    provides Parse
    provides Wrappers
    provides BoogieLang

  method ParseExpr(tokenizer: Tokenizer.Tokenizer) returns (r: Result<Expr, string>)
    requires tokenizer.Valid();
    ensures tokenizer.Valid();
    ensures r.Success? ==> old(tokenizer.pos) < tokenizer.pos;
    modifies tokenizer
    decreases |tokenizer.input| - tokenizer.pos
  {
    var nextToken :- tokenizer.TryGetTokenDefaultMsg();

    match nextToken 
    case Identifier(s) => return Success(Var(s));
    case IntToken(i) => return Success(ELit(LitInt(i)));
    case BoolToken(b) => return Success(ELit(LitBool(b)));
    case KeywordToken(OldKw) => 
      var oldSubExpr :- ParseExpr(tokenizer);
      return Success(Old(oldSubExpr));
    case Separator(sep) =>
      if(sep != '(') {
        return Failure("Unexpected separator [" + [sep] + "] while parsing expression");
      }

      //multiple choices here. For  simplicity, we force it to a binary operation) 
      var e1 :- ParseExpr(tokenizer);

      var bop :- tokenizer.TryGetTokenDefaultMsg();

      match bop {
        case ParseOp(ParseBinop(bop)) => 
          var e2 :- ParseExpr(tokenizer);

          var tok :- tokenizer.TryGetTokenDefaultMsg();

          if tok == Separator(')') {
            return Success(BinOp(e1, bop, e2));
          } else {
            return Failure("error");
          }
        case _ => return Failure("Expected binary operator");
      }
    case _ => return Failure("Could not parse expression");
  }

  function method AppendCmd(prev: Option<Cmd>, next:Cmd): Cmd {
    match prev 
    case Some(c) => Seq(c, next)
    case None => next
  }

  method Parse(input: seq<string>) returns (r: Result<Cmd, string>)
  {
    var tokenizer := new Tokenizer.Tokenizer(input);
    r := ParseCmd(tokenizer);
  }

  /** Parses a list of commands that must be enclosed within matching curly brackets
   */
  method ParseCmd(tokenizer: Tokenizer.Tokenizer) returns (r: Result<Cmd, string>)
    requires tokenizer.Valid()
    ensures tokenizer.Valid()
    ensures r.Success? ==> old(tokenizer.pos) < tokenizer.pos;
    modifies tokenizer
    decreases |tokenizer.input| - tokenizer.pos
  {
    var cmds: seq<Cmd> := [];

    var openingBrace :- tokenizer.ExpectSeparator('{');
    var foundClosingBrace := false;

    while !tokenizer.AtEof()
      invariant tokenizer.Valid()
      invariant cmds != [] ==> old(tokenizer.pos) < tokenizer.pos
      //invariant forall instr :: instr in instructions ==> instr.Valid(qbits)
      decreases |tokenizer.input| - tokenizer.pos
    {
      var tok := tokenizer.GetToken();

      if(tok == Separator('}')) {
        foundClosingBrace := true;
        break;
      }

      var cmd: Cmd;
      match tok {
        case KeywordToken(kw) =>
          match kw {
            case AssertKw =>
              var exprResult :- ParseExpr(tokenizer);
              var _ :- tokenizer.ExpectSeparator(';');
              cmd := Assert(exprResult);
            case AssumeKw =>
              var exprResult :- ParseExpr(tokenizer);
              var _ :- tokenizer.ExpectSeparator(';');
              cmd := Assume(exprResult);
            case HavocKw =>
              var varName :- tokenizer.ExpectIdentifier();
              var _ :- tokenizer.ExpectSeparator(';');
              cmd := Havoc([(varName, TPrim(TInt))]); //TODO: find type of variable, sequence of variables
            case BreakKw =>
              var scopeName :- tokenizer.ExpectIdentifier(); //TODO allow not providing scope name
              var _ :- tokenizer.ExpectSeparator(';');
              cmd := Break(Some(scopeName));
            case ScopeKw =>
              //TODO allow not providing scope name
              var scopeName :- tokenizer.ExpectIdentifier();
              var body :- ParseCmd(tokenizer);
              cmd := Scope(Some(scopeName), [], body); //TODO allow variable declarations
            case LoopKw =>
              var r :- tokenizer.ExpectKeyword(InvariantKw); //TODO multiple invariants
              var inv :- ParseExpr(tokenizer); 
              var loopBody :- ParseCmd(tokenizer);
              cmd := Loop([inv], loopBody);
            case IfKw =>
              var _ :- tokenizer.ExpectSeparator('(');
              var cond :- ParseExpr(tokenizer); //TODO allow nondeterministic branching
              var _ :- tokenizer.ExpectSeparator(')');

              var thenBranch :- ParseCmd(tokenizer);

              var _ :- tokenizer.ExpectKeyword(ElseKw); //TODO allow not providing else branch

              var elseBranch :- ParseCmd(tokenizer);

              cmd := If(Some(cond), thenBranch, elseBranch);
            case _ => return Failure("Unexpectedly parsed keyword " + tok.kw.ToString());
          }
        case Identifier(lhsVar) => 
          //assignment
          var assignOp :- tokenizer.TryGetTokenDefaultMsg();
          if(assignOp != ParseOp(ParseAssignmentOp)) {
            return Failure("Expected assignment operator [:=]");
          }

          var expr :- ParseExpr(tokenizer);

          var _ :- tokenizer.ExpectSeparator(';');

          return Success(Assign(lhsVar, TPrim(TInt), expr));

        case _ => return Failure("Could not parse command");

      }

      cmds := cmds + [cmd];
    }
    
    if !foundClosingBrace {
      return Failure("Could not find [}] to indicate end of commands.");
    } 

    if(cmds == []) {
      return Success(Skip);
    } else {
      return Success(SeqToCmd(cmds));
    }

  }
}

method Main()
{
  var args := Environment.GetCommandLineArguments();
  var r0;
  if |args| == 0 {
    r0 := IO.ReadAllLinesFromStdin();
  } else {
    r0 := IO.ReadAllLinesFromFile(args[0]);
  }
  if r0.Failure? {
    print "Error obtaining input: ", r0.error, "\n";
    return;
  }
  var input := r0.Extract();
 
  // Parse the program from the input that was read
  var r1 := BoogieParser.Parse(input);
  if r1.Failure? {
    print "Error parsing input: ", r1.error, "\n";
    return;
  } else {
    print "Success \n"; //placeholder
  }
  var program := r1.Extract();

  var programString := program.ToString(0);

  print(programString);
}