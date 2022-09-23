public class Shims {
  public static Dafny.ISequence<Dafny.ISequence<char>> GetCommandLineArguments() {
    string[] args = System.Environment.GetCommandLineArgs();

    // Convert the C# string[] to a Dafny seq<string>
    var n = args.Length - 1; // skip args[0], which is the name of the program
    var stringArray = new Dafny.ISequence<char>[n];
    for (var i = 0; i < n; i++) {
      // Convert the C# string to a Dafny string
      stringArray[i] = Dafny.Sequence<char>.FromString(args[i + 1]);
    }
    return Dafny.Sequence<Dafny.ISequence<char>>.FromArray(stringArray);
  }

  public static Wrappers_Compile._IResult<Dafny.ISequence<Dafny.ISequence<char>>, Dafny.ISequence<char>> ReadAllLinesFromStdin() {
    System.IO.StreamReader input = new System.IO.StreamReader(System.Console.OpenStandardInput(), false);
    return ReadAllLines(input);
  }

  public static Wrappers_Compile._IResult<Dafny.ISequence<Dafny.ISequence<char>>, Dafny.ISequence<char>> ReadAllLinesFromFile(Dafny.ISequence<char> filename) {
    System.IO.StreamReader input = new System.IO.StreamReader(filename.ToString());
    return ReadAllLines(input);
  }

  private static Wrappers_Compile._IResult<Dafny.ISequence<Dafny.ISequence<char>>, Dafny.ISequence<char>> ReadAllLines(System.IO.StreamReader input) {
    try {
      // Read all lines from the input until end-of-file
      var lines = new System.Collections.Generic.List<string>();
      while (true) {
        var line = input.ReadLine();
        if (line == null) {
          break;
        }
        lines.Add(line);
      }

      // Convert the C# List<string> to a Dafny seq<string>
      var stringArray = new Dafny.ISequence<char>[lines.Count];
      for (var i = 0; i < lines.Count; i++) {
        // Convert the C# string to a Dafny string
        stringArray[i] = Dafny.Sequence<char>.FromString(lines[i]);
      }
      var dafnyLines = Dafny.Sequence<Dafny.ISequence<char>>.FromArray(stringArray);

      // Return Success(dafnyLines)
      return Wrappers_Compile.Result<Dafny.ISequence<Dafny.ISequence<char>>, Dafny.ISequence<char>>.create_Success(dafnyLines);

    } catch (System.Exception e) {
      // Return Failure(errorString)
      Dafny.ISequence<char> errorString = Dafny.Sequence<char>.FromString(e.ToString());
      return Wrappers_Compile.Result<Dafny.ISequence<Dafny.ISequence<char>>, Dafny.ISequence<char>>.create_Failure(errorString);
    }
  }
}
