using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie;
using Microsoft.Boogie.SMTLib;
using Dafny;

namespace SMTInterface_Compile
{
    public class VCExprInterface
    {
        private VCExpressionGenerator exprGen;
        private String proverPath;
        private String logPath;

        ProverFactory proverFactory = ProverFactory.Load("SMTLib");

        /* keep a map from strings to var objects to make sure that we can return
        the same object for the same name (on the Dafny side variables are different
        iff their names are different) */
        private IDictionary<string, VCExprVar> nameToVar = new Dictionary<string, VCExprVar>();

        public VCExprInterface(VCExpressionGenerator exprGen, String proverPath, String logPath)
        {
            this.exprGen = exprGen;
            this.proverPath = proverPath;
            this.logPath = logPath;
        }
        
        public static VCExprInterface Create(String proverPath, String logPath)
        {
          var exprGen = new VCExpressionGenerator();
          return new VCExprInterface(exprGen, proverPath, logPath);
        }

        private async Task<ProverInterface.Outcome> InvokeProver(ProverInterface proverInterface, VCExpr vc, ProverInterface.ErrorHandler errorHandler, int errorLimit)
        {
          var proverOutcomeTask = 
            proverInterface.Check(
              "vc_query",
              vc,
              errorHandler,
              errorLimit,
              CancellationToken.None
            );

          var outcome = await proverOutcomeTask;
          return outcome;
        }

        public bool IsVCValid(VCExpr vc)
        {
          var options = CommandLineOptions.FromArguments();
          options.SIBoolControlVC = true;
          var proverOptions = (SMTLibSolverOptions) proverFactory.BlankProverOptions(options);
          proverOptions.Parse(new List<string> { 
            "PROVER_PATH="+proverPath,
            "LOG_FILE="+logPath
            });
          var proverContext = proverFactory.NewProverContext(proverOptions);
          ProverInterface proverInterface = 
            proverFactory.SpawnProver(
              options, 
              proverOptions, 
              proverContext
            );
          
          var proverOutcome = 
            InvokeProver(
              proverInterface,
              vc,
              new ProverInterface.ErrorHandler(options),
              options.ErrorLimit
            ).Result;

          //TODO give information on other outcomes
          return proverOutcome == ProverInterface.Outcome.Valid;
        }

        public VCExpr VCIntVar(Dafny.ISequence<char> x) 
        {
            string xS = x.ToString();
            if(!nameToVar.TryGetValue(xS, out var res)) {
                var intType = Microsoft.Boogie.Type.Int;
                res = exprGen.Variable(xS, intType);
                nameToVar.Add(xS, res);
            }

            return res;
        }

        public VCExpr VCBoolVar(Dafny.ISequence<char> x) 
        {
            string xS = x.ToString();
            if(!nameToVar.TryGetValue(xS, out var res)) {
                var intType = Microsoft.Boogie.Type.Bool;
                res = exprGen.Variable(xS, intType);
                nameToVar.Add(xS, res);
            }

            return res;
        }

        //TODO: change to BigInteger
        public VCExpr VCLitInt(int i) 
        {
            return exprGen.Integer(Microsoft.BaseTypes.BigNum.FromInt(i));
        }

        public VCExpr VCLitBool(bool b) 
        {
            if(b) {
                return VCExpressionGenerator.True;
            } else {
                return VCExpressionGenerator.False;
            }
        }

        public VCExpr VCEq(VCExpr e1, VCExpr e2)
        {
          return exprGen.Function(VCExpressionGenerator.EqOp, e1, e2);
        }

        public VCExpr VCNeq(VCExpr e1, VCExpr e2)
        {
          return exprGen.Function(VCExpressionGenerator.NeqOp, e1, e2);
        }

        public VCExpr VCAdd(VCExpr e1, VCExpr e2)
        {
          return exprGen.Function(VCExpressionGenerator.AddIOp, e1, e2);
        }

        public VCExpr VCSub(VCExpr e1, VCExpr e2)
        {
          return exprGen.Function(VCExpressionGenerator.SubIOp, e1, e2);
        }

        public VCExpr VCMul(VCExpr e1, VCExpr e2)
        {
          return exprGen.Function(VCExpressionGenerator.MulIOp, e1, e2);
        }

        public VCExpr VCDiv(VCExpr e1, VCExpr e2)
        {
          return exprGen.Function(VCExpressionGenerator.DivIOp, e1, e2);
        }

        public VCExpr VCMod(VCExpr e1, VCExpr e2)
        {
          return exprGen.Function(VCExpressionGenerator.ModOp, e1, e2);
        }

        public VCExpr VCLt(VCExpr e1, VCExpr e2)
        {
          return exprGen.Function(VCExpressionGenerator.LtOp, e1, e2);
        }

        public VCExpr VCLe(VCExpr e1, VCExpr e2)
        {
          return exprGen.Function(VCExpressionGenerator.LeOp, e1, e2);
        }

        public VCExpr VCGt(VCExpr e1, VCExpr e2)
        {
          return exprGen.Function(VCExpressionGenerator.GtOp, e1, e2);
        }

        public VCExpr VCGe(VCExpr e1, VCExpr e2)
        {
          return exprGen.Function(VCExpressionGenerator.GeOp, e1, e2);
        }

        public VCExpr VCAnd(VCExpr e1, VCExpr e2)
        {
          return exprGen.Function(VCExpressionGenerator.AndOp, e1, e2);
        }

        public VCExpr VCOr(VCExpr e1, VCExpr e2)
        {
          return exprGen.Function(VCExpressionGenerator.OrOp, e1, e2);
        }

        public VCExpr VCImp(VCExpr e1, VCExpr e2)
        {
          return exprGen.Function(VCExpressionGenerator.ImpliesOp, e1, e2);
        }
        
        public VCExpr VCIff(VCExpr e1, VCExpr e2)
        {
          //same as Eq (also the case in the Boogie 2 implementation at this point)
          return exprGen.Function(VCExpressionGenerator.EqOp, e1, e2);
        }

        public VCExpr VCNot(VCExpr e)
        {
            return exprGen.Function(VCExpressionGenerator.NotOp, e);
        }

        public VCExpr VCUMinus(VCExpr e)
        {
          //there is no unary minus in VCExpr --> Boogie 2 does the same encoding
          return exprGen.Function(VCExpressionGenerator.SubIOp, exprGen.Integer(Microsoft.BaseTypes.BigNum.ZERO), e);
        }

        public VCExpr VCLet(Dafny.ISequence<char> varName, VCExpr binding, VCExpr body)
        {
          throw new NotImplementedException();
        }

    }

    class MainClass {
      static void Main(String [] args) {
        if(args.Length < 2) {
          Console.WriteLine("Not enough arguments (need at least two)");
          return;
        }

        var vcExprGen = new VCExpressionGenerator();
        var exprInterface = new VCExprInterface(vcExprGen, args[0], args[1]);

        var x = vcExprGen.Variable("test", Microsoft.Boogie.Type.Int);

        var vc = 
          vcExprGen.Implies(vcExprGen.Gt(x, exprInterface.VCLitInt(4)), vcExprGen.Gt(x, exprInterface.VCLitInt(2)));

        var isVCValid = exprInterface.IsVCValid(vc);
        if(isVCValid) {
          Console.Out.WriteLine("Input program is correct.");
        } else {
          Console.Out.WriteLine("Input program might not be correct.");
        }
      }
    }
}
