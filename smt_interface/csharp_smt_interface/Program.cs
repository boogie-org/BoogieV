using Microsoft.Boogie.VCExprAST;
using Microsoft.Boogie;

namespace SMTInterface
{
    class VCExprInterface
    {
        private VCExpressionGenerator exprGen;

        ProverFactory proverFactory = ProverFactory.Load("SMTLib");

        /* keep a map from strings to var objects to make sure that we can return
        the same object for the same name (on the Dafny side variables are different
        iff their names are different) */
        private IDictionary<string, VCExprVar> nameToVar = new Dictionary<string, VCExprVar>();

        public VCExprInterface(VCExpressionGenerator exprGen)
        {
            this.exprGen = exprGen;
        }

        public bool IsVCValid(VCExpr vc)
        {
          var options = CommandLineOptions.FromArguments();
          var proverOptions = proverFactory.BlankProverOptions(options);
          var proverContext = proverFactory.NewProverContext(proverOptions);
          ProverInterface proverInterface = 
            proverFactory.SpawnProver(
              options, 
              proverOptions, 
              proverContext
            );
          
          var proverOutcomeTask = 
            proverInterface.Check(
              "vc_query",
              vc,
              new ProverInterface.ErrorHandler(options),
              options.ErrorLimit,
              CancellationToken.None
            );

          //TODO: should do something with async
          proverOutcomeTask.Wait();
          if(proverOutcomeTask.IsCompleted) {
              //TODO give information on other outcomes
              ProverInterface.Outcome proverOutcome = proverOutcomeTask.Result;
              return proverOutcome == ProverInterface.Outcome.Valid;
          } else {
            return false;
          }
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
    }
}
