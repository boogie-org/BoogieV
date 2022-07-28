# Formalization of BoogieV

## Most important files
* `BoogieLang.dfy`: AST for BoogieV (expressions, commands)
* `BoogieSemantics.dfy`: Semantics for BoogieV using weakest preconditions
* `Cfg.dfy`: Representation for control-flow graphs (CFGs) and a semantics for acyclic
CFGs based on weakest preconditions

## Boogie semantics 
The Boogie semantics is defined via the `WpCmd` function in `BoogieSemantics.dfy`
that defines the weakest precondition for commands, which relies on the 
evaluation of expressions `EvalExpr` function.

Correctness of a Boogie command is expressed in `CmdIsCorrect` in `BoogieSemantics.dfy`,
which essentially states that the weakest precondition must be true in all 
states. Note that once one adds procedures, then one will want a weaker version
that requires the weakest precondition to be true in just those states whose domains
include the parameters of the procedure and the corresponding mapped values
contain the specified types.