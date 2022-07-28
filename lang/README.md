# Formalization of BoogieV

## Most important files
* `BoogieLang.dfy`: AST for BoogieV (expressions, commands)
* `BoogieSemantics.dfy`: Semantics for BoogieV using weakest preconditions
* `Cfg.dfy`: Representation for control-flow graphs (CFGs) and a semantics for acyclic
CFGs based on weakest preconditions

## Boogie semantics main definitions
The Boogie semantics is defined via the `WpCmd` function in `BoogieSemantics.dfy`
that defines the weakest precondition for commands, which relies on the 
evaluation of expressions `EvalExpr` function.