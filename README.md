# BoogieV
BoogieV is a prototype of a core subset of the [Boogie verifier](https://github.com/boogie-org/Boogie) 
implemented in the Dafny language. The goal is to prove different parts of BoogieV
correct in Dafny. The prototype is under development.

## Folder structure
* `lang`: Contains the formalization of the BoogieV language including its semantics 
(BoogieSemantics.dfy), which is expressed as a weakest precondition semantics.
Formalizations for both the BoogieV abstract syntax tree and BoogieV CFG are
included.
* `transformations`: Contains the implementation of the BoogieV verifier translation,
which is implemented as a series of BoogieV program transformations until a verification
condition is generated.
Proofs (currently still being developed) for some of the transformations
are also in this folder.
* `util`: Contains helper lemmas and definitions.
* `smt_interface`: Contains the SMT solver interface expressed as an extern Dafny class
and also the C# implementation of the C# Dafny class.

## Using the tool
### Dependencies
To use the tool, you need:
* [Dafny](https://github.com/dafny-lang/dafny) on the command line
* .NET core 6
* A [Z3](https://github.com/Z3Prover/z3) binary (we have tested BoogieV on version 4.8.5)

### Verify, compile, run
The `Makefile` contains useful commands to verify and compile `BoogieV`:
* `make verify`: Verifies the existing proofs.
* `make compile`: Compiles the BoogieV implementation into the C# dll `BoogieV.dll`,
which is stored in `smt_interface/csharp_smt_interface/bin/Debug/net6.0`.
* `make` has the same effect as running `make verify` followed by `make compile`.

To run `BoogieV`, first run `make compile`, which generates `BoogieV.dll` at the 
path specified above. Run the dll as follows: 

`dotnet path/BoogieV.dll [path_to_z3] [vc_output_file]`

where `path_to_z3` is the path to the Z3 executable and `vc_output_file` is 
the file in which the SMTLIB file that is given to Z3 is stored.

We do not have a BoogieV parser yet (we are working on it). So, running the above
command runs BoogieV on the hardcoded program in the Dafny `AllTransformations`
method in the file `transformations/AllTransformations.dfy`. So, if you want to 
run it on a different program, you need to changed that program and recompile
BoogieV.

The output after running BoogieV includes many of the intermediate programs
obtained via BoogieV's transformations followed by the VC (which is represented
as a Boolean BoogieV expression). The SMTLIB representation of the VC is stored 
at the input file path given to BoogieV.