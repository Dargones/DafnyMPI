include "../DafnyMPI/Externs/MPIResource.dfy"
include "../DafnyMPI/Externs/ExternUtils.dfy"
include "SequentialBackend.dfy"
include "Shared.dfy"

module Sequential {

  import opened MPIResource
  import opened SequentialBackend
  import opened ExternUtils
  import opened Std.Strings
  import Shared

  method Main(args:seq<string>) {

    if |args| < 4 
      || !(forall c <- args[1] :: DecimalConversion.IsDigitChar(c)) 
      || !(forall c <- args[2] :: DecimalConversion.IsDigitChar(c)) 
      || (args[3] != "true" && args[3] != "false") {
        print("Error: invalid arguments:");
        print("Usage: python __main__.py length iters toPlot\n");
        return;
    }

    var length := ToNat(args[1]);
    var iterations := ToNat(args[2]);
    var plot := args[3] == "true";

    if (length < 3) {
      print("Error: unsupported domain size.\n");
      print("Requiremenent: length >= 3.\n");
      return;
    }

    var rhs := (x:int, y:int) => Shared.Rhs(x-1, y-1, length-2);

    reveal ArrayOfReals2D.FreeToWriteStatic;
    reveal ArrayOfReals2D.FreeToReadStatic;

    var u, converged := Sequential(length, iterations, 0.000001, rhs);
    if (!converged) {
      print("Did not converge!");
    }
    if plot {
      Plot2DV2(u, "Poisson_Sequential_" + 
                  OfNat(iterations) + "Iterations_" + 
                  OfNat(length) + "DomainSize.pdf", 
                0.0, 1.0, 0.0, 1.0, "x", "y");
    }
  }
}