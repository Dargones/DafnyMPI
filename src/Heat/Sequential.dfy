include "../DafnyMPI/Externs/MPIResource.dfy"
include "../DafnyMPI/Externs/ExternUtils.dfy"
include "SequentialBackend.dfy"

module Sequential {

  import opened MPIResource
  import opened SequentialBackend
  import opened ExternUtils
  import opened Std.Strings

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

    if (length <= 8) {
      print("Error: unsupported domain size.\n");
      print("Requiremenent: length > 8.\n");
      return;
    }

    var dx := (1 as real)/((length - 8) as real);
    reveal ArrayOfReals2D.FreeToWriteStatic;
    reveal ArrayOfReals2D.FreeToReadStatic;

    var u := Sequential((length - 8), (length - 8), iterations, length, 
                        length, dx, 0.25 * dx * dx);
    if plot {
      Plot2D(u, "Heat_Sequential_" + 
                  OfNat(iterations) + "Iterations_" + 
                  OfNat(length) + "DomainSize.pdf", 
                0.0, 1.0, 0.0, 1.0, 0.0, 1.0, "x", "y");
    }
  }
}