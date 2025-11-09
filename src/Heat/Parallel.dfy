include "../DafnyMPI/Externs/MPIResource.dfy"
include "../DafnyMPI/Externs/MPI.dfy"
include "../DafnyMPI/Externs/ExternUtils.dfy"
include "ParallelBackend.dfy"

module Parallel {

  import opened MPIResource
  import opened ParallelBackend
  import opened ExternUtils
  import opened Std.Strings
  import opened MPI

  method Main(args:seq<string>) {

    if |args| < 4 
      || !(forall c <- args[1] :: DecimalConversion.IsDigitChar(c)) 
      || !(forall c <- args[2] :: DecimalConversion.IsDigitChar(c)) 
      || (args[3] != "true" && args[3] != "false") {
        print("Error: invalid arguments:");
        print("Usage: mpiexec -n N python __main__.py length iters toPlot\n");
        return;
    }

    var length := ToNat(args[1]);
    var iterations := ToNat(args[2]);
    var plot := args[3] == "true";

    var size := GetMPISize();
    if ((size >= 32767 / 2) 
     || (size < 2) 
     || (length <= 8)
     || (length - 8) % size != 0 
     || (length - 8) / size < 4) {
      print("Error: unsupported combination of domain size and # of procs.\n");
      print("Requirements (length = domain size):\n");
      print("\t(length - 8) % size == 0\n");
      print("\t(length - 8) / size >= 4\n");
      print("\tsize >= 2\n");
      print("\tsize < 32767 / 2\n");
      return;
    }
    var dx := (1 as real)/((length - 8) as real);
    reveal ArrayOfReals2D.FreeToWriteStatic;
    reveal ArrayOfReals2D.FreeToReadStatic;

    var u, world := Parallel((length - 8), (length - 8), iterations, length, 
                             length, dx, 0.25 * dx * dx, size);
    if (world.rank == 0 && plot) {
      Plot2D(u, "Heat_Parallel_" + 
                OfNat(iterations) + "Iterations_" + 
                OfNat(length) + "DomainSize_" + 
                OfNat(size)+ "Processes.pdf", 
              0.0, 1.0, 0.0, 1.0, 0.0, 1.0, "x", "y");
    }
  }
}