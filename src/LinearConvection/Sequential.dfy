include "../DafnyMPI/Externs/MPIResource.dfy"
include "../DafnyMPI/Externs/ExternUtils.dfy"
include "../DafnyMPI/Arrays1D.dfy"
include "Spec.dfy"

module Sequential {

  import opened MPIResource
  import opened Arrays1D
  import opened Spec
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

    if (length < 2) {
      print("Error: unsupported domain size.\n");
      print("Requirement: length >= 2.\n");
      return;
    }

    reveal ArrayOfReals.FreeToWriteStatic;
    reveal ArrayOfReals.FreeToReadStatic;

    var dx := 3.0 / (length as real);
    var u := Sequential(iterations, length, dx, 1.0, 0.00625, 0.5, 1.0, 2.0);
    if plot {
      Plot1D(u, "LC_Sequential_" + 
                  OfNat(iterations) + "Iterations_" + 
                  OfNat(length) + "DomainSize.pdf", 
                0.0, 2.0, 0.75, 2.25, "x", "u(x," + OfNat(iterations) + ")");
    }
  }

  method Sequential(
    nt:nat, nx:nat, dx:real, c:real, dt:real, 
    low:real, high:real, value:real) 
    returns (u:ArrayOfReals) 
    requires dx > 0.0
    requires low > 0.0
    requires (low/dx).Floor <= (high / dx + 1.0).Floor < nx
    ensures fresh(u)
    ensures u.Repr == Spec.Spec(nt, 
                                Spec.SpecInit(nx, dx, low, high, value), 
                                Spec.F(c, dt, dx))
    ensures u.IsValid()
    ensures u.FreeToRead(0, u.Length())
  {
    reveal ArrayOfReals.FreeToWriteStatic;
    reveal ArrayOfReals.FreeToReadStatic;
    var F := Spec.F(c, dt, dx);
    ghost var init := Spec.SpecInit(nx, dx, low, high, value);

    u := Ones(nx); 
    Arrays1D.SetRange(u, (low/dx).Floor, (high / dx + 1.0).Floor, value); 
    assert u.Repr == init by {
      reveal SpecInit;
    }

    var un := Ones(nx);
    
    assert u.Repr == SpecOuterHelper(nt, nt, init, F) by {
      reveal SpecOuterHelper;
    }
    for n := 0 to nt 
      invariant u.Length() == |init|
      invariant u.IsValid()
      invariant u.FreeToWrite(0, u.length)
      invariant u.Repr == SpecOuterHelper(nt - n, nt, init, F)
    {
      un := Copy(u);
      ghost var prev := u.Repr;
      assert u.Repr == SpecInnerHelper(1, 1, prev, prev, F) by {
        reveal SpecInnerHelper;
      }
      for i := 1 to nx
        invariant u.IsValid()
        invariant u.FreeToWrite(0, u.length)
        invariant un.IsValid()
        invariant un.FreeToRead(0, un.length)
        invariant un.Repr == prev
        invariant forall j :: 1 <= j < i ==> 
          u.Repr[j] == F(prev[j], prev[j - 1])
        invariant u.Repr[0] == prev[0]
      { 
        u.Set(i, F(un.Get(i), un.Get(i - 1)));
      }
      SpecInnerLemmaCorollary(1, nx, u.Repr, prev, F);
      reveal SpecOuterHelper;
    }
    reveal Spec.Spec();
  }
}