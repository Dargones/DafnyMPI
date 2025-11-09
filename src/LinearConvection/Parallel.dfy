include "../DafnyMPI/Externs/MPIResource.dfy"
include "../DafnyMPI/Externs/ExternUtils.dfy"
include "../DafnyMPI/Externs/MPI.dfy"
include "../DafnyMPI/Arrays1D.dfy"
include "Spec.dfy"

module Parallel {

  import opened MPIResource
  import opened ExternUtils
  import opened Arrays1D
  import opened MPI
  import opened Spec
  import opened Std.Arithmetic.DivMod
  import opened Std.Arithmetic.Mul
  import opened Std.Strings

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
    if || (32767 <= size)
       || (size <= 1)
       || (length % size != 0)
       || (length < 2) {
      print("Error: unsupported combination of domain size and # of procs.\n");
      print("Requirements (length = domain size):\n");
      print("\t1 < size < 32767\n");
      print("\tlength % size == 0\n");
      print("\tlength >= 2\n");
      return;
    }

    reveal ArrayOfReals.FreeToWriteStatic;
    reveal ArrayOfReals.FreeToReadStatic;

    var dx := 3.0 / (length as real);
    var u, world := Parallel(iterations, length, 
                             dx, 1.0, 0.00625, 0.5, 1.0, 2.0, size);
    if (world.rank == 0 && plot) {
      Plot1D(u, "LC_Parallel_" + 
                  OfNat(iterations) + "Iterations_" + 
                  OfNat(length) + "DomainSize" + 
                  OfNat(size)+ "Processes.pdf", 
                0.0, 2.0, 0.75, 2.25, "x", "u(x," + OfNat(iterations) + ")");
    }
  }

  function max(a:int, b:int):int {
    if a > b then a else b
  }

  function min(a:int, b:int):int {
    if a < b then a else b
  }

  lemma BoundsOKLemma(rank:nat, size:nat, nx:nat) 
    requires size > 1 
    requires rank < size
    requires nx % size == 0
    requires nx > 0
    ensures (nx / size) * rank < nx
    ensures (nx / size) * (rank + 1) <= nx
  {
    LemmaFundamentalDivMod(nx, size);
  }

  lemma ParallelInitSize(nx:nat, dx:real, low:real, high:real, value:real, 
                         rank:nat, size:nat, u:ArrayOfReals)
    requires rank < size
    requires size > 1
    requires dx > 0.0
    requires low > 0.0
    requires (nx / size) * rank < nx
    requires (nx / size) * (rank + 1) <= nx
    requires (low / dx).Floor <= (high / dx + 1.0).Floor < nx
    requires u.Repr == Spec.SpecInit(nx, dx, low, high, value)
                                  [(nx / size) * rank..(nx / size) * (rank + 1)]
    ensures |u.Repr| == nx / size
  { }

  function SpecInitPartial
    (nx:nat, dx:real, low:real, high:real, value:real, size:nat, rank:nat)
    :seq<real> 
    requires dx > 0.0
    requires low > 0.0
    requires (low / dx).Floor <= (high / dx + 1.0).Floor < nx
    requires rank < size
    requires size > 1
    requires nx % size == 0
  {
    Spec.SpecInit(nx, dx, low, high, value)
      [(nx / size) * rank..(nx / size) * (rank + 1)]
  }

  method ParallelInit(
    nx:nat, dx:real, low:real, high:real, value:real, rank:nat, size:nat) 
    returns (u:ArrayOfReals) 
    requires rank < size
    requires size > 1
    requires nx % size == 0
    requires dx > 0.0
    requires low > 0.0
    ensures u.IsValid()
    requires (low / dx).Floor <= (high / dx + 1.0).Floor < nx
    ensures u.Repr == SpecInitPartial(nx, dx, low, high, value, size, rank)
    ensures fresh(u)
    ensures u.FreeToWrite(0, u.length)
  { 
    reveal ArrayOfReals2D.FreeToWriteStatic;
    reveal ArrayOfReals2D.FreeToReadStatic;
    var nx_loc := nx / size;
    BoundsOKLemma(rank, size, nx);
    ghost var init := SpecInitPartial(nx, dx, low, high, value, size, rank);
    var lb := (low / dx).Floor;
    var ub := (high / dx + 1.0).Floor;
    var start:nat := min(max(lb - nx_loc * rank, 0), nx_loc);
    var end:int   := min(max(ub - nx_loc * rank, 0), nx_loc);
    u := Ones(nx_loc);
    if start < end {
      Arrays1D.SetRange(u, start, end, value);
    } 
    reveal SpecInit;
  }

  function RelySender(tag:nat, size:nat):nat {
    if size > 1 then tag % (size - 1) else 1
  }

  function RelyRecv(tag:nat, size:nat):nat {
   if size > 1 then tag % (size - 1) + 1 else 1
  }

  ghost function {:opaque} RelyPayload(
    nt:nat, 
    nx:nat, 
    tag:nat, 
    size:nat,
    initial:seq<real>,
    F:(real,real)->real):(r:seq<real>)
    ensures |r| == 1
  {
    if (&& size > 1 
        && tag / (size - 1) <= nt 
        && tag >= 0 
        && nx % size == 0
        && nx > 0 
        && |initial| == nx) 
    then var sender := RelySender(tag, size) + 1;
    [SpecOuterHelper(nt - tag / (size - 1), nt, initial, F)
      [(nx / size) * sender - 1]]
    else [0.0]
  }

  lemma OrderHelperLemma(low:int, high:nat, size:nat, rank:nat, n:nat) 
    requires low >= -1
    requires n == 0 ==> low == -1
    requires (n != 0 && rank != size - 1) 
              ==> low == (n - 1) * (size - 1) + rank 
    requires (n != 0 && rank == size - 1) 
              ==> low == (n - 1) * (size - 1) + rank - 1 
    requires rank != 0 ==> high <= n * (size - 1) + rank - 1
    requires rank == 0 ==> high <= n * (size - 1)
    requires size > 1
    requires rank < size
    ensures World<real>.NoTagBeforeStatic(
      low, high, size, rank, RelySender, RelyRecv)
  {
    reveal World<real>.NoTagBeforeStatic;
    if high < low {
      return;
    }
    if n == 0 {
      return;
    }
    var newLow := if low >= 0 then low else 0;
    for i := newLow to high 
      invariant World<real>.NoTagBeforeStatic(
        low, i, size, rank, RelySender, RelyRecv)
    {
      if (i < n * (size - 1)) {
        var diff := i - (n - 1) * (size - 1);
        LemmaFundamentalDivModConverse(i, size - 1, n-1, diff);
      } else {
        var diff := i - n * (size - 1);
        LemmaFundamentalDivModConverse(i, size - 1, n, diff);
      }
    }
  }

  method {:timeLimit 60} Parallel(
    nt:nat, nx:nat, dx:real, c:real, dt:real, 
    low:real, high:real, value:real, size:nat) 
    returns (u:ArrayOfReals, world:MPI.World<real>) 
    requires 32767 > size > 1
    requires nx % size == 0
    requires dx > 0.0
    requires low > 0.0
    ensures (nx / size) * world.rank < nx
    ensures (nx / size) * (world.rank + 1) <= nx
    requires (low / dx).Floor <= (high / dx + 1.0).Floor < nx
    ensures world.rank == 0 ==> u.Repr == Spec.Spec(nt, 
                                Spec.SpecInit(nx, dx, low, high, value), 
                                Spec.F(c, dt, dx))
    ensures fresh(u)
    ensures world.Finalized()
    ensures u.IsValid()
    ensures u.FreeToWrite(0, u.length)
    ensures u.FreeToRead(0, u.length)
  { 
    ghost var init := Spec.SpecInit(nx, dx, low, high, value);
    var F := Spec.F(c, dt, dx);
    world := new MPI.World<real>(
      size, 
      (tag:nat, size:nat) => RelyPayload(nt, nx, tag, size, init, F),
      RelySender,
      RelyRecv,
      (id:nat, size:nat) => 
        if id < nt
        then MPI.BarrierKind.Simple(id * (if size == 0 then 0 else size - 1))
        else MPI.BarrierKind.Gather(
          0, // root
          Spec.Spec(nt, init, Spec.F(c, dt, dx)), // what to gather
          nt * (if size == 0 then 0 else size - 1)), // next tag
      (size:nat) => nt + 1);
    var rank := world.rank;

    var nx_loc := nx / size;
    assert (nx / size) * world.rank < nx by {
      BoundsOKLemma(rank, size, nx);
    }
    assert (nx / size) * (world.rank + 1) <= nx by {
      BoundsOKLemma(rank, size, nx);
    }
    var lower := nx_loc * rank;
    u := ParallelInit(nx, dx, low, high, value, rank, size);
    ParallelInitSize(nx, dx, low, high, value, rank, size, u);
    assert  forall i:nat :: i < |u.Repr| ==> 
      u.Repr[i] == SpecOuterHelper(nt, nt, init, F)[lower + i] by {
      reveal SpecOuterHelper;
    }
    
    var un := Ones(nx_loc);
    reveal ArrayOfReals2D.FreeToWriteStatic;
    reveal ArrayOfReals2D.FreeToReadStatic;
    for n := 0 to nt 
      invariant u.IsValid()
      invariant un.IsValid()
      invariant u.FreeToWrite(0, u.length)
      invariant un.FreeToWrite(0, un.length)
      invariant forall i:nat :: i < |u.Repr| ==> 
        u.Repr[i] == SpecOuterHelper(nt - n, nt, init, F)[lower + i]
      invariant lower == 0 ==> u.Repr[0] == init[0]
      invariant world.RecvBuffer() == {}
      invariant world.SendBuffer() == {}
      invariant world.BarrierID() == n
      invariant !world.Finalized()
      invariant n == 0 ==> world.Tag() == -1
      invariant (n != 0 && rank == size - 1) 
                  ==> world.Tag() == (n - 1) * (size - 1) + rank - 1
      invariant (n != 0 && rank != size - 1) 
                  ==> world.Tag() == (n - 1) * (size - 1) + rank  
    {
      un := Copy(u);
      ghost var specOuter := SpecOuterHelper(nt - n, nt, init, F);
      for i := 1 to nx_loc 
        modifies u
        invariant u.IsValid()
        invariant u.FreeToWrite(0, u.length)
        invariant lower == 0 ==> u.Repr[0] == init[0]
        invariant forall i:nat :: i < |un.Repr| ==> 
           (un.Repr[i] == specOuter[lower + i])
        invariant forall j:nat :: 0 < j < i ==> 
           (u.Repr[j] == F(specOuter[lower + j], 
                           specOuter[lower + j - 1]))
      {
        u.Set(i, F(un.Get(i), un.Get(i - 1)));
      }
      if rank == 0 {
        var tag := n * (size - 1);
        LemmaFundamentalDivModConverse(tag, size - 1, n, 0);
        assert RelyPayload(nt, nx, tag, size, init, F) ==
               un.Repr[un.length - 1..un.length] by {
          reveal RelyPayload;
        }
        OrderHelperLemma(world.Tag(), tag, size, rank, n);
        world.Send(un, un.Length() - 1, 1, rank + 1, tag);
      } else if rank == size-1 {
        var tag := n * (size - 1) + rank - 1;
        LemmaFundamentalDivModConverse(tag, size - 1, n, rank - 1);
        OrderHelperLemma(world.Tag(), tag, size, rank, n);
        world.Recv(u, 0, 1, rank-1, tag);
        u.Set(0, F(un.Get(0), u.Get(0)));
        assert  u.Repr[0] == F(specOuter[lower], specOuter[lower - 1]) by {
          reveal RelyPayload;
        }
      } else {
        var itag := n * (size - 1) + rank;
        LemmaFundamentalDivModConverse(itag, size - 1, n, rank);
        assert RelyPayload(nt, nx, itag, size, init, F) ==
               un.Repr[un.length - 1..un.length] by {
          reveal RelyPayload;
        }
        var req := world.ISend(un, un.Length() - 1, 1, rank + 1, itag);
        var tag := n * (size - 1) + rank - 1;
        LemmaFundamentalDivModConverse(tag, size - 1, n, rank - 1);

        OrderHelperLemma(world.Tag(), tag, size, rank, n);
        calc {
          tag;
          == n * (size - 1) + rank - 1;
          <  n * (size - 1) + (size - 1);
          == {LemmaMulIsDistributive(size - 1, n, 1);}
             (n + 1) * (size - 1);
          == world.BarriersFull(world.BarrierID() + 1);
        }
        world.Recv(u, 0, 1, rank-1, tag);
        u.Set(0, F(un.Get(0), u.Get(0)));

        assert  u.Repr[0] == F(specOuter[lower], specOuter[lower - 1]) by {
          reveal RelyPayload;
        }
        world.LemmaNoTagBeforeVacuous(itag);
        req.Wait();
      }
      assert forall j:nat :: 0 < j < nx_loc ==> 
           (u.Repr[j] == F(specOuter[lower + j], 
                           specOuter[lower + j - 1]));
      SpecOuterLemmaCorollary(n, nt, lower, lower + nx_loc, 
                              init, specOuter, u.Repr, F);
      assert (rank == size - 1) ==> world.Tag() == n * (size - 1) + rank - 1;
      assert (rank != size - 1) ==> world.Tag() == n * (size - 1) + rank;
      OrderHelperLemma(world.Tag(), 
                       world.BarriersFull(world.BarrierID() + 1), 
                       size, rank, n + 1);
      calc {
        world.Tag();
        <
        n * (size - 1) + size - 1;
        == 
        (n + 1) * (size - 1);
      }
      world.Barrier(n);
    }
    OrderHelperLemma(world.Tag(), 
                     world.BarriersFull(world.BarrierID() + 1), 
                     size, rank, nt);
    var part := u;
    if (rank == 0) {
      u := new ArrayOfReals(nx, 0.0);
    }
    calc {
      |world.Barriers(nt, size).whole|;
      == |Spec.Spec(nt, init, Spec.F(c, dt, dx))|;
      == |init|;
      == nx;
    }
    assert part.Repr == Spec.Spec(nt,
      Spec.SpecInit(nx, dx, low, high, value), 
      Spec.F(c, dt, dx))
       [(nx / size) * world.rank..(nx / size) * (world.rank + 1)]
    by {
      reveal Spec.Spec;
    }
    world.Gather(0, part, u, 0, part.Length(), 0, nx, nt);
  }
}