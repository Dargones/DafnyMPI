include "../DafnyMPI/Externs/MPI.dfy"
include "../DafnyMPI/Externs/MPIResource.dfy"
include "../DafnyMPI/Arrays2D.dfy"
include "Spec.dfy"
include "../DafnyMPI/Utils.dfy"
include "RK4Impl.dfy"

module ParallelBackend {

  import opened Arrays2D
  import opened MPIResource
  import opened Spec
  import opened MPI
  import opened Std.Arithmetic.DivMod
  import opened Std.Arithmetic.Mul
  import opened Utils
  import opened RK4Impl

  lemma LemmaEqualWithPaddingAlt
    (u:ArrayOfReals2D, uSpec:seq<seq<real>>, 
     dim1:nat, dim2:nat, padding:nat, sx:nat, sy:nat) 
    requires |uSpec| == dim1
    requires forall i :: 0 <= i < |uSpec| ==> |uSpec[i]| == dim2
    requires dim1 >= u.dim1 + sx
    requires dim2 >= u.dim2 + sy
    requires padding <= u.dim1 - padding
    requires u.IsValid()
    requires u.Repr2D[padding..u.dim1 - padding] == 
             uSpec[sx + padding .. u.dim1 + sx - padding]
    ensures EqualWithPadding(u, uSpec, dim1, dim2, padding, sx, sy)
  {
    reveal EqualWithPadding;
  }

  lemma LemmaEqualWithPaddingAltConverse
    (u:ArrayOfReals2D, uSpec:seq<seq<real>>, 
     dim1:nat, dim2:nat, sx:nat) 
    requires |uSpec| == dim1
    requires forall i :: 0 <= i < |uSpec| ==> |uSpec[i]| == dim2
    requires dim1 >= u.dim1 + sx
    requires dim2 == u.dim2
    requires u.IsValid()
    requires EqualWithPadding(u, uSpec, dim1, dim2, 0, sx, 0)
    ensures u.Repr2D == uSpec[sx .. u.dim1 + sx]
  {
    reveal EqualWithPadding;
    assert forall i :: 0 <= i < |u.Repr2D| ==> 
      u.Repr2D[i] == uSpec[sx .. u.dim1 + sx][i];
  }

  lemma LemmaBarrierOrder
    (world:MPI.World<real>, high:nat, n:nat, nt:nat, 
     nx:nat, ny:nat, dim1:nat, dim2:nat, dx:real, dt:real) 
    requires world.rank == 0 
      ==> || (high == n * 2 * (world.size - 1))
          || (high == n * 2 * (world.size - 1) + 1)
    requires world.rank == world.size - 1
      ==> || (high == n * 2 * (world.size - 1) + 2 * (world.size - 2))
          || (high == n * 2 * (world.size - 1) + 2 * (world.size - 2) + 1)
    requires (world.rank != 0 && world.rank != world.size - 1) 
       ==> || (high == n * 2 * (world.size - 1) + 2 * (world.rank - 1))
           || (high == n * 2 * (world.size - 1) + 2 * (world.rank - 1) + 1)
           || (high == n * 2 * (world.size - 1) + 2 * (world.rank - 1) + 2)
           || (high == n * 2 * (world.size - 1) + 2 * (world.rank - 1) + 3)
    requires world.size > 1
    requires world.rank < world.size
    requires n <= nt
    requires dim1 >= 9
    requires dim2 >= 9
    requires dx * dx != 0.0
    requires world.Barriers == ((id, size) => 
      Barriers(id, size, nt, nx, ny, dim1, dim2, dx, dt))
    ensures world.Barriers(n, world.size).nextTag <= high < world.Barriers(n + 1, world.size).nextTag
  {
    assert world.Barriers(n, world.size).nextTag == n * 2 * (world.size - 1);
    assert world.Barriers(n + 1, world.size).nextTag == (n + 1) * 2 * (world.size - 1);
    assert high < n * 2 * (world.size - 1) + 2 * (world.size - 1);
    calc {
        high;
        <  n * 2 * (world.size - 1) + 2 * (world.size - 1);
        == {LemmaMulIsDistributiveAddOtherWay(2 * (world.size - 1), n ,1);}
           (n+1) * 2 * (world.size - 1);
        == world.Barriers(n + 1, world.size).nextTag;}
  }

  lemma LemmaOrder(world:MPI.World<real>, high:nat, n:nat) 
    requires world.Tag() >= -1
    requires world.RelyRecv == RelyReceiver
    requires world.RelySend == RelySender
    requires n == 0 ==> world.Tag() == -1
    requires (n != 0 && world.rank != world.size - 1) 
      ==> world.Tag() == (n - 1) * 2 * (world.size - 1) + 2 * world.rank + 1
    requires (n != 0 && world.rank == world.size - 1) 
      ==> world.Tag() == (n - 1) * 2 * (world.size - 1) + 2 * world.rank - 1
    requires world.rank == 0 
      ==> high == n * 2 * (world.size - 1)
    requires world.rank != 0 
      ==> n * 2 * (world.size - 1) <= high 
       <= n * 2 * (world.size - 1) + 2 * (world.rank - 1)
    requires world.size > 1
    requires world.rank < world.size
    ensures world.NoTagBefore(high)
    ensures high > world.Tag()
  {
    reveal World<real>.NoTagBeforeStatic;
    assert high > world.Tag() by {
      if (n != 0) {
        calc {
          world.Tag();
          < (n - 1) * 2 * (world.size - 1) + 2 * (world.size - 1);
          == {LemmaMulIsDistributive(2 * (world.size - 1), n-1, 1);}
            (n-1 + 1) * 2 * (world.size - 1);
        }
      } else {
        assert n * 2 * (world.size - 1) >= 0;
      }
    }
    var newTag := if world.Tag() >= 0 then world.Tag() else 0;
    for i := newTag to high 
      invariant World<real>.NoTagBeforeStatic(
        world.Tag(), i, world.size, world.rank, world.RelySend, world.RelyRecv)
    {
      if (i < n * 2 * (world.size - 1)) {
        var diff := i - (n - 1) * 2 * (world.size - 1);
        assert diff < 2 * (world.size - 1);
        LemmaFundamentalDivModConverse(i, 2 * (world.size - 1), n-1, diff);
      } else {
        var diff := i - 2 * n * (world.size - 1);
        LemmaFundamentalDivModConverse(i, 2 * (world.size - 1), n, diff);
      }
    }
  }

  lemma LemmaRTagRight(n:nat, size:nat, rtag:int, rank:nat) 
    requires size > 1
    requires rank < size - 1
    requires rtag == n * 2 * (size - 1) + 2 * rank + 1
    ensures rtag >= 0
    ensures RelySender(rtag, size) == rank + 1
    ensures RelyReceiver(rtag, size) == rank
    ensures Iteration(rtag, size) == n
  {
    assert ModuloIteration(rtag, size) == 2 * rank + 1 by {
      LemmaFundamentalDivModConverse(rtag, 2 * (size - 1), n, 2 * rank + 1);
    }
    calc {
      RelyReceiver(rtag, size);
      == ModuloIteration(rtag, size) / 2 + (rtag + 1) % 2;
      == {LemmaFundamentalDivModConverse(2 * rank + 1, 2, rank, 1);}
         rank + (rtag + 1) % 2;
      == rank + (2 * n * (size - 1) + 2) % 2;
      == {LemmaMulIsDistributiveAdd(2, n * (size - 1), 1);}
          rank + (2 * (n * (size - 1) + 1)) % 2;
      == rank;
    }
  }

  lemma LemmaRLenRight(rfrom:int, len:nat, u:ArrayOfReals2D) 
    requires u.IsValid()
    requires rfrom == (u.Dim1() - 4) * u.Dim2()
    requires len == 4 * u.Dim2()
    requires u.dim1 >= 9
    ensures rfrom >= 0
    ensures rfrom + len <= u.length
  {
    assert u.Dim1() - 4 >= 1;
    calc {
      rfrom + len;
      == (u.Dim1() - 4) * u.Dim2() + 4 * u.Dim2();
      == {LemmaMulIsDistributive(u.Dim2(), u.Dim1() - 4, 4);}
          (u.Dim1() - 4 + 4) * u.Dim2();
      == u.Dim1() * u.Dim2();
      == u.length;
    }
  }

  lemma LemmaSTagRight(n:nat, size:nat, stag:nat, rank:nat) 
    requires size > 1
    requires rank < size - 1
    requires stag == n * 2 * (size - 1) + 2 * rank
    ensures stag >= 0
    ensures RelySender(stag, size) == rank
    ensures RelyReceiver(stag, size) == rank + 1
    ensures Iteration(stag, size) == n
  {
    assert ModuloIteration(stag, size) == 2 * rank by {
      LemmaFundamentalDivModConverse(stag, 2 * (size - 1), n, 2 * rank);
    }
    calc {
      RelyReceiver(stag, size);
      == ModuloIteration(stag, size) / 2 + (stag + 1) % 2;
      == rank + (stag + 1) % 2;
      == rank + (2 * n * (size - 1) + 1) % 2;
      == {LemmaFundamentalDivModConverse(
          2 * n * (size - 1) + 1, 2, n * (size - 1), 1);}
         rank + 1;
    }
  }

  lemma LemmaSLenRight(sfrom:int, len:nat, u:ArrayOfReals2D) 
    requires u.IsValid()
    requires sfrom == (u.Dim1() - 8) * u.Dim2()
    requires len == 4 * u.Dim2()
    requires u.dim1 >= 9
    ensures sfrom >= 0
    ensures sfrom + len <= u.length
  {
    assert u.Dim1() - 4 >= 1;
    calc {
      sfrom + len;
      == (u.Dim1() - 8) * u.Dim2() + 4 * u.Dim2();
      == {LemmaMulIsDistributive(u.Dim2(), u.Dim1() - 8, 4);}
         (u.Dim1() - 8 + 4) * u.Dim2();
      <= {LemmaMulInequality(u.Dim1() - 4, u.Dim1(), u.Dim2());}
         u.Dim1() * u.Dim2();
      == u.length;
    }
  }

  lemma LemmaRTagLeft(n:nat, size:nat, rtag:int, rank:nat) 
    requires size > 1
    requires 0 < rank < size
    requires rtag == n * 2 * (size - 1) + 2 * rank - 2
    ensures rtag >= 0
    ensures RelySender(rtag, size) == rank - 1
    ensures RelyReceiver(rtag, size) == rank
    ensures Iteration(rtag, size) == n
  {
    assert ModuloIteration(rtag, size) == 2 * rank - 2 by {
      LemmaFundamentalDivModConverse(rtag, 2 * (size - 1), n, 
                                           2 * rank - 2);
    }
    calc {
      RelyReceiver(rtag, size);
      == ModuloIteration(rtag, size) / 2 + (rtag + 1) % 2;
      == 1 * rank - 1 + (rtag + 1) % 2;
      == {LemmaFundamentalDivModConverse(rtag, 2, 
          n * (size - 1) + rank - 1, 0);}
         rank;
    }
  }

  lemma LemmaSTagLeft(n:nat, size:nat, rtag:int, rank:nat) 
    requires size > 1
    requires 0 < rank < size
    requires rtag == n * 2 * (size - 1) + 2 * rank - 1
    ensures rtag >= 0
    ensures RelySender(rtag, size) == rank
    ensures RelyReceiver(rtag, size) == rank - 1
    ensures Iteration(rtag, size) == n
  {
    assert ModuloIteration(rtag, size) == 2 * rank - 1 by {
      LemmaFundamentalDivModConverse(rtag, 2 * (size - 1), n, 
                                           2 * rank - 1);
    }
    calc {
      ModuloIteration(rtag, size) / 2;
      == (2 * rank - 1) / 2;
      == (2 * rank - 2 + 1) / 2;
      == {LemmaMulIsDistributiveAdd(2, rank, -1);}
         (2 * (rank - 1) + 1) / 2;
      == {LemmaFundamentalDivModConverse(2 * (rank - 1) + 1, 2, rank - 1, 1);}
         rank - 1;
    } 
    calc {
      RelyReceiver(rtag, size);
      == ModuloIteration(rtag, size) / 2 + (rtag + 1) % 2;
      == rank - 1 + (rtag + 1) % 2;
      == {LemmaFundamentalDivModConverse(rtag + 1, 2, 
          n * (size - 1) + rank, 0);}
         rank - 1;
    }
  }

  method {:isolate_assertions} {:timeLimit 80} ExchangeBoundaryDataP0
    (u:ArrayOfReals2D, world:MPI.World<real>, 
     nx:nat, ny:nat, nt:nat, dim1:nat, dim2:nat, dx:real, dt:real, n:nat)
    requires world.size > 1
    requires dim1 >= 9
    requires dim2 >= 9
    requires world.size > 1
    requires world.rank == 0
    requires (dim1 - 8) % world.size == 0 
    requires (dim1 - 8) / world.size >= 4
    requires dx * dx != 0.0
    requires 0 < 1 * ((dim1 - 8) / world.size) <= dim1 - 8
    requires n <= nt
    requires u.IsValid()
    requires u.FreeToWrite(0, u.length)
    requires u.FreeToRead(0, u.length)
    requires u.dim1 == (dim1 - 8) / world.size + 8
    requires u.dim2 == dim2
    requires EqualSlice(u, 
      SpecOuterHelper(nt-n, nt, 
                      Spec.SpecInit(nx, ny, dim1, dim2), 
                      dim1, dim2, dx, dt), 
      dim1, 4, u.dim1 - 4, 0)
    requires world.BarrierID() == n
    requires n == 0 ==> world.Tag() == -1
    requires n != 0 
      ==> world.Tag() == (n - 1) * 2 * (world.size - 1) + 1
    requires world.SendBuffer() == {}
    requires world.RecvBuffer() == {}
    requires !world.Finalized()
    requires world.RelyMess == ((tag:nat, size:nat) => 
        RelyPayload(tag, size, nx, ny, nt, dim1, dim2, dx, dt))
    requires world.RelySend == RelySender
    requires world.RelyRecv == RelyReceiver
    requires world.Barriers == ((id, size) => 
      Barriers(id, size, nt, nx, ny, dim1, dim2, dx, dt))
    requires world.LastBarrier == ((size:nat) => nt + 2)
    modifies u, world
    ensures u.IsValid()
    ensures u.FreeToWrite(0, u.length)
    ensures EqualWithPadding(u, 
      SpecOuterHelper(nt-n, nt, 
                      Spec.SpecInit(nx, ny, dim1, dim2), 
                      dim1, dim2, dx, dt), 
      dim1, dim2, 0, 0, 0)
    ensures world.Tag() == n * 2 * (world.size - 1) + 1 
    ensures world.SendBuffer() == {}
    ensures world.RecvBuffer() == {}
    ensures world.BarrierID() == n
    ensures !world.Finalized()
  {
    ghost var spec := SpecOuterHelper(nt-n, nt, 
                      Spec.SpecInit(nx, ny, dim1, dim2), 
                      dim1, dim2, dx, dt);
    LemmaNoWriteLockBlockTrivial(u, 0, 4, 0, u.dim2);
    LemmaNoReadLockBlockTrivial(u, 0, 4, 0, u.dim2);
    Arrays2D.SetRange(u, 0, 4, 0, u.Dim2(), 0.0);
    assert EqualSlice(u, spec, dim1, 4, u.dim1 - 4, 0)
        && AllInRange(u, 0, 4, 0, u.dim2, 0.0) by {
      reveal Arrays2D.AllInRange;
      reveal Arrays2D.AllOutRange;
      reveal EqualSlice;
    }
    ghost var oldRepr2D := u.Repr2D;

    var rtag := n * 2 * (world.size - 1) + 1;
    var rfrom := (u.Dim1() - 4) * u.Dim2();
    var len := 4 * u.Dim2();
    LemmaRLenRight(rfrom, len, u);
    LemmaRTagRight(n, world.size, rtag, 0);
    var stag := n * 2 * (world.size - 1);
    var sfrom := (u.Dim1() - 8) * u.Dim2();
    LemmaSLenRight(sfrom, len, u);
    LemmaSTagRight(n, world.size, stag, 0);
    ghost var oldWriteLock := u.WriteLock;
    u.LemmaFreeToReadNarrower(sfrom, sfrom + len);

    u.LemmaFreeToWriteNarrower(rfrom, rfrom + len);
    var req := world.IRecv(u, rfrom, len, 1, rtag);
    u.LemmaRepr2DUnchanged(oldRepr2D);
    assert EqualSlice(u, spec, dim1, 4, u.dim1 - 4, 0)
        && AllInRange(u, 0, 4, 0, u.dim2, 0.0) by {
      reveal Arrays2D.AllInRange;
      reveal EqualSlice;
    }

    assert u.FreeToRead(sfrom, sfrom+len) by {
      LemmaSLenRight(sfrom, len, u);
      LemmaRLenRight(rfrom, len, u);
      assert ArrayOfReals2D.FreeToReadStatic
        (oldWriteLock, u.length, sfrom, sfrom + len) ;
      ArrayOfReals2D.LemmaWriteNonOverlapping
        (oldWriteLock, u.WriteLock, u.ReadLocks, rfrom, rfrom+len, 
        sfrom, sfrom+len, u.length);
    }
    assert world.RelyMessFull(stag) == u.Repr[sfrom..sfrom+len] by {
      ghost var step := (dim1 - 8) / world.size;
      LemmaEqualWithPaddingFlatten(u, spec, dim1, 0, u.dim1 - 8, 4, 4);
      LemmaRelyPayloadContent(stag, world.size, nx, ny, nt, dim1, dim2, 
                              dx, dt, spec, 0, 1, n, step);
       calc {
        0 * u.dim2 + (u.dim1 - 8) * u.dim2;
        == (u.dim1 - 8) * u.dim2;
        == ((dim1 - 8) / world.size + 8 - 8) * u.dim2;
        == ((dim1 - 8) / world.size) * u.dim2;
        == step * dim2;
        == ((0 + 1) * step) * dim2;
       }
       calc {
        0 * u.dim2 + (u.dim1 - 8) * u.dim2 + 4 * u.dim2;
        == ((0 + 1) * step) * dim2 + 4 * u.dim2;
        == {LemmaMulIsDistributiveAddOtherWay(u.dim2, ((0 + 1) * step), 4);}
           ((0 + 1) * step + 4) * u.dim2;
       }
    }
    LemmaOrder(world, stag, n);
    LemmaBarrierOrder(world, stag, n, nt, nx, ny, dim1, dim2, dx, dt);
    world.Send(u, sfrom, len, 1, stag);
    u.LemmaRepr2DUnchanged(oldRepr2D);
    ghost var oldRepr := u.Repr;
    assert EqualSlice(u, spec, dim1, 4, u.dim1 - 4, 0)
        && AllInRange(u, 0, 4, 0, u.dim2, 0.0) by {
      reveal Arrays2D.AllInRange;
      reveal EqualSlice;
    }
    
    world.LemmaNoTagBeforeVacuous(rtag);
    LemmaBarrierOrder(world, rtag, n, nt, nx, ny, dim1, dim2, dx, dt);
    LemmaRelyPayloadSize(rtag, world.size, nx, ny, nt, dim1, dim2, dx, dt);
    req.Wait();

    assert EqualSlice(u, spec, dim1, (u.dim1 - 4), u.dim1, 0) by {
      ghost var step := (dim1 - 8) / world.size;
      LemmaRelyPayloadContent(rtag, world.size, nx, ny, nt, dim1, dim2, 
                              dx, dt, spec, 1, 0, n, step);
      assert RelyPayload(rtag, world.size, nx, ny, nt, dim1, dim2, dx, dt) 
          == ArrayOfReals2D.Flatten(spec, dim2)[(1 * step + 4) * dim2..(1 * step + 8) * dim2];
      assert u.Repr[rfrom..rfrom+len] == 
        ArrayOfReals2D.Flatten(spec, dim2)[rfrom..rfrom+len] by {
          calc {
               (1 * step + 4) * dim2;
            == (step + 4) * dim2;
            == (u.dim1 - 4) * dim2;
            == rfrom;
          }
          calc {
               (1 * step + 8) * dim2;
            == (step + 8) * dim2;
            == (u.dim1 - 4 + 4) * dim2;
            == {LemmaMulIsDistributiveAdd(dim2, u.dim1 - 4, 4);}
               (u.dim1 - 4) * dim2 + 4 * dim2;
            == rfrom + len;
          }
      }
      LemmaEqualWithPaddingFlattenConverse(u, spec, dim1, 0, u.dim1 - 4, 4, 
                                           rfrom, len);
    }

    assert EqualWithPadding(u, spec, dim1, dim2, 0, 0, 0) by {
      u.LemmaRepr2DPartiallyChanged(oldRepr2D, oldRepr, u.dim1 - 4, 4);
      reveal Arrays2D.AllInRange;
      reveal EqualWithPadding;
      reveal EqualSlice;
      reveal Spec.BorderIsZero;
    }

    assert u.FreeToWrite(0, u.length) by {
      ArrayOfReals2D.LemmaSetWriteLockCancel
        (oldWriteLock, u.ReadLocks, rfrom, len);
      reveal ArrayOfReals2D.FreeToWriteStatic;
    }
  }

  method {:isolate_assertions} {:timeLimit 60} ExchangeBoundaryDataPLast
    (u:ArrayOfReals2D, world:MPI.World<real>, 
     nx:nat, ny:nat, nt:nat, dim1:nat, dim2:nat, dx:real, dt:real, n:nat)
    requires world.size > 1
    requires dim1 >= 9
    requires dim2 >= 9
    requires world.size > 1
    requires world.rank == world.size - 1
    requires (dim1 - 8) % world.size == 0 
    requires (dim1 - 8) / world.size >= 4
    requires dx * dx != 0.0
    requires 0 < 1 * ((dim1 - 8) / world.size) <= dim1 - 8
    requires n <= nt
    requires u.IsValid()
    requires u.FreeToWrite(0, u.length)
    requires u.FreeToRead(0, u.length)
    requires u.dim1 == (dim1 - 8) / world.size + 8
    requires u.dim2 == dim2
    requires EqualSlice(u, 
      SpecOuterHelper(nt-n, nt, 
                      Spec.SpecInit(nx, ny, dim1, dim2), 
                      dim1, dim2, dx, dt), 
      dim1, 4, u.dim1 - 4, world.rank * ((dim1 - 8) / world.size))
    requires world.BarrierID() == n
    requires n == 0 ==> world.Tag() == -1
    requires n != 0 
      ==> world.Tag() == (n - 1) * 2 * (world.size - 1) + 2 * world.rank - 1
    requires world.SendBuffer() == {}
    requires world.RecvBuffer() == {}
    requires !world.Finalized()
    requires world.RelyMess == ((tag:nat, size:nat) => 
        RelyPayload(tag, size, nx, ny, nt, dim1, dim2, dx, dt))
    requires world.RelySend == RelySender
    requires world.RelyRecv == RelyReceiver
    requires world.Barriers == ((id, size) => 
      Barriers(id, size, nt, nx, ny, dim1, dim2, dx, dt))
    requires world.LastBarrier == ((size:nat) => nt + 2)
    modifies u, world
    ensures u.IsValid()
    ensures u.FreeToWrite(0, u.length)
    ensures EqualWithPadding(u, 
      SpecOuterHelper(nt-n, nt, 
                      Spec.SpecInit(nx, ny, dim1, dim2), 
                      dim1, dim2, dx, dt), 
      dim1, dim2, 0, world.rank * ((dim1 - 8) / world.size), 0)
    ensures world.Tag() == n * 2 * (world.size - 1) + 2 * world.rank - 1
    ensures world.SendBuffer() == {}
    ensures world.RecvBuffer() == {}
    ensures world.BarrierID() == n
    ensures !world.Finalized()
  {
    ghost var step := (dim1 - 8) / world.size;
    ghost var shift := (world.size - 1) * step;
    ghost var spec := SpecOuterHelper(nt-n, nt, 
                      Spec.SpecInit(nx, ny, dim1, dim2), 
                      dim1, dim2, dx, dt);
    LemmaNoWriteLockBlockTrivial(u, u.dim1 - 4, u.dim1, 0, u.dim2);
    LemmaNoReadLockBlockTrivial(u, u.dim1 - 4, u.dim1, 0, u.dim2);
    Arrays2D.SetRange(u, u.Dim1() - 4, u.Dim1(), 0, u.Dim2(), 0.0);
    assert EqualSlice(u, spec, dim1, 4, u.dim1 - 4, shift)
        && AllInRange(u, u.dim1 - 4, u.dim1, 0, u.dim2, 0.0) by {
      reveal Arrays2D.AllInRange;
      reveal Arrays2D.AllOutRange;
      reveal EqualSlice;
    }
    ghost var oldRepr2D := u.Repr2D;

    var rtag := n * 2 * (world.size - 1) + 2 * (world.size - 1) - 2;
    var rfrom := 0;
    var len := 4 * u.Dim2();
    LemmaRTagLeft(n, world.size, rtag, world.size-1);
    var stag := n * 2 * (world.size - 1) + 2 * (world.size - 1) - 1;
    var sfrom := 4 * u.Dim2();
    LemmaSTagLeft(n, world.size, stag, world.size-1);
    ghost var oldWriteLock := u.WriteLock;
    ghost var oldReadLocks := u.ReadLocks;
    calc {
      sfrom + len;
      == 4 * u.Dim2() + 4 * u.Dim2();
      == {LemmaMulIsDistributiveAddOtherWay(u.Dim2(), 4, 4);}
         8 * u.Dim2();
      <= {LemmaMulStrictInequality(8, u.Dim1(), u.Dim2());}
         u.Dim1() * u.Dim2();
      == u.length;
    }
    u.LemmaFreeToReadNarrower(sfrom, sfrom + len);
    u.LemmaFreeToWriteNarrower(rfrom, rfrom + len);

    assert world.RelyMessFull(stag) == u.Repr[sfrom..sfrom+len] by {
      LemmaEqualWithPaddingFlatten(u, spec, dim1, shift, 4, 4, 4);
      LemmaRelyPayloadContent(stag, world.size, nx, ny, nt, dim1, dim2, dx, dt,
                              spec, world.size - 1, world.size - 2, n, step);
      assert ((world.size - 1) * step + 4) * dim2 ==
             shift * u.dim2 + 4 * u.dim2;
      assert ((world.size - 1) * step + 8) * dim2 == 
             shift * u.dim2 + 4 * u.dim2 + 4 * u.dim2;
    }
    
    var req := world.ISend(u, sfrom, len, world.size - 2, stag);
    u.LemmaRepr2DUnchanged(oldRepr2D);
    assert EqualSlice(u, spec, dim1, 4, u.dim1 - 4, shift)
        && AllInRange(u, u.dim1 - 4, u.dim1, 0, u.dim2, 0.0) by {
      reveal Arrays2D.AllInRange;
      reveal EqualSlice;
    }

    assert u.FreeToWrite(rfrom, rfrom+len) by {
      assert ArrayOfReals2D.FreeToWriteStatic
        (oldWriteLock, oldReadLocks, u.length, rfrom, rfrom + len) ;
      ArrayOfReals2D.LemmaReadNonOverlapping
        (oldReadLocks, u.ReadLocks, u.WriteLock, sfrom, sfrom+len, 
        rfrom, rfrom+len, u.length, 1);
    }

    LemmaOrder(world, rtag, n);
    LemmaBarrierOrder(world, rtag, n, nt, nx, ny, dim1, dim2, dx, dt);
    LemmaRelyPayloadSize(rtag, world.size, nx, ny, nt, dim1, dim2, dx, dt);
    var oldRepr := u.Repr;
    
    world.Recv(u, rfrom, len, world.size - 2, rtag);

    assert EqualSlice(u, spec, dim1, 0, 4, shift) by {
      LemmaRelyPayloadContent(rtag, world.size, nx, ny, nt, dim1, dim2, dx, dt,
                              spec, world.size - 2, world.size - 1, n, step);
      LemmaRelyPayloadConds(rtag, world.size, nt, dim1, dim2, dx, step, 
                            world.size - 2, world.size - 1); 
      assert  RelyPayload(rtag, world.size, nx, ny, nt, dim1, dim2, dx, dt) ==
        ArrayOfReals2D.Flatten(spec, dim2)
          [((world.size - 1) * step) * dim2..
           ((world.size - 1) * step + 4) * dim2];
      assert u.Repr[rfrom..rfrom+len] == 
        ArrayOfReals2D.Flatten(spec, dim2)
        [shift * u.dim2+rfrom..shift * u.dim2+rfrom+len];
      // might want to use calc to prove shift * u.dim2+rfrom == rfrom, etc.
      LemmaEqualWithPaddingFlattenConverse(u, spec, dim1, shift, 0, 4,
                                           rfrom, len);
    }

    assert EqualWithPadding(u, spec, dim1, dim2, 0, shift, 0) by {   
      u.LemmaRepr2DPartiallyChanged(oldRepr2D, oldRepr, 0, 4);
      reveal EqualSlice;
      reveal EqualWithPadding;
      reveal Spec.BorderIsZero;
      reveal Arrays2D.AllInRange;
      calc {
        shift + u.dim1 - 4;
        == {LemmaMulIsDistributiveAdd((|spec| - 8) / world.size, 1, 
                                       world.size - 1);}
          world.size * ((|spec| - 8) / world.size) + 4;
        == |spec| - 8 + 4;
        == |spec| - 4;
      }
    }
    oldRepr2D := u.Repr2D;
    
    world.LemmaNoTagBeforeVacuous(stag);
    LemmaBarrierOrder(world, stag, n, nt, nx, ny, dim1, dim2, dx, dt);
    req.Wait();

    assert EqualWithPadding(u, spec, dim1, dim2, 0, shift, 0) by {
      u.LemmaRepr2DUnchanged(oldRepr2D);
      reveal EqualWithPadding;
    }

    assert u.FreeToWrite(0, u.length) by {
      ArrayOfReals2D.LemmaUpdateReadLockCancel(oldReadLocks, rfrom, len);
      reveal ArrayOfReals2D.FreeToWriteStatic;
    }
  }

  method {:isolate_assertions} {:timeLimit 80} ExchangeBoundaryDataPMiddle
    (u:ArrayOfReals2D, world:MPI.World<real>, 
     nx:nat, ny:nat, nt:nat, dim1:nat, dim2:nat, dx:real, dt:real, n:nat)
    requires world.size > 1
    requires dim1 >= 9
    requires dim2 >= 9
    requires world.size > 1
    requires 0 < world.rank < world.size - 1
    requires (dim1 - 8) % world.size == 0 
    requires (dim1 - 8) / world.size >= 4
    requires dx * dx != 0.0
    requires 0 <= world.rank      * ((dim1 - 8) / world.size) 
               < (world.rank + 1) * ((dim1 - 8) / world.size) <= dim1 - 8
    requires n <= nt
    requires u.IsValid()
    requires u.FreeToWrite(0, u.length)
    requires u.FreeToRead(0, u.length)
    requires u.dim1 == (dim1 - 8) / world.size + 8
    requires u.dim2 == dim2
    requires EqualSlice(u, 
      SpecOuterHelper(nt-n, nt, 
                      Spec.SpecInit(nx, ny, dim1, dim2), 
                      dim1, dim2, dx, dt), 
      dim1, 4, u.dim1 - 4, world.rank * ((dim1 - 8) / world.size))
    requires world.BarrierID() == n
    requires n == 0 ==> world.Tag() == -1
    requires n != 0 
      ==> world.Tag() == (n - 1) * 2 * (world.size - 1) + 2 * world.rank + 1
    requires world.SendBuffer() == {}
    requires world.RecvBuffer() == {}
    requires !world.Finalized()
    requires world.RelyMess == ((tag:nat, size:nat) => 
        RelyPayload(tag, size, nx, ny, nt, dim1, dim2, dx, dt))
    requires world.RelySend == RelySender
    requires world.RelyRecv == RelyReceiver
    requires world.Barriers == ((id, size) => 
      Barriers(id, size, nt, nx, ny, dim1, dim2, dx, dt))
    requires world.LastBarrier == ((size:nat) => nt + 2)
    modifies u, world
    ensures u.IsValid()
    ensures u.FreeToWrite(0, u.length)
    ensures EqualWithPadding(u, 
      SpecOuterHelper(nt-n, nt, 
                      Spec.SpecInit(nx, ny, dim1, dim2), 
                      dim1, dim2, dx, dt), 
      dim1, dim2, 0, world.rank * ((dim1 - 8) / world.size), 0)
    ensures world.Tag() == n * 2 * (world.size - 1) + 2 * world.rank + 1 
    ensures world.SendBuffer() == {}
    ensures world.RecvBuffer() == {}
    ensures world.BarrierID() == n
    ensures !world.Finalized()
  {
    ghost var step := (dim1 - 8) / world.size;
    ghost var shift := world.rank * step;
    ghost var spec := SpecOuterHelper(nt-n, nt, 
                      Spec.SpecInit(nx, ny, dim1, dim2), 
                      dim1, dim2, dx, dt);
    ghost var oldRepr2D := u.Repr2D;
    ghost var oldWriteLock := u.WriteLock;
    ghost var oldReadLocks := u.ReadLocks;
    ghost var oldRepr := u.Repr;

    // Tags for communication with the process on the left:
    var len := 4 * u.Dim2();
    var rLeftTag := n * 2 * (world.size - 1) + 2 * world.rank - 2;
    var rLeftFrom := 0;
    LemmaRTagLeft(n, world.size, rLeftTag, world.rank);
    var sLeftTag := n * 2 * (world.size - 1) + 2 * world.rank - 1;
    var sLeftFrom := 4 * u.Dim2();
    LemmaSTagLeft(n, world.size, sLeftTag, world.rank);

    // Tags for communication with the process on the right:
    var sRightTag := n * 2 * (world.size - 1) + 2 * world.rank;
    var sRightFrom := (u.Dim1() - 8) * u.Dim2();
    LemmaSLenRight(sRightFrom, len, u);
    LemmaSTagRight(n, world.size, sRightTag, world.rank);

    var rRightTag := n * 2 * (world.size - 1) + 2 * world.rank +1;
    var rRightFrom := (u.Dim1() - 4) * u.Dim2();
    LemmaRLenRight(rRightFrom, len, u);
    LemmaRTagRight(n, world.size, rRightTag, world.rank);

    u.LemmaFreeToReadNarrower(sLeftFrom, sLeftFrom + len);
    u.LemmaFreeToWriteNarrower(rLeftFrom, rLeftFrom + len);
    u.LemmaFreeToReadNarrower(sRightFrom, sRightFrom + len);
    u.LemmaFreeToWriteNarrower(rRightFrom, rRightFrom + len);

    LemmaRelyPayloadSize(rLeftTag, world.size, nx, ny, nt, dim1, dim2, dx, dt);
    
    var reqRRight := world.IRecv(u, rRightFrom, len, world.rank + 1, rRightTag);
    
    assert EqualSlice(u, spec, dim1, 4, u.dim1 - 4, shift) by {
      u.LemmaRepr2DUnchanged(oldRepr2D);
      reveal EqualSlice;
    }

    assert world.RelyMessFull(sRightTag) == 
           u.Repr[sRightFrom..sRightFrom+len] by {
      LemmaEqualWithPaddingFlatten(u, spec, dim1, shift, u.dim1 - 8, 4, 4);
      LemmaRelyPayloadContent(sRightTag, world.size, nx, ny, nt, dim1, dim2, 
                              dx, dt, spec, world.rank, world.rank+1, n, step);
      calc {
        shift * u.dim2 + (u.dim1 - 8) * u.dim2;
        == (world.rank * step) * dim2 + (step + 8 - 8) * dim2;
        == (world.rank * step) * dim2 + step * dim2;
        == {LemmaMulIsAssociative(world.rank, step, dim2);}
           world.rank * (step * dim2) + step * dim2;
        == {LemmaMulIsDistributiveAddOtherWay(step * dim2, world.rank, 1);}
           (world.rank + 1) * (step * dim2);
        == {LemmaMulIsAssociative(world.rank + 1, step, dim2);}
           ((world.rank + 1) * step) * dim2;
      }
      calc {
        ((world.rank + 1) * step + 4) * dim2;
        == {LemmaMulIsDistributiveAddOtherWay(dim2, (world.rank+1) * step, 4);}
           ((world.rank + 1) * step) * dim2 + 4 * dim2;
        == shift * u.dim2 + (u.dim1 - 8) * u.dim2 + 4 * u.dim2;
      }
    }

    assert u.FreeToRead(sLeftFrom, sLeftFrom+len)
        && u.FreeToRead(sRightFrom, sRightFrom+len)
        && u.FreeToWrite(rLeftFrom, rLeftFrom+len) by {
      calc {
        sLeftFrom+len;
        == 4 * u.Dim2() + 4 * u.Dim2();
        == {LemmaMulIsDistributiveAddOtherWay(u.Dim2(), 4, 4);}
           8 * u.Dim2();
        <= {LemmaMulInequality(8, u.Dim1() - 4, u.Dim2());}
           (u.Dim1() - 4) * u.Dim2();
        == rRightFrom;
      }
      ArrayOfReals2D.LemmaWriteNonOverlapping
        (oldWriteLock, u.WriteLock, u.ReadLocks, rRightFrom, rRightFrom+len, 
        sLeftFrom, sLeftFrom+len, u.length);
      ArrayOfReals2D.LemmaWriteNonOverlapping
        (oldWriteLock, u.WriteLock, u.ReadLocks, rRightFrom, rRightFrom+len, 
        sRightFrom, sRightFrom+len, u.length);
      ArrayOfReals2D.LemmaWriteNonOverlapping
        (oldWriteLock, u.WriteLock, u.ReadLocks, rRightFrom, rRightFrom+len, 
        rLeftFrom, rLeftFrom+len, u.length);
    }
    var newerReadLock := u.ReadLocks;

    var reqSRight := world.ISend(u, sRightFrom, len, world.rank + 1, sRightTag);

    assert u.FreeToRead(sLeftFrom, sLeftFrom+len)
        && u.FreeToWrite(rLeftFrom, rLeftFrom+len) by {
      calc {
        rLeftFrom+len;
        == 4 * u.Dim2();
        <= {LemmaMulInequality(4, u.Dim1() - 8, u.Dim2());}
           (u.Dim1() - 8) * u.Dim2(); 
        == sRightFrom;
      }
      ArrayOfReals2D.LemmaReadNonOverlapping
        (newerReadLock, u.ReadLocks, u.WriteLock, sRightFrom, sRightFrom+len, 
        rLeftFrom, rLeftFrom+len, u.length, 1);
    }

    assert EqualSlice(u, spec, dim1, 4, u.dim1 - 4, shift) by {
      u.LemmaRepr2DUnchanged(oldRepr2D);
      reveal EqualSlice;
    }

    assert world.RelyMessFull(sLeftTag) == 
           u.Repr[sLeftFrom..sLeftFrom+len] by {
      LemmaEqualWithPaddingFlatten(u, spec, dim1, shift, 4, 4, 4);
      LemmaRelyPayloadContent(sLeftTag, world.size, nx, ny, nt, dim1, dim2, dx, 
                              dt, spec, world.rank, world.rank-1, n, step);
      assert (world.rank * step + 4) * dim2 == shift * u.dim2 + 4 * u.dim2;
      assert (world.rank * step + 8) * dim2 == 
             shift * u.dim2 + 4 * u.dim2 + 4 * u.dim2;
    }

    var newestReadLock := u.ReadLocks;
    
    var reqSLeft := world.ISend(u, sLeftFrom, len, world.rank - 1, sLeftTag);

    assert EqualSlice(u, spec, dim1, 4, u.dim1 - 4, shift) by {
      u.LemmaRepr2DUnchanged(oldRepr2D);
      reveal EqualSlice;
    }

    assert u.FreeToWrite(rLeftFrom, rLeftFrom+len) by {
      ArrayOfReals2D.LemmaReadNonOverlapping
        (newestReadLock, u.ReadLocks, u.WriteLock, sLeftFrom, sLeftFrom+len, 
        rLeftFrom, rLeftFrom+len, u.length, 1);
    }

    LemmaOrder(world, rLeftTag, n);
    LemmaBarrierOrder(world, rLeftTag, n, nt, nx, ny, dim1, dim2, dx, dt);
    LemmaRelyPayloadSize(rLeftTag, world.size, nx, ny, nt, dim1, dim2, dx, dt);
    
    world.Recv(u, rLeftFrom, len, world.rank - 1, rLeftTag);
    
    assert EqualSlice(u, spec, dim1, 0, 4, shift) by {
      LemmaRelyPayloadContent(rLeftTag, world.size, nx, ny, nt, dim1, dim2, dx, dt,
                              spec, world.rank - 1, world.rank, n, step);
      LemmaRelyPayloadConds(rLeftTag, world.size, nt, dim1, dim2, dx, step, 
                            world.rank - 1, world.rank); 
      calc {
        shift * u.dim2+rLeftFrom;
        == (world.rank * step) * dim2;
      }
      calc {
        (world.rank * step + 4) * dim2;
        == {LemmaMulIsDistributiveAddOtherWay(dim2, world.rank * step, 4);}
           (world.rank * step) * dim2 + 4 * dim2;
        == shift * u.dim2+rLeftFrom + 4 * u.dim2;
        == shift * u.dim2+rLeftFrom+len;
      }
      LemmaEqualWithPaddingFlattenConverse(u, spec, dim1, shift, 0, 4,
                                           rLeftFrom, len);
    }

    assert EqualSlice(u, spec, dim1, 0, u.dim1 - 4, shift) by {
      u.LemmaRepr2DPartiallyChanged(oldRepr2D, oldRepr, 0, 4);
      reveal EqualSlice;
    }

    oldRepr2D := u.Repr2D;
    oldRepr := u.Repr;
    
    world.LemmaNoTagBeforeVacuous(sLeftTag);
    LemmaBarrierOrder(world, sLeftTag, n, nt, nx, ny, dim1, dim2, dx, dt);
    reqSLeft.Wait();

    var afterWaitreadLock := u.ReadLocks;

    assert EqualSlice(u, spec, dim1, 0, u.dim1 - 4, shift) by {
      u.LemmaRepr2DUnchanged(oldRepr2D);
      reveal EqualSlice;
    }

    world.LemmaNoTagBeforeVacuous(sRightTag);
    LemmaBarrierOrder(world, sRightTag, n, nt, nx, ny, dim1, dim2, dx, dt);
    reqSRight.Wait();

    var afterWaitreadLock2 := u.ReadLocks;

    assert EqualSlice(u, spec, dim1, 0, u.dim1 - 4, shift) by {
      u.LemmaRepr2DUnchanged(oldRepr2D);
      reveal EqualSlice;
    }

    world.LemmaNoTagBeforeVacuous(rRightTag);
    LemmaBarrierOrder(world, rRightTag, n, nt, nx, ny, dim1, dim2, dx, dt);
    LemmaRelyPayloadSize(rRightTag, world.size, nx, ny, nt, dim1, dim2, dx, dt);

    reqRRight.Wait();

    assert EqualSlice(u, spec, dim1, (u.dim1 - 4), u.dim1, shift) by {
      LemmaRelyPayloadContent(rRightTag, world.size, nx, ny, nt, dim1, dim2, dx,
                              dt, spec, world.rank + 1, world.rank, n, step);
      assert RelyPayload(rRightTag, world.size, nx, ny, nt, dim1, dim2, dx, dt) 
          == ArrayOfReals2D.Flatten(spec, dim2)
              [((world.rank + 1) * step + 4) * dim2..
               ((world.rank + 1) * step + 8) * dim2];
      assert u.Repr[rRightFrom..rRightFrom+len] == 
        ArrayOfReals2D.Flatten(spec, dim2)
          [shift * dim2 +rRightFrom..shift * dim2 +rRightFrom+len] by {
        calc {
             shift * dim2 + rRightFrom;
          == (world.rank * step) * dim2 + (u.dim1 - 4) * dim2;
          == (world.rank * step) * dim2 + (step + 4) * dim2;
          == {LemmaMulIsDistributiveAddOtherWay
              (dim2, world.rank * step, step + 4);}
             (world.rank * step + step + 4) * dim2;
          == {LemmaMulIsDistributiveAddOtherWay(step, world.rank, 1);}
             ((world.rank + 1) * step + 4) * dim2;
        }
        calc {
             shift * dim2 + rRightFrom + len;
          == ((world.rank + 1) * step + 4) * dim2 + 4 * dim2;
          == {LemmaMulIsDistributiveAddOtherWay
              (dim2, ((world.rank + 1) * step + 4), 4);}
             ((world.rank + 1) * step + 8) * dim2;
        }
      }
      LemmaEqualWithPaddingFlattenConverse(u, spec, dim1, shift, u.dim1 - 4, 4, 
                                           rRightFrom, len);
    }

    assert EqualWithPadding(u, spec, dim1, dim2, 0, shift, 0) by {
      u.LemmaRepr2DPartiallyChanged(oldRepr2D, oldRepr, u.dim1 - 4, 4);
      reveal EqualWithPadding;
      reveal EqualSlice;
    }

    assert u.FreeToWrite(0, u.length) by {
      reveal ArrayOfReals2D.FreeToWriteStatic;
      reveal ArrayOfReals2D.FreeToReadStatic;
      ArrayOfReals2D.LemmaUpdateReadLockCancel(newestReadLock, sRightFrom, len);
      assert newestReadLock == afterWaitreadLock;
      ArrayOfReals2D.LemmaUpdateReadLockCancel(newerReadLock, sLeftFrom, len);
      assert newerReadLock == afterWaitreadLock2;
      ArrayOfReals2D.LemmaSetWriteLockCancel
        (oldWriteLock, oldReadLocks, rLeftFrom, len);
      assert oldWriteLock == u.WriteLock;
    }
  }

  method ExchangeBoundaryData
    (u:ArrayOfReals2D, world:MPI.World<real>, 
     nx:nat, ny:nat, nt:nat, dim1:nat, dim2:nat, dx:real, dt:real, n:nat)
    requires world.size > 1
    requires dim1 >= 9
    requires dim2 >= 9
    requires world.size > 1
    requires world.rank < world.size
    requires (dim1 - 8) % world.size == 0 
    requires (dim1 - 8) / world.size >= 4
    requires dx * dx != 0.0
    requires 0 <= world.rank      * ((dim1 - 8) / world.size) 
               < (world.rank + 1) * ((dim1 - 8) / world.size) <= dim1 - 8
    requires n <= nt
    requires u.IsValid()
    requires u.FreeToWrite(0, u.length)
    requires u.dim1 == (dim1 - 8) / world.size + 8
    requires u.dim2 == dim2
    requires 
      EqualWithPadding(u, 
        SpecOuterHelper(nt-n, nt, 
                      Spec.SpecInit(nx, ny, dim1, dim2), 
                      dim1, dim2, dx, dt), 
        dim1, dim2, 4, world.rank * ((dim1 - 8) / world.size), 0)
    requires world.BarrierID() == n
    requires n == 0 ==> world.Tag() == -1
    requires (n != 0 && world.rank != world.size - 1) 
      ==> world.Tag() == (n - 1) * 2 * (world.size - 1) + 2 * world.rank + 1
    requires (n != 0 && world.rank == world.size - 1) 
      ==> world.Tag() == (n - 1) * 2 * (world.size - 1) + 2 * world.rank - 1
    requires world.SendBuffer() == {}
    requires world.RecvBuffer() == {}
    requires !world.Finalized()
    requires world.RelyMess == ((tag:nat, size:nat) => 
        RelyPayload(tag, size, nx, ny, nt, dim1, dim2, dx, dt))
    requires world.RelySend == RelySender
    requires world.RelyRecv == RelyReceiver
    requires world.Barriers == ((id, size) => 
      Barriers(id, size, nt, nx, ny, dim1, dim2, dx, dt))
    requires world.LastBarrier == ((size:nat) => nt + 2)
    modifies u, world
    ensures u.IsValid()
    ensures u.FreeToWrite(0, u.length)
    ensures EqualWithPadding(u, 
      SpecOuterHelper(nt-n, nt, 
                      Spec.SpecInit(nx, ny, dim1, dim2), 
                      dim1, dim2, dx, dt), 
      dim1, dim2, 0, world.rank * ((dim1 - 8) / world.size), 0)
    ensures world.rank != world.size - 1
      ==> world.Tag() == n * 2 * (world.size - 1) + 2 * world.rank + 1 
    ensures world.rank == world.size - 1
      ==> world.Tag() == n * 2 * (world.size - 1) + 2 * world.rank - 1
    ensures world.SendBuffer() == {}
    ensures world.RecvBuffer() == {}
    ensures world.BarrierID() == n + 1
    ensures !world.Finalized()
  {
    ghost var step := (dim1 - 8) / world.size;
    ghost var shift := world.rank * step;
    ghost var spec := SpecOuterHelper(nt-n, nt, 
                      Spec.SpecInit(nx, ny, dim1, dim2), 
                      dim1, dim2, dx, dt);
    LemmaNoWriteLockBlockTrivial(u, 4, u.dim1 - 4, u.dim2 - 4, u.dim2);
    LemmaNoReadLockBlockTrivial(u, 4, u.dim1 - 4, u.dim2 - 4, u.dim2);
    Arrays2D.SetRange(u, 4, u.Dim1() - 4, u.Dim2() - 4, u.Dim2(), 0.0);
    assert EqualWithPadding(u, spec, |spec|, u.dim2, 4, shift, 0)
        && AllInRange(u, 4, u.dim1 - 4, u.dim2 - 4, u.dim2, 0.0) by {
      reveal Arrays2D.AllInRange;
      reveal Arrays2D.AllOutRange;
      reveal EqualWithPadding;
    }
    LemmaNoWriteLockBlockTrivial(u, 4, u.dim1 - 4, 0, 4);
    LemmaNoReadLockBlockTrivial(u, 4, u.dim1 - 4, 0, 4);
    Arrays2D.SetRange(u, 4, u.Dim1() - 4, 0, 4, 0.0);
    assert EqualSlice(u, spec, |spec|, 4, u.dim1 - 4, shift) by {
      reveal Arrays2D.AllInRange;
      reveal Arrays2D.AllOutRange;
      reveal EqualSlice;
      reveal EqualWithPadding;
      reveal BorderIsZero;
    }
    reveal ArrayOfReals2D.FreeToReadStatic;
    reveal ArrayOfReals2D.FreeToWriteStatic;
    if world.rank == 0 {
      ExchangeBoundaryDataP0(u, world, nx, ny, nt, dim1, dim2, dx, dt, n);
    } else if world.rank == world.size - 1 {
      ExchangeBoundaryDataPLast(u, world, nx, ny, nt, dim1, dim2, dx, dt, n);
    } else {
      ExchangeBoundaryDataPMiddle(u, world, nx, ny, nt, dim1, dim2, dx, dt, n);
    }
    assert world.BarriersFull(world.BarrierID() + 1) == 
           (n + 1) * 2 * (world.size - 1);
    LemmaOrder(world, world.BarriersFull(world.BarrierID() + 1), n + 1);
    assert world.BarriersFull(world.BarrierID() + 1) > world.Tag();
    world.Barrier(n);
  }

  ghost function ModuloIteration(tag:nat, size:nat):nat {
    if size <= 1 then 0 else tag % (2 * (size - 1))
  }

  ghost function Iteration(tag:nat, size:nat):nat 
    requires size > 1
  {
    assert size - 1 > 0;
    if size <= 1 then 0 else tag / (2 * (size - 1))
  }

  ghost function RelySender(tag:nat, size:nat):nat {
    (ModuloIteration(tag, size) + 1) / 2
    // Example. Let size == 4. Then 2 * (size - 1) == 6:
    // 0 => (0 % 6 + 1) / 2 == 0 (sends to 1)
    // 1 => (1 % 6 + 1) / 2 == 1 (sends to 0)
    // 2 => (2 % 6 + 1) / 2 == 1 (sends to 2)
    // 3 => (3 % 6 + 1) / 2 == 2 (sends to 1)
    // 4 => (4 % 6 + 1) / 2 == 2 (sends to 3)
    // 5 => (5 % 6 + 1) / 2 == 3 (sends to 2)
    // 6 => (6 % 6 + 1) / 2 == 0 (sends to 1)
    // 7 => (7 % 6 + 1) / 2 == 1 (sends to 0)
    // ...
  }

  ghost function RelyReceiver(tag:nat, size:nat):nat {
    ModuloIteration(tag, size) / 2 + (tag + 1) % 2
    // Example. Let size == 4. Then 2 * (size - 1) == 6:
    // 0 => (0 % 6) / 2 + (0 + 1) % 2 == 1 (receves from 0)
    // 1 => (1 % 6) / 2 + (1 + 1) % 2 == 0 (receves from 1)
    // 2 => (2 % 6) / 2 + (2 + 1) % 2 == 2 (receves from 1)
    // 3 => (3 % 6) / 2 + (3 + 1) % 2 == 1 (receves from 2)
    // 4 => (4 % 6) / 2 + (4 + 1) % 2 == 3 (receves from 2)
    // 5 => (5 % 6) / 2 + (5 + 1) % 2 == 2 (receves from 3)
    // 6 => (6 % 6) / 2 + (6 + 1) % 2 == 1 (receves from 0)
    // 7 => (7 % 6) / 2 + (7 + 1) % 2 == 0 (receves from 1)
    // ...
  }

  ghost predicate RelyPayloadConds
    (tag:nat, size:nat, nt:nat, dim1:nat, dim2:nat, dx:real)
  {
    && size > 1 && dx * dx != 0.0 && dim1 >= 9 && dim2 >= 9 
    && ((dim1 - 8) / size) >= 4 
    && Iteration(tag, size) <= nt 
    && RelySender(tag, size) < size 
    && RelyReceiver(tag, size) < size
    && RelySender(tag, size) != RelyReceiver(tag, size)
  }

  lemma LemmaRelyPayloadConds
    (tag:nat, size:nat, nt:nat, dim1:nat, dim2:nat, dx:real, 
     step:nat, sender:nat, receiver:nat) 
    requires sender == RelySender(tag, size)
    requires receiver == RelyReceiver(tag, size)
    requires RelyPayloadConds(tag, size, nt, dim1, dim2, dx)
    requires step == ((dim1 - 8) / size)
    ensures (receiver > sender) ==> ((sender + 1) * step + 4) * dim2 <= dim1 * dim2
    ensures (receiver > sender) ==> ((sender + 1) * step) * dim2 >= 0
    ensures (receiver <= sender) ==> (sender * step + 8) * dim2 <= dim1 * dim2
    ensures (receiver <= sender) ==> (sender * step + 4) * dim2 >= 0
  {
    if receiver > sender {
      assert (sender + 1) * step + 4 < dim1 by {
        calc {
          (sender + 1) * step;
          <= receiver * step;
          < {LemmaMulStrictInequality(receiver, size, step);}
            size * step;
          == step * size;
          == (dim1 - 8) / size * size;
          <= {LemmaRemainderLower(dim1 - 8, size);} 
          dim1 - 8;
        }
      }
      LemmaMulInequality((sender + 1) * step + 4, dim1, dim2);
    } else {
      calc {
        sender * step;
        < {LemmaMulStrictInequality(sender, size, step);}
           size * step;
        == step * size;
        == (dim1 - 8) / size * size;
        <= {LemmaRemainderLower(dim1 - 8, size);} dim1 - 8;
          dim1 - 8;
      }
      LemmaMulInequality((sender * step + 8), dim1, dim2);
    }
  }

  lemma LemmaRelyPayloadSize
    (tag:nat, size:nat, nx:nat, ny:nat, nt:nat, 
     dim1:nat, dim2:nat, dx:real, dt:real) 
    ensures |RelyPayload(tag, size, nx, ny, nt, dim1, dim2, dx, dt)| == 4 * dim2
  {
    reveal RelyPayload;
    var sender := RelySender(tag, size);
    var receiver := RelyReceiver(tag, size);
    if !RelyPayloadConds(tag, size, nt, dim1, dim2, dx) {
      assert RelyPayload(tag, size, nx, ny, nt, dim1, dim2, dx, dt)
          == seq(4 * dim2, i => 0.0);
      return;
    }
    var step := ((dim1 - 8) / size);
    LemmaRelyPayloadConds(tag, size, nt, dim1, dim2, dx, 
                                step, sender, receiver);
    var spec := SpecOuterHelper(nt, nt - Iteration(tag, size), 
            Spec.SpecInit(nx, ny, dim1, dim2), dim1, dim2, dx, dt);
    if receiver > sender {
    } else {
    }
  }

  lemma LemmaRelyPayloadContent
    (tag:nat, size:nat, nx:nat, ny:nat, nt:nat, dim1:nat, dim2:nat, dx:real, 
     dt:real, spec:seq<seq<real>>, sender:nat, receiver:nat, n:nat, step:nat) 
    requires RelyPayloadConds(tag, size, nt, dim1, dim2, dx)
    requires step == ((dim1 - 8) / size)
    requires n <= nt
    requires spec == SpecOuterHelper(nt - n, nt, 
      Spec.SpecInit(nx, ny, dim1, dim2), dim1, dim2, dx, dt)
    requires sender == RelySender(tag, size)
    requires receiver == RelyReceiver(tag, size)
    requires n == Iteration(tag, size)
    ensures (receiver > sender) ==> ((sender + 1) * step + 4) * dim2 <= dim1 * dim2
    ensures (receiver > sender) ==> ((sender + 1) * step) * dim2 >= 0
    ensures (receiver <= sender) ==> (sender * step + 8) * dim2 <= dim1 * dim2
    ensures (receiver <= sender) ==> (sender * step + 4) * dim2 >= 0
    ensures receiver > sender ==> 
      RelyPayload(tag, size, nx, ny, nt, dim1, dim2, dx, dt) ==
      ArrayOfReals2D.Flatten(spec, dim2)
            [((sender + 1) * step) * dim2..
             ((sender + 1) * step + 4) * dim2]
    ensures receiver <= sender ==> 
      RelyPayload(tag, size, nx, ny, nt, dim1, dim2, dx, dt) ==
      ArrayOfReals2D.Flatten(spec, dim2)
            [(sender * step + 4) * dim2..
             (sender * step + 8) * dim2]
  {
    LemmaRelyPayloadConds(tag, size, nt, dim1, dim2, dx, step, sender, receiver);
    reveal RelyPayload;
  }

  ghost function {:opaque} RelyPayload
    (tag:nat, size:nat, nx:nat, ny:nat, nt:nat, 
     dim1:nat, dim2:nat, dx:real, dt:real):seq<real> {
    var sender := RelySender(tag, size);
    var receiver := RelyReceiver(tag, size);
    if !RelyPayloadConds(tag, size, nt, dim1, dim2, dx)
    then seq(4 * dim2, i => 0.0) 
    else  var step := ((dim1 - 8) / size);
          LemmaRelyPayloadConds(tag, size, nt, dim1, dim2, dx, 
                                step, sender, receiver);
          var spec := SpecOuterHelper(nt - Iteration(tag, size), nt,
            Spec.SpecInit(nx, ny, dim1, dim2), dim1, dim2, dx, dt);
          if receiver > sender
          then ArrayOfReals2D.Flatten(spec, dim2)
            [((sender + 1) * step)     * dim2..((sender + 1) * step + 4) * dim2]
          else ArrayOfReals2D.Flatten(spec, dim2)
            [(sender *       step + 4) * dim2..(sender *       step + 8) * dim2]
  }

  ghost function Barriers
    (id:nat, size:nat, nt:nat, 
     nx:nat, ny:nat, dim1:nat, dim2:nat, dx:real, dt:real):BarrierKind<real> 
     requires dim1 >= 9
     requires dim2 >= 9
     requires dx * dx != 0.0
  {
    if id < nt + 1
    then MPI.BarrierKind.Simple(id * (if size == 0 then 0 else 2 * (size - 1)))
    else
        LemmaMulInequality(dim1-4, dim1, dim2);
        LemmaMulInequality(4, dim1 - 4, dim2);
        MPI.BarrierKind.Gather(
          0,
          ArrayOfReals2D.Flatten(
            Spec.Spec(nx, ny, nt, dim1, dim2, dx, dt), dim2)
            [4 * dim2..(dim1-4) * dim2],
          (nt + 1) * (if size == 0 then 0 else 2 * (size - 1)))
  }

  lemma LemmaGatherBarrierSpec(id:nat, size:nat, nt:nat, 
     nx:nat, ny:nat, dim1:nat, dim2:nat, dx:real, dt:real) 
    requires id >= nt + 1
    requires dim1 >= 9
    requires dim2 >= 9
    requires dx * dx != 0.0
    requires size > 1
    ensures Barriers(id, size, nt, nx, ny, dim1, dim2, dx, dt).Gather?
    ensures Barriers(id, size, nt, nx, ny, dim1, dim2, dx, dt).nextTag == 
       (nt + 1) * 2 * (size - 1)
    ensures Barriers(id, size, nt, nx, ny, dim1, dim2, dx, dt).root == 0
    ensures Barriers(id, size, nt, nx, ny, dim1, dim2, dx, dt).whole == 
      ArrayOfReals2D.Flatten(
        Spec.Spec(nx, ny, nt, dim1, dim2, dx, dt), dim2)
        [4 * dim2..(dim1-4) * dim2]
    ensures |Barriers(id, size, nt, nx, ny, dim1, dim2, dx, dt).whole| 
         == (dim1 - 8) * dim2
  {
    LemmaMulInequality(dim1-4, dim1, dim2);
    LemmaMulInequality(4, dim1 - 4, dim2);
  }

  lemma LemmaBarriersNotTooFarApart
    (size:nat, nt:nat, nx:nat, ny:nat, dim1:nat, dim2:nat, dx:real, dt:real) 
    requires 32767 / 2 > size
    requires dim1 >= 9
    requires dim2 >= 9
    requires dx * dx != 0.0
    ensures World.BarriersNotTooFarApart((id, size) => 
      Barriers(id, size, nt, nx, ny, dim1, dim2, dx, dt), size)
  {
    var BarriersTemp := (id, size) => 
      Barriers(id, size, nt, nx, ny, dim1, dim2, dx, dt);
    if size == 0 {
      assert forall i :: i > 0 ==> 
        BarriersTemp(i, size).nextTag - BarriersTemp(i - 1, size).nextTag == 0;
    } else {
      assert forall i :: i > 0 ==> 
        BarriersTemp(i, size).nextTag - 
        BarriersTemp(i-1, size).nextTag <= 2 * (size-1);
    }
  }

  method ParallelInit
    (nx:nat, ny:nat, dim1:nat, dim2:nat, size:nat, rank:nat) 
    returns (u:ArrayOfReals2D)
    requires dim1 >= 9
    requires dim2 >= 9
    requires size != 0
    requires (dim1 - 8) % size == 0 // 8 = 4 * 2 zero padding from both sides
    requires (dim1 - 8) / size >= 4 
    requires rank < size
    ensures 0 <= rank *      ((dim1 - 8) / size) 
              < (rank + 1) * ((dim1 - 8) / size) <= dim1 - 8
    ensures u.IsValid()
    ensures u.dim2 == dim2
    ensures u.dim1 == (dim1 - 8) / size + 8
    ensures u.Repr2D[4..u.dim1-4] == Spec.SpecInit(nx, ny, dim1, dim2)
                      [rank *      ((dim1 - 8) / size) + 4
                    ..(rank + 1) * ((dim1 - 8) / size) + 4]
    ensures fresh(u)
    ensures u.FreeToWrite(0, u.length)
  {
    calc {
      (rank + 1) * ((dim1 - 8) / size);
      <= {LemmaMulInequality(rank + 1, size, (dim1 - 8) / size);}
      size * ((dim1 - 8) / size);
      == {assert (dim1 - 8) % size == 0;}
      size * ((dim1 - 8) / size) + (dim1 - 8) % size;
      == {LemmaFundamentalDivMod(dim1 - 8, size);}
      dim1 - 8;
    }
    var spec := Spec.SpecInit(nx, ny, dim1, dim2)
                      [(rank *      ((dim1 - 8) / size)) + 4
                    ..((rank + 1) * ((dim1 - 8) / size)) + 4];
    assert |spec| == (dim1 - 8) / size;
    var padding := seq(4, i => seq(dim2, j => 0.0));
    u := Arrays2D.FromSeq(padding + spec + padding, (dim1 - 8)/size + 8, dim2);
  }

  lemma {:isolate_assertions} LemmaParallelGatherHelper
    (s1:seq<real>, s2:seq<real>, 
     dim1:nat, dim2:nat, step:nat, rank:nat, size:nat) 
    requires (step * rank) * dim2 + 4 * dim2 + step * dim2 
          <= dim1 * dim2 == |s2|
    requires s1 == s2[(step * rank) * dim2 + 4 * dim2..
                      (step * rank) * dim2 + 4 * dim2 + step * dim2]
    requires dim1 >= 9
    requires dim2 >= 9
    requires size > rank >= 0
    requires step == (dim1 - 8) / size
    requires (dim1 - 8) % size == 0
    ensures step * dim2 * (rank + 1) <= (dim1-8) * dim2
    ensures s1 == s2[4 * dim2..(dim1-4) * dim2]
                    [step * dim2 * rank..step * dim2 * (rank + 1)]
  {
    calc {
         step * dim2 * (rank + 1);
      <= {LemmaMulInequality(rank + 1, size, step * dim2);}
         step * dim2 * size;
      == dim2 * (size * ((dim1 - 8) / size));
      == {LemmaFundamentalDivMod(dim1 - 8, size);}
         dim2 * (dim1 - 8);
      == (dim1 - 8) * dim2;
    }
    if rank == 0 {
    } else {
      for i := 0 to |s1| 
        invariant s1[..i] == s2
          [4 * dim2..(dim1-4) * dim2]
          [step * dim2 * rank..step * dim2 * (rank + 1)][..i]
      {
        assert s1[i] == s2[(step * rank) * dim2 + 4 * dim2 + i];
      }
    }
  }

  method Parallel
    (nx:nat, ny:nat, nt:nat, dim1:nat, dim2:nat, dx:real, dt:real, size:nat) 
    returns (u:ArrayOfReals2D, world:MPI.World<real>) 
    requires 32767 / 2 > size > 1
    requires dim1 >= 9
    requires dim2 >= 9
    requires size != 0
    requires (dim1 - 8) % size == 0 // 8 = 4 * 2 zero padding from both sides
    requires (dim1 - 8) / size >= 4 
    requires dx * dx != 0.0
    ensures 0 <= world.rank *      ((dim1 - 8) / size) 
              < (world.rank + 1) * ((dim1 - 8) / size) <= dim1 - 8
    ensures world.rank == 0 
      ==> u.Repr2D == Spec.Spec(nx, ny, nt, dim1, dim2, dx, dt)
    ensures world.rank == 0 ==> u.dim1 == dim1
    ensures world.rank == 0 ==> u.dim2 == dim2
    ensures u.IsValid()
    ensures u.FreeToWrite(0, u.length)
    ensures world.Finalized()
  {
    LemmaBarriersNotTooFarApart(size, nt, nx, ny, dim1, dim2, dx, dt);
    world := new MPI.World<real>(
      size, 
      (tag:nat, size:nat) => 
        RelyPayload(tag, size, nx, ny, nt, dim1, dim2, dx, dt),
      RelySender,
      RelyReceiver,
      (id:nat, size:nat) => Barriers(id, size, nt, nx, ny, dim1, dim2, dx, dt),
      (size:nat) => nt + 2);
    var rank := world.rank;
    u := ParallelInit(nx, ny, dim1, dim2, size, rank);
    ghost var initial := Spec.SpecInit(nx, ny, dim1, dim2);
    var step := (dim1 - 8) / size;
    reveal SpecOuterHelper;
    LemmaEqualWithPaddingAlt
    (u, SpecOuterHelper(nt, nt, initial, dim1, dim2, dx, dt), 
     dim1, dim2, 4, step * rank, 0); 
    ExchangeBoundaryData(u, world, nx, ny, nt, dim1, dim2, dx, dt, 0);
    for n := 0 to nt 
      modifies u, world
      invariant u.dim1 == step + 8
      invariant u.dim2 == dim2
      invariant u.IsValid()
      invariant u.FreeToWrite(0, u.length)
      invariant EqualWithPadding(u, 
        SpecOuterHelper(nt-n, nt, 
                        Spec.SpecInit(nx, ny, dim1, dim2), 
                        dim1, dim2, dx, dt), 
        dim1, dim2, 0, rank * ((dim1 - 8) / world.size), 0)
      invariant world.BarrierID() == n + 1
      invariant (rank != size - 1) 
      ==> world.Tag() == n * 2 * (size - 1) + 2 * rank + 1 
      invariant (rank == size - 1) 
      ==> world.Tag() == n * 2 * (size - 1) + 2 * rank - 1
      invariant world.SendBuffer() == {}
      invariant world.RecvBuffer() == {}
      invariant !world.Finalized()
    {
      u := RK4Impl.RK4Step(u, 
        SpecOuterHelper(nt-n, nt, Spec.SpecInit(nx, ny, dim1, dim2), 
          dim1, dim2, dx, dt), 
        dim1, dim2, dx, dt, rank * ((dim1 - 8) / world.size), 0);
      ExchangeBoundaryData(u, world, nx, ny, nt, dim1, dim2, dx, dt, n + 1);
    }
    var part := u;
    calc {
      4 * dim2+(dim1 - 8) * dim2;
      == {LemmaMulIsDistributiveAddOtherWay(dim2, 4, dim1 - 8);}
      (dim1 - 8 + 4) * dim2;
      == (dim1 - 4) * dim2;
    }
    if (rank == 0) {
      u := new ArrayOfReals2D(dim1, dim2, 0.0);
      calc { 4 * dim2 + (dim1 - 8) * dim2;
        == (dim1 - 4) * dim2;
        <  {LemmaMulStrictInequality(dim1 - 4, dim1, dim2);}
           dim1 * dim2;
        == u.length; }
      calc { 4 * dim2 + (dim1 - 8) * dim2;
        == (dim1 - 4) * dim2;
        >= {LemmaMulStrictInequality(4, dim1 - 4, dim2);} 
           4 * dim2; }
      u.LemmaFreeToWriteNarrower(4 * dim2, 4 * dim2 + (dim1 - 8) * dim2);
    }
    assert world.BarrierID() + 1 == nt + 2;
    LemmaGatherBarrierSpec(nt + 2, size, nt, nx, ny, dim1, dim2, dx, dt);
    LemmaOrder(world, world.BarriersFull(world.BarrierID() + 1), nt + 1);
    calc {
      4 * dim2 + step * dim2;
      == {LemmaMulIsDistributiveAddOtherWay(dim2, 4, step);}
        (4 + step) * dim2;
      < {LemmaMulStrictInequality(4 + step, step + 8, dim2);}
        (step + 8) * dim2;
      == part.dim1 * part.dim2;
      == part.length;
    }
    assert part.FreeToRead(4 * dim2, 4 * dim2 + step * dim2) by {
      part.LemmaFreeToWriteNarrower(4 * dim2, 4 * dim2 + step * dim2);
      part.LemmaFreeToWriteStronger(4 * dim2, 4 * dim2 + step * dim2);
    }
    calc {
      (step * dim2) * size;
      == {LemmaMulIsCommutative(step, dim2);
          LemmaMulIsAssociative(dim2, step, size);}
         dim2 * (step * size);
      == {LemmaMulIsCommutative(step, size);}
         dim2 * (size * step);
      == dim2 * (size * ((dim1 - 8) / size));
      == {assert (dim1 - 8) % size == 0;
          LemmaFundamentalDivMod(dim1 - 8, size);
          assert (dim1 - 8) == size * ((dim1 - 8) / size);}
         dim2 * (dim1 - 8);
      == {LemmaMulIsCommutative(dim2, dim1 - 8);}
         (dim1 - 8) * dim2;
    }
    assert EqualSlice(part, 
      Spec.Spec(nx, ny, nt, dim1, dim2, dx, dt), 
      dim1, 4, part.dim1 - 4, step * rank) by {
      reveal EqualSlice;
      reveal EqualWithPadding;
      reveal Spec.Spec;
    }
    LemmaEqualWithPaddingFlatten(part, 
      Spec.Spec(nx, ny, nt, dim1, dim2, dx, dt), dim1, step * rank, 4, step, 4);
    LemmaParallelGatherHelper(
      part.Repr[4 * dim2..4 * dim2 + step * dim2], 
      u.Flatten(Spec.Spec(nx, ny, nt, dim1, dim2, dx, dt), dim2),
      dim1, dim2, step, rank, size);
    LemmaMulInequality(rank+1, size, step * dim2);
    var oldRepr2D := u.Repr2D;
    var oldRepr := u.Repr;
    world.Gather(0, part, u, 4 * dim2, step * dim2, 4 * dim2, (dim1 - 8) * dim2, nt + 1);
    if rank == 0 {
      LemmaEqualWithPaddingFlattenConverse(
        u, Spec.Spec(nx, ny, nt, dim1, dim2, dx, dt),
        dim1, 0, 4, dim1 - 8, 4 * dim2,  (dim1 - 8) * dim2);
      u.LemmaRepr2DPartiallyChanged(oldRepr2D, oldRepr, 4, (dim1 - 8));
      reveal BorderIsZero;
      reveal EqualSlice;
      assert forall i :: 0 <= i < dim1 ==> u.Repr2D[i] == Spec.Spec(nx, ny, nt, dim1, dim2, dx, dt)[i];
    }
  }
}