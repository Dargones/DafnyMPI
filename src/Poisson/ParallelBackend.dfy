include "../DafnyMPI/Externs/MPI.dfy"
include "../DafnyMPI/Externs/MPIResource.dfy"
include "../DafnyMPI/Arrays2D.dfy"
include "../DafnyMPI/Utils.dfy"
include "Spec.dfy"
include "Shared.dfy"

module ParallelBackend {

  import opened Arrays2D
  import opened MPIResource
  import opened Spec
  import opened MPI
  import opened Std.Arithmetic.DivMod
  import opened Std.Arithmetic.Mul
  import opened Utils
  import opened Shared

  lemma LemmaBarrierOrder
    (world:MPI.World<real>, high:nat, n:nat, maxIts:nat, cNumber:nat, N:nat,
     tol:real, F:(int, int) -> real) 
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
    requires n < cNumber <= maxIts
    requires N >= 3
    requires (N - 2) / world.size >= 1
    requires (world.Barriers == (id:nat, size:nat) => 
        Barriers(id, size, maxIts, cNumber, N, RhsInit(N, F), tol))
    ensures world.Barriers(n, world.size).nextTag <= high < world.Barriers(n + 1, world.size).nextTag
  {
    reveal Barriers;
    LemmaBarrierId(world, maxIts, cNumber, N, tol, F, n);
    LemmaBarrierId(world, maxIts, cNumber, N, tol, F, n+1);
    assert high < n * 2 * (world.size - 1) + 2 * (world.size - 1);
    calc {
        high;
        <  n * 2 * (world.size - 1) + 2 * (world.size - 1);
        == {LemmaMulIsDistributiveAddOtherWay(2 * (world.size - 1), n ,1);}
           (n+1) * 2 * (world.size - 1);
        == world.Barriers(n + 1, world.size).nextTag;}
  }

  lemma LemmaRTagRight(n:nat, size:nat, rtag:int, rank:nat) 
    requires size > 1
    requires rank < size - 1
    requires rtag == n * 2 * (size - 1) + 2 * rank + 1
    ensures rtag >= 0
    ensures RelySender(rtag, size) == rank + 1
    ensures RelyReceiver(rtag, size) == rank
    ensures Iteration(rtag, size) == n + 1
  {
    LemmaFundamentalDivModConverse(rtag, 2 * (size - 1), n, 2 * rank + 1);
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

  lemma LemmaSTagRight(n:nat, size:nat, stag:nat, rank:nat) 
    requires size > 1
    requires rank < size - 1
    requires stag == n * 2 * (size - 1) + 2 * rank
    ensures stag >= 0
    ensures RelySender(stag, size) == rank
    ensures RelyReceiver(stag, size) == rank + 1
    ensures Iteration(stag, size) == n + 1
  {
    LemmaFundamentalDivModConverse(stag, 2 * (size - 1), n, 2 * rank);
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

  lemma LemmaRTagLeft(n:nat, size:nat, rtag:int, rank:nat) 
    requires size > 1
    requires 0 < rank < size
    requires rtag == n * 2 * (size - 1) + 2 * rank - 2
    ensures rtag >= 0
    ensures RelySender(rtag, size) == rank - 1
    ensures RelyReceiver(rtag, size) == rank
    ensures Iteration(rtag, size) == n + 1
  {
    LemmaFundamentalDivModConverse(rtag, 2 * (size - 1), n, 
                                           2 * rank - 2);
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
    ensures Iteration(rtag, size) == n + 1
  {
    LemmaFundamentalDivModConverse(rtag, 2 * (size - 1), n, 
                                           2 * rank - 1);
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

  lemma {:isolate_assertions} LemmaOnSend
    (u:ArrayOfReals2D, size:nat, cNumber:nat, nt:nat, n:nat, N:nat,
     tolerance:real, F: (int, int) -> real, spec:seq<seq<real>>, tag:nat,
     receiver:nat, sender:nat, step:nat, sfrom:nat) 
    requires N >= 3
    requires n < cNumber <= nt
    requires spec == SpecOuterHelperWithConvergence
        (nt-n-1, nt, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0
    requires u.IsValid()
    requires size > 1
    requires step == (N - 2) / size
    requires u.dim1 == step + 2
    requires (N - 2) % size == 0 
    requires (N - 2) / size >= 1
    requires u.IsValid()
    requires u.dim2 == N
    requires N >= u.dim1 + step * sender
    requires EqualSlice(u, spec, N, 1, u.dim1 - 1, sender * step)
    requires receiver == RelyReceiver(tag, size)
    requires sender == RelySender(tag, size)
    requires Iteration(tag, size) == n + 1
    requires sender == receiver + 1 || receiver == sender + 1
    requires receiver > sender ==> sfrom == (u.Dim1() - 2) * u.Dim2()
    requires receiver <= sender ==> sfrom == u.Dim2()
    ensures RelyPayload(tag, size, nt, N, RhsInit(N, F), tolerance) 
         == u.Repr[sfrom..sfrom+u.Dim2()]
  {
    reveal RelyPayload;
    u.LemmaRepr2DtoRepr();
    if receiver > sender {
      assert forall i, j :: 
        u.dim1 - 2 <= i < u.dim1 - 1 && 0 <= j < N ==> (u.Repr2D[i][j] 
        == u.Repr[sfrom..sfrom+u.Dim2()][j]);
      assert u.Repr[sfrom..sfrom+u.Dim2()] == u.Repr2D[u.dim1 - 2];
      assert u.Repr2D[u.dim1 - 2] == spec[sender * step + u.dim1 - 2] by {
        reveal EqualSlice;
      }
      assert RelyPayload(tag, size, nt, N, RhsInit(N, F), tolerance) 
         == spec[(sender + 1) * step];
    } else {
      assert forall i, j :: 
        1 <= i < 2 && 0 <= j < N ==> (u.Repr2D[i][j] 
        == u.Repr[sfrom..sfrom+u.Dim2()][j]);
      assert u.Repr[sfrom..sfrom+u.Dim2()] == u.Repr2D[1];
       assert u.Repr2D[1] == spec[sender * step + 1] by {
        reveal EqualSlice;
      }
      assert RelyPayload(tag, size, nt, N, RhsInit(N, F), tolerance) 
          == spec[sender * step + 1];
    }
  }

  lemma {:isolate_assertions} LemmaOnRecv
    (u:ArrayOfReals2D, size:nat, cNumber:nat, nt:nat, n:nat, N:nat,
     tolerance:real, F: (int, int) -> real, spec:seq<seq<real>>, tag:nat,
     receiver:nat, sender:nat, step:nat, rfromMin:nat, rfrom:nat) 
    requires N >= 3
    requires n < cNumber <= nt
    requires spec == SpecOuterHelperWithConvergence
        (nt-n-1, nt, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0
    requires u.IsValid()
    requires size > 1
    requires step == (N - 2) / size
    requires u.dim1 == step + 2
    requires (N - 2) % size == 0 
    requires (N - 2) / size >= 1
    requires u.IsValid()
    requires u.dim2 == N
    requires N >= u.dim1 + step * receiver
    requires receiver == RelyReceiver(tag, size)
    requires sender == RelySender(tag, size)
    requires Iteration(tag, size) == n + 1
    requires sender == receiver + 1 || receiver == sender + 1
    requires receiver > sender ==> rfromMin == 0
    requires receiver <= sender ==> rfromMin == (u.Dim1() - 1)
    requires rfrom == rfromMin * u.Dim2()
    requires RelyPayload(tag, size, nt, N, RhsInit(N, F), tolerance) 
         == u.Repr[rfrom..rfrom+u.Dim2()]
    ensures EqualSlice(u, spec, N, rfromMin, rfromMin + 1, receiver * step)
  {
    reveal RelyPayload;
    u.LemmaRepr2DtoRepr();
    if receiver > sender {
      assert forall i, j :: 
        0 <= i < 1 && 0 <= j < N ==> (u.Repr2D[i][j] 
        == u.Repr[rfrom..rfrom+u.Dim2()][j]);
      assert u.Repr[rfrom..rfrom+u.Dim2()] == u.Repr2D[0];
      // assert u.Repr2D[0] == spec[receiver * step] by {
      //   reveal EqualSlice;
      // }
      assert RelyPayload(tag, size, nt, N, RhsInit(N, F), tolerance) 
         == spec[(sender + 1) * step];
      assert u.Repr2D[0] == spec[receiver * step];
      reveal EqualSlice;
      assert EqualSlice(u, spec, N, 0, 1, receiver * step);
      return;
    } else {
      assert forall i, j :: 
        u.dim1 - 1 <= i < u.dim1 && 0 <= j < N ==> (u.Repr2D[i][j] 
        == u.Repr[rfrom..rfrom+u.Dim2()][j]);
      assert u.Repr[rfrom..rfrom+u.Dim2()] == u.Repr2D[u.dim1 - 1];
      // assert u.Repr2D[u.dim1 - 1] == spec[receiver * step + (u.dim1 - 1)] by {
      //   reveal EqualSlice;
      // }
      assert RelyPayload(tag, size, nt, N, RhsInit(N, F), tolerance) 
          == spec[sender * step + 1];
      assert u.Repr2D[u.dim1 - 1] == spec[sender * step + 1];
      calc {
        sender * step + 1;
        == (receiver + 1) * step + 1;
        == {LemmaMulIsDistributiveAddOtherWay(step, receiver, 1);}
           receiver * step + step + 1;
        == receiver * step + u.dim1 - 1;
      }
      reveal EqualSlice;
      assert EqualSlice(u, spec, N, u.dim1 - 1, u.dim1, receiver * step);
      return;
    }
  }

  method ExchangeBoundaryDataP0
    (u:ArrayOfReals2D, world:MPI.World<real>, ghost cNumber:nat,
     nt:nat, n:nat, N:nat, tolerance:real, F: (int, int) -> real) 
    requires world.size > 1
    requires N >= 3
    requires world.rank == 0
    requires (N - 2) % world.size == 0 
    requires (N - 2) / world.size >= 1
    requires n < cNumber <= nt
    requires u.IsValid()
    requires u.FreeToWrite(0, u.length)
    requires u.dim1 == (N - 2) / world.size + 2
    requires N >= u.dim1
    requires u.dim2 == N
    requires EqualSlice(u, 
      SpecOuterHelperWithConvergence
        (nt-n-1, nt, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0, 
      N, 1, u.dim1 - 1, 0)
    requires world.BarrierID() == n
    requires n == 0 ==> world.Tag() == -1
    requires (n != 0) ==> world.Tag() == (n - 1) * 2 * (world.size - 1) + 1
    requires world.SendBuffer() == {}
    requires world.RecvBuffer() == {}
    requires !world.Finalized()
    requires world.RelyMess == ((tag:nat, size:nat) => 
      RelyPayload(tag, size, nt, N, RhsInit(N, F), tolerance))
    requires world.RelySend == RelySender
    requires world.RelyRecv == RelyReceiver
    requires world.Barriers == ((id:nat, size:nat) => 
        Barriers(id, size, nt, cNumber, N, RhsInit(N, F), tolerance))
    modifies u, world
    ensures u.IsValid()
    ensures u.FreeToWrite(0, u.length)
    ensures EqualWithPadding(u, 
      SpecOuterHelperWithConvergence
        (nt-n-1, nt, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0,
      N, N, 0, 0, 0)
    ensures world.Tag() == n * 2 * (world.size - 1) + 1 
    ensures world.SendBuffer() == {}
    ensures world.RecvBuffer() == {}
    ensures world.BarrierID() == n
    ensures !world.Finalized()
  {
    ghost var spec := SpecOuterHelperWithConvergence
        (nt-n-1, nt, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0;
    ghost var step := (N - 2) / world.size;
    LemmaNoWriteLockBlockTrivial(u, 0, 1, 0, u.dim2);
    LemmaNoReadLockBlockTrivial(u, 0, 1, 0, u.dim2);
    Arrays2D.SetRange(u, 0, 1, 0, u.Dim2(), 0.0);
    assert EqualSlice(u, spec, N, 1, u.dim1 - 1, 0)
        && AllInRange(u, 0, 1, 0, u.dim2, 0.0) by {
      reveal Arrays2D.AllInRange;
      reveal Arrays2D.AllOutRange;
      reveal EqualSlice;
    }
    ghost var oldRepr2D := u.Repr2D;

    var rtag := n * 2 * (world.size - 1) + 1;
    var rfrom := (u.Dim1() - 1) * u.Dim2();
    var len := u.Dim2();
    LemmaRTagRight(n, world.size, rtag, 0);
    var stag := n * 2 * (world.size - 1);
    var sfrom := (u.Dim1() - 2) * u.Dim2();
    LemmaSTagRight(n, world.size, stag, 0);
    ghost var oldWriteLock := u.WriteLock;
    u.LemmaFreeToWriteStronger(0, u.length);
    u.LemmaFreeToReadNarrower(sfrom, sfrom + len);

    u.LemmaFreeToWriteNarrower(rfrom, rfrom + len);
    var req := world.IRecv(u, rfrom, len, 1, rtag);
    u.LemmaRepr2DUnchanged(oldRepr2D);
    assert EqualSlice(u, spec, N, 1, u.dim1 - 1, 0)
        && AllInRange(u, 0, 1, 0, u.dim2, 0.0) by {
      reveal Arrays2D.AllInRange;
      reveal EqualSlice;
    }

    assert u.FreeToRead(sfrom, sfrom+len) by {
      assert ArrayOfReals2D.FreeToReadStatic
        (oldWriteLock, u.length, sfrom, sfrom + len) ;
      ArrayOfReals2D.LemmaWriteNonOverlapping
        (oldWriteLock, u.WriteLock, u.ReadLocks, rfrom, rfrom+len, 
        sfrom, sfrom+len, u.length);
    }
    assert world.RelyMessFull(stag) == u.Repr[sfrom..sfrom+len] by {
      LemmaOnSend(u, world.size, cNumber, nt, n, N, tolerance, F, spec, stag,
                  1, 0, step, sfrom);
    }
    LemmaOrder(world, stag, n);
    LemmaBarrierOrder(world, stag, n, nt, cNumber, N, tolerance, F);
    world.Send(u, sfrom, len, 1, stag);
    u.LemmaRepr2DUnchanged(oldRepr2D);
    ghost var oldRepr := u.Repr;
    assert EqualSlice(u, spec, N, 1, u.dim1 - 1, 0)
        && AllInRange(u, 0, 1, 0, u.dim2, 0.0) by {
      reveal Arrays2D.AllInRange;
      reveal EqualSlice;
    }
    
    world.LemmaNoTagBeforeVacuous(rtag);
    LemmaBarrierOrder(world, rtag, n, nt, cNumber, N, tolerance, F);
    LemmaRelyPayloadSize(rtag, world.size, nt, N, RhsInit(N, F), tolerance);
    req.Wait();

    assert EqualSlice(u, spec, N, (u.dim1 - 1), u.dim1, 0) by {
      LemmaOnRecv(u, world.size, cNumber, nt, n, N, tolerance, F, spec, rtag,
                  0, 1, step, u.dim1 - 1, rfrom);
    }

    assert EqualWithPadding(u, spec, N, N, 0, 0, 0) by {
      u.LemmaRepr2DPartiallyChanged(oldRepr2D, oldRepr, u.dim1 - 1, 1);
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

  method {:isolate_assertions} ExchangeBoundaryDataPLast
    (u:ArrayOfReals2D, world:MPI.World<real>, ghost cNumber:nat,
     nt:nat, n:nat, N:nat, tolerance:real, F: (int, int) -> real) 
    requires world.size > 1
    requires N >= 3
    requires world.rank == world.size - 1
    requires (N - 2) % world.size == 0 
    requires (N - 2) / world.size >= 1
    requires n < cNumber <= nt
    requires u.IsValid()
    requires u.FreeToWrite(0, u.length)
    requires u.dim1 == (N - 2) / world.size + 2
    requires N >= u.dim1 + ((N - 2) / world.size) * world.rank
    requires u.dim2 == N
    requires ((N - 2) / world.size) * world.rank >= 0
    requires EqualSlice(u, 
      SpecOuterHelperWithConvergence
        (nt-n-1, nt, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0, 
      N, 1, u.dim1 - 1, world.rank * ((N - 2) / world.size))
    requires world.BarrierID() == n
    requires n == 0 ==> world.Tag() == -1
    requires n != 0 
      ==> world.Tag() == (n - 1) * 2 * (world.size - 1) + 2 * world.rank - 1
    requires world.SendBuffer() == {}
    requires world.RecvBuffer() == {}
    requires !world.Finalized()
    requires world.RelyMess == ((tag:nat, size:nat) => 
      RelyPayload(tag, size, nt, N, RhsInit(N, F), tolerance))
    requires world.RelySend == RelySender
    requires world.RelyRecv == RelyReceiver
    requires world.Barriers == ((id:nat, size:nat) => 
        Barriers(id, size, nt, cNumber, N, RhsInit(N, F), tolerance))
    modifies u, world
    ensures u.IsValid()
    ensures u.FreeToWrite(0, u.length)
    ensures EqualWithPadding(u, 
      SpecOuterHelperWithConvergence
        (nt-n-1, nt, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0,
      N, N, 0, ((N - 2) / world.size) * world.rank, 0)
    ensures world.Tag() == n * 2 * (world.size - 1) + 2 * world.rank - 1
    ensures world.SendBuffer() == {}
    ensures world.RecvBuffer() == {}
    ensures world.BarrierID() == n
    ensures !world.Finalized()
  {
    ghost var step := (N - 2) / world.size;
    ghost var shift := (world.size - 1) * step;
    ghost var spec :=  SpecOuterHelperWithConvergence
        (nt-n-1, nt, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0;
    LemmaNoWriteLockBlockTrivial(u, u.dim1 - 1, u.dim1, 0, u.dim2);
    LemmaNoReadLockBlockTrivial(u, u.dim1 - 1, u.dim1, 0, u.dim2);
    Arrays2D.SetRange(u, u.Dim1() - 1, u.Dim1(), 0, u.Dim2(), 0.0);
    assert EqualSlice(u, spec, N, 1, u.dim1 - 1, shift)
        && AllInRange(u, u.dim1 - 1, u.dim1, 0, u.dim2, 0.0) by {
      reveal Arrays2D.AllInRange;
      reveal Arrays2D.AllOutRange;
      reveal EqualSlice;
    }
    ghost var oldRepr2D := u.Repr2D;

    var rtag := n * 2 * (world.size - 1) + 2 * (world.size - 1) - 2;
    var rfrom := 0;
    var len := u.Dim2();
    LemmaRTagLeft(n, world.size, rtag, world.size-1);
    var stag := n * 2 * (world.size - 1) + 2 * (world.size - 1) - 1;
    var sfrom := u.Dim2();
    LemmaSTagLeft(n, world.size, stag, world.size-1);
    ghost var oldWriteLock := u.WriteLock;
    ghost var oldReadLocks := u.ReadLocks;
  
    u.LemmaFreeToWriteStronger(0, u.length);
    u.LemmaFreeToReadNarrower(sfrom, sfrom + len);
    u.LemmaFreeToWriteNarrower(rfrom, rfrom + len);

    assert world.RelyMessFull(stag) == u.Repr[sfrom..sfrom+len] by {
      LemmaOnSend(u, world.size, cNumber, nt, n, N, tolerance, F, spec, stag,
                  world.size - 2, world.size - 1, step, sfrom);
    }
    
    var req := world.ISend(u, sfrom, len, world.size - 2, stag);
    u.LemmaRepr2DUnchanged(oldRepr2D);
    assert EqualSlice(u, spec, N, 1, u.dim1 - 1, shift)
        && AllInRange(u, u.dim1 - 1, u.dim1, 0, u.dim2, 0.0) by {
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
    LemmaBarrierOrder(world, rtag, n, nt, cNumber, N, tolerance, F);
    LemmaRelyPayloadSize(rtag, world.size, nt, N, RhsInit(N, F), tolerance);
    var oldRepr := u.Repr;
    
    world.Recv(u, rfrom, len, world.size - 2, rtag);

    assert EqualSlice(u, spec, N, 0, 1, shift) by {
      LemmaOnRecv(u, world.size, cNumber, nt, n, N, tolerance, F, spec, rtag,
                  world.size - 1, world.size - 2, step, 0, rfrom);
    }

    assert EqualWithPadding(u, spec, N, N, 0, shift, 0) by { 
      calc {
        0 * u.dim2 + 1 * u.dim2;
        == u.dim2;
        <= {LemmaMulInequality(1, u.dim2, u.dim2);}
        |oldRepr|;
      } 
      u.LemmaRepr2DPartiallyChanged(oldRepr2D, oldRepr, 0, 1);
      reveal EqualSlice;
      reveal EqualWithPadding;
      reveal Spec.BorderIsZero;
      reveal Arrays2D.AllInRange;
    }
    oldRepr2D := u.Repr2D;
    
    world.LemmaNoTagBeforeVacuous(stag);
    LemmaBarrierOrder(world, stag, n, nt, cNumber, N, tolerance, F);
    req.Wait();

    assert EqualWithPadding(u, spec, N, N, 0, shift, 0) by {
      u.LemmaRepr2DUnchanged(oldRepr2D);
      reveal EqualWithPadding;
    }

    assert u.FreeToWrite(0, u.length) by {
      ArrayOfReals2D.LemmaUpdateReadLockCancel(oldReadLocks, rfrom, len);
      reveal ArrayOfReals2D.FreeToWriteStatic;
    }
  }

  method {:isolate_assertions} ExchangeBoundaryDataPMid
    (u:ArrayOfReals2D, world:MPI.World<real>, ghost cNumber:nat,
     nt:nat, n:nat, N:nat, tolerance:real, F: (int, int) -> real) 
    requires world.size > 1
    requires N >= 3
    requires 0 < world.rank < world.size - 1
    requires (N - 2) % world.size == 0 
    requires (N - 2) / world.size >= 1
    requires n < cNumber <= nt
    requires u.IsValid()
    requires u.FreeToWrite(0, u.length)
    requires u.dim1 == (N - 2) / world.size + 2
    requires N >= u.dim1 + ((N - 2) / world.size) * world.rank
    requires u.dim2 == N
    requires EqualSlice(u, 
      SpecOuterHelperWithConvergence
        (nt-n-1, nt, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0, 
      N, 1, u.dim1 - 1, world.rank * ((N - 2) / world.size))
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
      RelyPayload(tag, size, nt, N, RhsInit(N, F), tolerance))
    requires world.RelySend == RelySender
    requires world.RelyRecv == RelyReceiver
    requires world.Barriers == ((id:nat, size:nat) => 
        Barriers(id, size, nt, cNumber, N, RhsInit(N, F), tolerance))
    modifies u, world
    ensures u.IsValid()
    ensures u.FreeToWrite(0, u.length)
    ensures EqualWithPadding(u, 
      SpecOuterHelperWithConvergence
        (nt-n-1, nt, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0,
      N, N, 0, ((N - 2) / world.size) * world.rank, 0)
    ensures world.rank != world.size - 1
      ==> world.Tag() == n * 2 * (world.size - 1) + 2 * world.rank + 1 
    ensures world.rank == world.size - 1
      ==> world.Tag() == n * 2 * (world.size - 1) + 2 * world.rank - 1
    ensures world.SendBuffer() == {}
    ensures world.RecvBuffer() == {}
    ensures world.BarrierID() == n
    ensures !world.Finalized()
  {
    ghost var step := (N - 2) / world.size;
    ghost var shift := world.rank * step;
    ghost var spec := SpecOuterHelperWithConvergence
        (nt-n-1, nt, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0;
    ghost var oldRepr2D := u.Repr2D;
    ghost var oldWriteLock := u.WriteLock;
    ghost var oldReadLocks := u.ReadLocks;
    ghost var oldRepr := u.Repr;

    // Tags for communication with the process on the left:
    var len := u.Dim2();
    var rLeftTag := n * 2 * (world.size - 1) + 2 * world.rank - 2;
    var rLeftFrom := 0;
    LemmaRTagLeft(n, world.size, rLeftTag, world.rank);
    var sLeftTag := n * 2 * (world.size - 1) + 2 * world.rank - 1;
    var sLeftFrom := u.Dim2();
    LemmaSTagLeft(n, world.size, sLeftTag, world.rank);

    // Tags for communication with the process on the right:
    var sRightTag := n * 2 * (world.size - 1) + 2 * world.rank;
    var sRightFrom := (u.Dim1() - 2) * u.Dim2();
    LemmaSTagRight(n, world.size, sRightTag, world.rank);

    var rRightTag := n * 2 * (world.size - 1) + 2 * world.rank +1;
    var rRightFrom := (u.Dim1() - 1) * u.Dim2();
    LemmaRTagRight(n, world.size, rRightTag, world.rank);

    u.LemmaFreeToWriteStronger(0, u.length);
    u.LemmaFreeToReadNarrower(sLeftFrom, sLeftFrom + len);
    u.LemmaFreeToWriteNarrower(rLeftFrom, rLeftFrom + len);
    u.LemmaFreeToReadNarrower(sRightFrom, sRightFrom + len);
    u.LemmaFreeToWriteNarrower(rRightFrom, rRightFrom + len);

    LemmaRelyPayloadSize(rLeftTag, world.size, nt, N, RhsInit(N, F), tolerance);
    
    var reqRRight := world.IRecv(u, rRightFrom, len, world.rank + 1, rRightTag);
    
    assert EqualSlice(u, spec, N, 1, u.dim1 - 1, shift) by {
      u.LemmaRepr2DUnchanged(oldRepr2D);
      reveal EqualSlice;
    }

    assert world.RelyMessFull(sRightTag) == 
           u.Repr[sRightFrom..sRightFrom+len] by {
      LemmaOnSend(u, world.size, cNumber, nt, n, N, tolerance, F, spec, 
                  sRightTag, world.rank + 1, world.rank, step, sRightFrom);
    }

    assert u.FreeToRead(sLeftFrom, sLeftFrom+len)
        && u.FreeToRead(sRightFrom, sRightFrom+len)
        && u.FreeToWrite(rLeftFrom, rLeftFrom+len) by {
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
        == u.Dim2();
        <= {LemmaMulInequality(1, u.Dim1() - 2, u.Dim2());}
           (u.Dim1() - 2) * u.Dim2(); 
        == sRightFrom;
      }
      ArrayOfReals2D.LemmaReadNonOverlapping
        (newerReadLock, u.ReadLocks, u.WriteLock, sRightFrom, sRightFrom+len, 
        rLeftFrom, rLeftFrom+len, u.length, 1);
    }

    assert EqualSlice(u, spec, N, 1, u.dim1 - 1, shift) by {
      u.LemmaRepr2DUnchanged(oldRepr2D);
      reveal EqualSlice;
    }

    assert world.RelyMessFull(sLeftTag) == 
           u.Repr[sLeftFrom..sLeftFrom+len] by {
      LemmaOnSend(u, world.size, cNumber, nt, n, N, tolerance, F, spec, 
                  sLeftTag, world.rank - 1, world.rank, step, sLeftFrom);
    }

    var newestReadLock := u.ReadLocks;
    
    var reqSLeft := world.ISend(u, sLeftFrom, len, world.rank - 1, sLeftTag);

    assert EqualSlice(u, spec, N, 1, u.dim1 - 1, shift) by {
      u.LemmaRepr2DUnchanged(oldRepr2D);
      reveal EqualSlice;
    }

    assert u.FreeToWrite(rLeftFrom, rLeftFrom+len) by {
      ArrayOfReals2D.LemmaReadNonOverlapping
        (newestReadLock, u.ReadLocks, u.WriteLock, sLeftFrom, sLeftFrom+len, 
        rLeftFrom, rLeftFrom+len, u.length, 1);
    }

    LemmaOrder(world, rLeftTag, n);
    LemmaBarrierOrder(world, rLeftTag, n, nt, cNumber, N, tolerance, F);
    LemmaRelyPayloadSize(rLeftTag, world.size, nt, N, RhsInit(N, F), tolerance);

    world.Recv(u, rLeftFrom, len, world.rank - 1, rLeftTag);
    
    assert EqualSlice(u, spec, N, 0, 1, shift) by {
      LemmaOnRecv(u, world.size, cNumber, nt, n, N, tolerance, F, spec, 
                  rLeftTag, world.rank, world.rank - 1, step, 0, rLeftFrom);
    }

    assert EqualSlice(u, spec, N, 0, u.dim1 - 1, shift) by {
      calc {
        0 * u.dim2 + 1 * u.dim2;
        == u.dim2;
        <= {LemmaMulInequality(1, u.dim2, u.dim2);}
        |oldRepr|;
      } 
      u.LemmaRepr2DPartiallyChanged(oldRepr2D, oldRepr, 0, 1);
      reveal EqualSlice;
    }

    oldRepr2D := u.Repr2D;
    oldRepr := u.Repr;
    
    world.LemmaNoTagBeforeVacuous(sLeftTag);
    LemmaBarrierOrder(world, sLeftTag, n, nt, cNumber, N, tolerance, F);
    reqSLeft.Wait();

    var afterWaitreadLock := u.ReadLocks;

    assert EqualSlice(u, spec, N, 0, u.dim1 - 1, shift) by {
      u.LemmaRepr2DUnchanged(oldRepr2D);
      reveal EqualSlice;
    }

    world.LemmaNoTagBeforeVacuous(sRightTag);
    LemmaBarrierOrder(world, sRightTag, n, nt, cNumber, N, tolerance, F);
    reqSRight.Wait();

    var afterWaitreadLock2 := u.ReadLocks;

    assert EqualSlice(u, spec, N, 0, u.dim1 - 1, shift) by {
      u.LemmaRepr2DUnchanged(oldRepr2D);
      reveal EqualSlice;
    }

    world.LemmaNoTagBeforeVacuous(rRightTag);
    LemmaBarrierOrder(world, rRightTag, n, nt, cNumber, N, tolerance, F);
    LemmaRelyPayloadSize(rRightTag, world.size, nt, N, 
                         RhsInit(N, F), tolerance);
    
    reqRRight.Wait();

    assert EqualSlice(u, spec, N, (u.dim1 - 1), u.dim1, shift) by {
      LemmaOnRecv(u, world.size, cNumber, nt, n, N, tolerance, F, spec, 
                  rRightTag, world.rank, world.rank + 1, step, (u.dim1 - 1),
                  rRightFrom);
    }

    assert EqualWithPadding(u, spec, N, N, 0, shift, 0) by {
      u.LemmaRepr2DPartiallyChanged(oldRepr2D, oldRepr, u.dim1 - 1, 1);
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
    (u:ArrayOfReals2D, world:MPI.World<real>, ghost cNumber:nat,
     nt:nat, n:nat, N:nat, tolerance:real, F: (int, int) -> real) 
    requires world.size > 1
    requires N >= 3
    requires world.rank < world.size
    requires (N - 2) % world.size == 0 
    requires (N - 2) / world.size >= 1
    requires n < cNumber <= nt
    requires u.IsValid()
    requires u.FreeToWrite(0, u.length)
    requires u.dim1 == (N - 2) / world.size + 2
    requires N >= u.dim1 + ((N - 2) / world.size) * world.rank
    requires u.dim2 == N
    requires EqualWithPadding(u, 
      SpecOuterHelperWithConvergence
        (nt-n-1, nt, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0,
      N, N, 1, ((N - 2) / world.size) * world.rank, 0)
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
      RelyPayload(tag, size, nt, N, RhsInit(N, F), tolerance))
    requires world.RelySend == RelySender
    requires world.RelyRecv == RelyReceiver
    requires world.Barriers == ((id:nat, size:nat) => 
        Barriers(id, size, nt, cNumber, N, RhsInit(N, F), tolerance))
    modifies u, world
    ensures u.IsValid()
    ensures u.FreeToWrite(0, u.length)
    ensures EqualWithPadding(u, 
      SpecOuterHelperWithConvergence
        (nt-n-1, nt, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0,
      N, N, 0, ((N - 2) / world.size) * world.rank, 0)
    ensures world.rank != world.size - 1
      ==> world.Tag() == n * 2 * (world.size - 1) + 2 * world.rank + 1 
    ensures world.rank == world.size - 1
      ==> world.Tag() == n * 2 * (world.size - 1) + 2 * world.rank - 1
    ensures world.SendBuffer() == {}
    ensures world.RecvBuffer() == {}
    ensures world.BarrierID() == n
    ensures !world.Finalized()
  {
    ghost var step := (N - 2) / world.size;
    ghost var shift := world.rank * step;
    ghost var spec := SpecOuterHelperWithConvergence
        (nt-n-1, nt, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0;
    LemmaNoWriteLockBlockTrivial(u, 1, u.dim1 - 1, u.dim2 - 1, u.dim2);
    LemmaNoReadLockBlockTrivial(u, 1, u.dim1 - 1, u.dim2 - 1, u.dim2);
    Arrays2D.SetRange(u, 1, u.Dim1() - 1, u.Dim2() - 1, u.Dim2(), 0.0);
    assert EqualWithPadding(u, spec, |spec|, u.dim2, 1, shift, 0)
        && AllInRange(u, 1, u.dim1 - 1, u.dim2 - 1, u.dim2, 0.0) by {
      reveal Arrays2D.AllInRange;
      reveal Arrays2D.AllOutRange;
      reveal EqualWithPadding;
    }
    LemmaNoWriteLockBlockTrivial(u, 1, u.dim1 - 1, 0, 1);
    LemmaNoReadLockBlockTrivial(u, 1, u.dim1 - 1, 0, 1);
    Arrays2D.SetRange(u, 1, u.Dim1() - 1, 0, 1, 0.0);
    assert EqualSlice(u, spec, |spec|, 1, u.dim1 - 1, shift) by {
      reveal Arrays2D.AllInRange;
      reveal Arrays2D.AllOutRange;
      reveal EqualSlice;
      reveal EqualWithPadding;
      reveal BorderIsZero;
    }
    reveal ArrayOfReals2D.FreeToReadStatic;
    reveal ArrayOfReals2D.FreeToWriteStatic;
    if world.rank == 0 {
      ExchangeBoundaryDataP0(u, world, cNumber, nt, n, N, tolerance, F);
    } else if world.rank == world.size - 1 {
      ExchangeBoundaryDataPLast(u, world, cNumber, nt, n, N, tolerance, F);
    } else {
      ExchangeBoundaryDataPMid(u, world, cNumber, nt, n, N, tolerance, F);
    }
  }

  ghost function ModuloIteration(tag:nat, size:nat):nat {
    if size <= 1 then 0 else tag % (2 * (size - 1))
  }

  ghost function Iteration(tag:nat, size:nat):nat 
    requires size > 1
  {
    assert size - 1 > 0;
    assert tag / (2 * (size - 1)) >= 0;
    if size <= 1 then 0 else tag / (2 * (size - 1)) + 1
  }

  ghost function RelySender(tag:nat, size:nat):nat {
    (ModuloIteration(tag, size) + 1) / 2
  }

  ghost function RelyReceiver(tag:nat, size:nat):nat {
    ModuloIteration(tag, size) / 2 + (tag + 1) % 2
  }

  ghost predicate RelyPayloadConds
    (tag:nat, size:nat, nt:nat, N:nat, Rhs:seq<seq<real>>)
  {
    && size > 1 && N >= 3
    && ((N - 2) / size) >= 1
    && Iteration(tag, size) <= nt 
    && RelySender(tag, size) < size 
    && RelyReceiver(tag, size) < size
    && RelySender(tag, size) != RelyReceiver(tag, size)
    && SequenceIsSquare(N, Rhs)
  }

  lemma LemmaRelyPayloadConds
    (tag:nat, size:nat, nt:nat, N:nat, Rhs:seq<seq<real>>, 
     sender:nat, receiver:nat, step: nat, spec:seq<seq<real>>, tol:real)
    requires RelyPayloadConds(tag, size, nt, N, Rhs)
    requires sender == RelySender(tag, size)
    requires receiver == RelyReceiver(tag, size)
    requires step == (N - 2) / size
    requires spec == SpecOuterHelperWithConvergence
            (nt-Iteration(tag, size), nt, N, tol, Rhs, SpecInitZeros(N)).0
    ensures receiver > sender ==> (sender + 1) * step < |spec|
    ensures receiver <= sender ==> sender * step + 1 < |spec|
  {
    if receiver > sender {
      calc {
        (sender + 1) * step;
        <= {LemmaMulInequality(receiver, size, step);}
        receiver * step;
        < {LemmaMulStrictInequality(sender + 1, size, step);}
        size * step;
        == size * ((N - 2) / size);
      }
    } else {
      calc {
        sender * step + 1;
        <= {LemmaMulStrictInequality(sender, size, step);}
        size * step;
        == size * ((N - 2) / size);
      }
    }
  }

  ghost function {:opaque} RelyPayload
    (tag:nat, size:nat, nt:nat, N:nat, Rhs:seq<seq<real>>, tol:real):seq<real> {
    var sender := RelySender(tag, size);
    var receiver := RelyReceiver(tag, size);
    if !RelyPayloadConds(tag, size, nt, N, Rhs)
    then seq(N, i => 0.0) 
    else  var step := (N - 2) / size;
          var spec := SpecOuterHelperWithConvergence
            (nt-Iteration(tag, size), nt, N, tol, Rhs, SpecInitZeros(N)).0;
          LemmaRelyPayloadConds(tag, size, nt, N, Rhs, 
            sender, receiver, step, spec, tol);
          if receiver > sender
          then spec[(sender + 1) * step]
          else spec[sender * step + 1]
  }

  lemma LemmaRelyPayloadSize
    (tag:nat, size:nat, nt:nat, N:nat, Rhs:seq<seq<real>>, tol:real) 
    ensures |RelyPayload(tag, size, nt, N, Rhs, tol)| == N
  {
    reveal RelyPayload;
  }

  lemma LemmaBarriersConds
    (id:nat, size:nat, maxIts:nat, cNumber:nat, N:nat, 
     Rhs:seq<seq<real>>, step:nat, rank:nat) 
    requires N >= 3
    requires size > 1
    requires rank < size
    requires step == (N - 2) / size
    requires step >= 1
    requires SequenceIsSquare(N, Rhs)
    requires id < cNumber
    requires cNumber <= maxIts
    ensures 0 <= rank * step < rank * step + step + 2 
    ensures rank * step + step + 2 
        <= |SpecOuterHelper(maxIts - id, maxIts, N, Rhs, SpecInitZeros(N))|
    ensures rank * step + step + 2 
        <= |SpecOuterHelper(maxIts - id + 1, maxIts, N, Rhs, SpecInitZeros(N))|
  {
    calc {
      rank * step + step;
      == {LemmaMulIsDistributiveAddOtherWay(step, rank, 1);}
         (rank + 1) * step;
      <= {LemmaMulInequality(rank + 1, size, step);}
         size * step;
      == size * ((N-2) / size);
    }
  }

  ghost function {:opaque} Barriers
    (id:nat, size:nat, maxIts:nat, 
     cNumber:nat, N:nat, Rhs:seq<seq<real>>, tolerance:real):
    (r:BarrierKind<real>)
     requires N >= 3
     requires SequenceIsSquare(N, Rhs)
     requires cNumber <= maxIts
  {
    if size > 1 && (N - 2) / size >= 1
    then assert id * 2 * (size - 1) >= 0;
    if id < cNumber
    then 
      MPI.BarrierKind.AllReduceAnd(
        rank => 
          if 0 <= rank < size 
          then LemmaBarriersConds(id, size, maxIts, cNumber, N, Rhs, 
                (N-2)/size, rank);
               Converged((N - 2) / size + 2, N, tolerance, 
                SpecOuterHelper(maxIts - id - 1, maxIts, N, Rhs, 
                  SpecInitZeros(N))
                  [rank * ((N - 2) / size)..
                   rank * ((N - 2) / size) + ((N - 2) / size) + 2],
                SpecOuterHelper(maxIts - id, maxIts, N, Rhs, 
                  SpecInitZeros(N))
                  [rank * ((N - 2) / size)..
                   rank * ((N - 2) / size) + ((N - 2) / size) + 2])
                else false,
          id * 2 * (size - 1))
    else MPI.BarrierKind.Gather(
          0,
          ArrayOfReals2D.Flatten(
            Spec.SpecOuterHelperWithConvergence(
              maxIts - cNumber, maxIts, N, tolerance, Rhs, SpecInitZeros(N)).0, N)
            [1 * N..(N-1) * N],
          cNumber * 2 * (size - 1))
    else MPI.BarrierKind.Simple(0)
  }

  lemma LemmaConvergedInParts
    (world:MPI.World<real>, cNumber:nat, nt:nat, N:nat, tol:real, 
     F: (int,int)->real, n:nat) 
    requires N >= 3
    requires n < cNumber <= nt
    requires world.size > 1 
    requires world.rank < world.size
    requires (N - 2) % world.size == 0
    requires (N - 2) / world.size >= 1
    requires (world.Barriers == (id:nat, size:nat) => 
        Barriers(id, size, nt, cNumber, N, RhsInit(N, F), tol))
    requires world.Barriers(n, world.size).AllReduceAnd?
    requires world.RecursiveReduceAnd(n, 0)
    ensures Converged(N, N, tol, 
        SpecOuterHelper(nt - n - 1, nt, N, RhsInit(N, F), SpecInitZeros(N)),
        SpecOuterHelper(nt - n, nt, N, RhsInit(N, F), SpecInitZeros(N)))
  {
    reveal Barriers;
    var step := (N - 2) / world.size;
    var a := SpecOuterHelper(nt-n-1, nt, N, RhsInit(N, F), SpecInitZeros(N));
    var b := SpecOuterHelper(nt-n, nt, N, RhsInit(N, F), SpecInitZeros(N));
    for rank := 0 to world.size
      invariant rank > 0 ==> (rank - 1) * step + step + 2 <= N
      invariant rank > 0 ==> 
        ConvergedInRange(N, N, tol, a, b, 0, (rank - 1) * step + step + 2 )
    {
      world.LemmaRecursiveAnd(n, rank);
      LemmaBarriersConds(n, world.size, nt, cNumber, N, RhsInit(N, F), 
                (N-2)/world.size, rank);
      LemmaConvergedSplit(N, N, tol, a, b, (rank) * step, 
        (rank) * step + step + 2);
      if rank > 0 {
        LemmaConvergedInRangeSum(N, N, tol, a, b, 0,
          (rank - 1) * step + step + 2, rank * step, rank * step + step + 2);
      }
    }
    LemmaConverged(N, N, tol, a, b);
  }

  lemma LemmaConvergedInPartsConverse
    (world:MPI.World<real>, cNumber:nat, nt:nat, N:nat, tol:real, 
     F: (int,int)->real, n:nat) 
    requires N >= 3
    requires n < cNumber <= nt
    requires world.size > 1 
    requires world.rank < world.size
    requires (N - 2) % world.size == 0
    requires (N - 2) / world.size >= 1
    requires (world.Barriers == (id:nat, size:nat) => 
        Barriers(id, size, nt, cNumber, N, RhsInit(N, F), tol))
    requires world.Barriers(n, world.size).AllReduceAnd?
    requires Converged(N, N, tol, 
        SpecOuterHelper(nt - n - 1, nt, N, RhsInit(N, F), SpecInitZeros(N)),
        SpecOuterHelper(nt - n, nt, N, RhsInit(N, F), SpecInitZeros(N)))
    ensures world.RecursiveReduceAnd(n, 0)
  {
    reveal Barriers;
    var step := (N - 2) / world.size;
    var a := SpecOuterHelper(nt-n-1, nt, N, RhsInit(N, F), SpecInitZeros(N));
    var b := SpecOuterHelper(nt-n, nt, N, RhsInit(N, F), SpecInitZeros(N));
    for rank := 0 to world.size
      invariant forall i :: 0 <= i < rank 
                  ==> world.Barriers(n, world.size).value(i)
    {
      LemmaConverged(N, N, tol, a, b);
      LemmaBarriersConds(n, world.size, nt, cNumber, N, RhsInit(N, F), 
                (N-2)/world.size, rank);
      LemmaConvergedInRangeNarrower(N, N, tol, a, b, 0, N, (rank) * step, 
        (rank) * step + step + 2);
      LemmaConvergedSplit(N, N, tol, a, b, (rank) * step, 
        (rank) * step + step + 2);
    }
    world.LemmaRecursiveAndConverse(n);
  }

  lemma LemmaConvergedInPartsFull
    (world:MPI.World<real>, cNumber:nat, nt:nat, N:nat, tol:real, 
     F: (int,int)->real, n:nat) 
    requires N >= 3
    requires n < cNumber <= nt
    requires world.size > 1 
    requires world.rank < world.size
    requires (N - 2) % world.size == 0
    requires (N - 2) / world.size >= 1
    requires (world.Barriers == (id:nat, size:nat) => 
        Barriers(id, size, nt, cNumber, N, RhsInit(N, F), tol))
    requires world.Barriers(n, world.size).AllReduceAnd?
    ensures world.RecursiveReduceAnd(n, 0) <==>
    Converged(N, N, tol, 
        SpecOuterHelper(nt - n - 1, nt, N, RhsInit(N, F), SpecInitZeros(N)),
        SpecOuterHelper(nt - n, nt, N, RhsInit(N, F), SpecInitZeros(N)))
  {
    if world.RecursiveReduceAnd(n, 0) {
        LemmaConvergedInParts(world, cNumber, nt, N, tol, F, n);
    }
    if (Converged(N, N, tol, 
        SpecOuterHelper(nt - n - 1, nt, N, RhsInit(N, F), SpecInitZeros(N)),
        SpecOuterHelper(nt - n, nt, N, RhsInit(N, F), SpecInitZeros(N)))) {
      LemmaConvergedInPartsConverse(world, cNumber, nt, N, tol, F, n);
    }
  }

  lemma LemmaConvergedPart
    (world:MPI.World<real>, uOld:ArrayOfReals2D, u:ArrayOfReals2D, 
     specOld:seq<seq<real>>, spec:seq<seq<real>>,
     cNumber:nat, nt:nat, N:nat, tol:real, 
     F: (int,int)->real, n:nat, step:nat) 
    requires N >= 3
    requires n < cNumber <= nt
    requires world.size > 1 
    requires world.rank < world.size
    requires step == (N - 2) / world.size
    requires (N - 2) % world.size == 0
    requires (N - 2) / world.size >= 1
    requires (world.Barriers == (id:nat, size:nat) => 
        Barriers(id, size, nt, cNumber, N, RhsInit(N, F), tol))
    requires spec == SpecOuterHelperWithConvergence
        (nt-n-1, nt, N, tol, RhsInit(N, F), SpecInitZeros(N)).0
    requires specOld == SpecOuterHelperWithConvergence
        (nt-n, nt, N, tol, RhsInit(N, F), SpecInitZeros(N)).0
    requires !SpecConverged
        (nt-n, nt, N, tol, RhsInit(N, F), SpecInitZeros(N))
    requires u.IsValid()
    requires uOld.IsValid()
    requires u.dim2 == N
    requires uOld.dim2 == N
    requires u.dim1 == step + 2
    requires uOld.dim1 == step + 2
    requires world.Barriers(n, world.size).AllReduceAnd?
    requires N >= step + 2 + step * world.rank
    requires EqualWithPadding(u, spec, N, N, 0, step * world.rank, 0) 
    requires EqualWithPadding(uOld, specOld, N, N, 0, step * world.rank, 0) 
    ensures world.Barriers(n, world.size).value(world.rank) <==>
      Converged(u.dim1, N, tol, uOld.Repr2D, u.Repr2D)
  {
    assert specOld == SpecOuterHelper(
      nt - n, nt, N, RhsInit(N, F), SpecInitZeros(N))
        && spec == SpecOuterHelper(
      nt - n - 1, nt, N, RhsInit(N, F), SpecInitZeros(N)) by {
        reveal SpecOuterHelperWithConvergence;
        reveal SpecConverged;
    }
    reveal Barriers;
    LemmaBarriersConds(n, world.size, nt, cNumber, N, RhsInit(N, F), 
                (N-2)/world.size, world.rank);
    assert u.Repr2D == spec[step * world.rank..step * world.rank + step + 2] 
      && uOld.Repr2D == specOld[step * world.rank..step * world.rank + step + 2]
    by {
      reveal EqualWithPadding;
      assert forall i :: 0 <= i < |u.Repr2D| ==>
        u.Repr2D[i] == spec[step * world.rank + i];
      assert forall i :: 0 <= i < |uOld.Repr2D| ==>
        uOld.Repr2D[i] == specOld[step * world.rank + i];
    } 
    assert Converged(u.dim1, N, tol, uOld.Repr2D, u.Repr2D) == 
           Converged(u.dim1, N, tol, u.Repr2D, uOld.Repr2D) by {
      LemmaConverged(u.dim1, N, tol, uOld.Repr2D, u.Repr2D);
      LemmaConverged(u.dim1, N, tol, u.Repr2D, uOld.Repr2D);
      reveal ConvergedInRange;
    }
  }

  lemma LemmaBarriersNotTooFarApart
    (size:nat, maxIts:nat, cNumber:nat, N:nat, F:(int,int)->real, tol:real) 
    requires 32767 / 2 > size
    requires N >= 3
    requires size > 1
    requires cNumber <= maxIts
    requires (N - 2) / size >= 1
    ensures World.BarriersNotTooFarApart((id:nat, size:nat) => 
      Barriers(id, size, maxIts, cNumber, N, RhsInit(N, F), tol), size)
  {
    reveal Barriers;
    var BarriersTemp := (id:nat, size:nat) => 
      Barriers(id, size, maxIts, cNumber, N, RhsInit(N, F), tol);
    if size > 1 && (N - 2) / size >= 1 {
      assert forall i :: cNumber > i > 0 ==> 
        BarriersTemp(i, size).nextTag == i * 2 * (size - 1);
    } 
  }

  lemma LemmaBarrierId
    (world:MPI.World<real>, maxIts:nat, 
     cNumber:nat, N:nat, tol:real, F: (int,int)->real, n:nat) 
    requires N >= 3
    requires cNumber <= maxIts
    requires (world.Barriers == (id:nat, size:nat) => 
        Barriers(id, size, maxIts, cNumber, N, RhsInit(N, F), tol))
    requires world.size > 1
    requires (N - 2) / world.size >= 1
    ensures n < cNumber ==> world.BarriersFull(n) == n * 2 * (world.size - 1)
    ensures n >= cNumber 
      ==> world.BarriersFull(n) == cNumber * 2 * (world.size - 1)
  {
    reveal Barriers;
  }

  lemma LemmaGatherBarrierSpec(
     maxIts:nat, cN:nat, N:nat, tol:real, F: (int,int)->real, size:nat) 
    requires N >= 3
    requires size > 1
    requires cN <= maxIts
    requires (N - 2) / size >= 1
    ensures Barriers(cN, size, maxIts, cN, N, RhsInit(N, F), tol).Gather?
    ensures Barriers(cN, size, maxIts, cN, N, RhsInit(N, F), tol).nextTag 
       == cN * 2 * (size - 1)
    ensures Barriers(cN, size, maxIts, cN, N, RhsInit(N, F), tol).root == 0
    ensures Barriers(cN, size, maxIts, cN, N, RhsInit(N, F), tol).whole == 
      ArrayOfReals2D.Flatten(
        SpecOuterHelperWithConvergence
        (maxIts-cN, maxIts, N, tol, RhsInit(N, F), SpecInitZeros(N)).0, N)
        [N..(N-1) * N]
    ensures |Barriers(cN, size, maxIts, cN, N, RhsInit(N, F), tol).whole| 
         == (N - 2) * N
  {
    reveal Barriers;
    LemmaMulInequality(N-1, N, N);
    LemmaMulInequality(1, N - 1, N);
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

  lemma {:isolate_assertions} LemmaParallelGatherHelper
    (s1:seq<real>, s2:seq<real>, N:nat, step:nat, rank:nat, size:nat) 
    requires (step * rank) * N + N + step * N 
          <= N * N == |s2|
    requires s1 == s2[(step * rank) * N + 1 * N..
                      (step * rank) * N + 1 * N + step * N]
    requires N >= 3
    requires size > rank >= 0
    requires step == (N - 2) / size
    requires (N - 2) % size == 0
    ensures step * N * (rank + 1) <= (N-2) * N
    ensures s1 == s2[1 * N..(N-1) * N][step * N * rank..step * N * (rank + 1)]
  {
    calc {
         step * N * (rank + 1);
      <= {LemmaMulInequality(rank + 1, size, step * N);}
         step * N * size;
      == N * (size * ((N - 2) / size));
      == {LemmaFundamentalDivMod(N - 2, size);}
         N * (N - 2);
      == (N - 2) * N;
    }
    if rank == 0 {
    } else {
      for i := 0 to |s1| 
        invariant s1[..i] == s2
          [1 * N..(N-1) * N][step * N * rank..step * N * (rank + 1)][..i]
      {
        assert s1[i] == s2[(step * rank) * N + 1 * N + i];
      }
    }
  }

  method RhsParallelInit
    (N:nat, F: (int, int) -> real, rank:nat, size:nat, step:nat) 
    returns (r:ArrayOfReals2D)
    requires rank < size
    requires size > 1
    requires step == (N - 2) / size
    requires (N - 2) % size == 0
    requires (N - 2) / size >= 1
    ensures r.IsValid()
    ensures fresh(r)
    ensures r.FreeToWrite(0, r.length)
    ensures r.FreeToRead(0, r.length)
    ensures r.dim1 == step + 2
    ensures r.dim2 == N
    ensures N >= step + 2 + step * rank
    ensures EqualWithPadding(r, Spec.RhsInit(N, F), N, N, 0, step * rank, 0)
  {
    reveal ArrayOfReals2D.FreeToReadStatic;
    reveal ArrayOfReals2D.FreeToWriteStatic;
    LemmaRhsInit(N, F);
    var rhsSpec :=  seq(step + 2, i => seq(N, j => F(step * rank + i, j)));
    assert forall i, j :: (0 <= i < step + 2 && 0 <= j < N) 
            ==> rhsSpec[i][j] == F(step * rank + i, j);
    calc {
      rank * step + step + 2;
      == {LemmaMulIsDistributiveAddOtherWay(step, rank, 1);}
         (rank + 1) * step + 2;
      <= {LemmaMulInequality(rank + 1, size, step);}
         size * step + 2;
      == size * ((N-2) / size) + 2;
    }
    reveal EqualWithPadding;
    assert forall i, j :: (0 <= i < step + 2 && 0 <= j < N) 
            ==> assert step * rank + i < rank * step + step + 2; 
                rhsSpec[i][j] == RhsInit(N, F)[step * rank + i][j];
    r := FromSeq(rhsSpec, step + 2, N);
  }

  lemma LemmaParallelInitHelper
    (u:ArrayOfReals2D, maxIts:nat, N:nat, tolerance:real, F: (int, int) -> real,
     step:nat, rank:nat, size:nat) 
    requires N >= 3
    requires 32767 / 2 > size > 1
    requires (N - 2) % size == 0
    requires (N - 2) / size >= 1
    requires step == (N - 2) / size
    requires u.IsValid()
    requires u.dim1 == step + 2
    requires u.dim2 == N
    requires forall i,j :: 
      (0 <= i < u.dim1 && 0 <= j < u.dim2) ==> u.Repr2D[i][j] == 0.0
    requires rank < size
    ensures N >= u.dim1 + step * rank
    ensures EqualWithPadding(u, SpecOuterHelperWithConvergence
      (maxIts, maxIts, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0,
      N, N, 0, step * rank, 0) 
  {
    calc {
      u.dim1 + step * rank;
      == step + 2 + step * rank;
      == step + step * rank + 2;
      == {LemmaMulIsDistributiveAdd(step, 1, rank);}
         step * (1 + rank) + 2;
      <= {LemmaMulInequality(1 + rank, size, step);}
      step * size + 2;
    }
    reveal SpecOuterHelperWithConvergence;
    reveal SpecOuterHelper;
    reveal EqualWithPadding;
    reveal SpecConverged;
    LemmaSpecInitZeros(N);
  }

  method {:isolate_assertions} Parallel
    (N:nat, maxIts:nat, tolerance:real, F: (int, int) -> real, size:nat) 
    returns (u:ArrayOfReals2D, world:MPI.World<real>, converged: bool)
    requires N >= 3
    requires 32767 / 2 > size > 1
    requires (N - 2) % size == 0
    requires (N - 2) / size >= 1
    ensures world.rank == 0 ==> 
      (u.Repr2D, converged) == Spec.Spec(N, maxIts, tolerance, F)
    ensures u.IsValid()
    ensures u.FreeToRead(0, u.length)
    ensures u.FreeToWrite(0, u.length)
    ensures world.rank == 0 ==> u.dim1 == N
    ensures world.rank == 0 ==> u.dim2 == N
    ensures world.Finalized()
  {
    var cNumber := ConvergenceNumber
      (0, maxIts, N, tolerance, RhsInit(N, F),  SpecInitZeros(N));
    LemmaBarriersNotTooFarApart(size, maxIts, cNumber, N, F, tolerance);
    world := new MPI.World<real>(
      size, 
      (tag:nat, size:nat) => 
        RelyPayload(tag, size, maxIts, N, RhsInit(N, F), tolerance),
      RelySender,
      RelyReceiver,
      (id:nat, size:nat) => 
        Barriers(id, size, maxIts, cNumber, N, RhsInit(N, F), tolerance),
      (size:nat) => cNumber + 1);
    var rank := world.rank;
    var step := (N - 2) / size;
    var rhs := RhsParallelInit(N, F, rank, size, step);
    u := Zeros(step + 2, N);
    LemmaParallelInitHelper(u, maxIts, N, tolerance, F, step, rank, size);
    var n := 0;
    converged := false;
    assert converged == SpecConverged
        (maxIts, maxIts, N, tolerance, RhsInit(N, F), SpecInitZeros(N)) 
      && !SpecConverged
        (maxIts + 1, maxIts, N, tolerance, RhsInit(N, F), SpecInitZeros(N)) by {
      reveal SpecOuterHelperWithConvergence;
      reveal SpecOuterHelper;
      reveal SpecConverged;
    }
    u.LemmaFreeToWriteStronger(0, u.length);
    while n < maxIts && !converged 
      modifies u, world
      invariant u != rhs
      invariant u.dim1 == step + 2
      invariant u.dim2 == N
      invariant n <= maxIts
      invariant converged ==> n == cNumber
      invariant (!converged && n != maxIts) ==> n < cNumber
      invariant converged == SpecConverged
        (maxIts-n, maxIts, N, tolerance, RhsInit(N, F), SpecInitZeros(N))
      invariant !SpecConverged
        (maxIts-n + 1, maxIts, N, tolerance, RhsInit(N, F), SpecInitZeros(N))
      invariant u.IsValid()
      invariant u.FreeToWrite(0, u.length)
      invariant u.FreeToRead(0, u.length)
      invariant EqualWithPadding(u, SpecOuterHelperWithConvergence
        (maxIts-n, maxIts, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0,
        N, N, 0, step * rank, 0) 
      invariant world.BarrierID() == n
      invariant n == 0 ==> world.Tag() == -1
      invariant (n != 0 && rank != size - 1) 
        ==> world.Tag() == (n - 1) * 2 * (size - 1) + 2 * rank + 1 
      invariant (n != 0 && rank == size - 1) 
        ==> world.Tag() == (n - 1) * 2 * (size - 1) + 2 * rank - 1
      invariant world.SendBuffer() == {}
      invariant world.RecvBuffer() == {}
      invariant !world.Finalized()
    {
      var uOld := u;
      var uSpec := SpecOuterHelperWithConvergence
        (maxIts-n-1, maxIts, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0;
      var uSpecOld := SpecOuterHelperWithConvergence
        (maxIts-n, maxIts, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0;
      u := Shared.JacobiFull(N, uOld, rhs, step * rank, uSpecOld, RhsInit(N, F));
      assert EqualWithPadding(u, uSpec, N, N, 1, step * rank, 0) by {
        reveal SpecOuterHelperWithConvergence;
        reveal SpecOuterHelper;
        reveal EqualWithPadding;
        reveal SpecConverged;
      }
      ExchangeBoundaryData(u, world, cNumber, maxIts, n, N, tolerance, F);
      u.LemmaFreeToWriteStronger(0, u.length);
      var convergedLocally := Convergence(step + 2, N, tolerance, uOld, u);
      LemmaBarrierId(world, maxIts, cNumber, N, tolerance, F, n + 1);
      assert world.BarriersFull(world.BarrierID() + 1) == (n + 1) * 2 * (world.size - 1);
      LemmaOrder(world, world.BarriersFull(world.BarrierID() + 1), n + 1);
      assert world.Barriers(n, world.size).AllReduceAnd? by {
        reveal Barriers;
      }
      LemmaConvergedPart(world, uOld, u, uSpecOld, uSpec, cNumber, maxIts, N, 
        tolerance, F, n, step);
      converged := world.AllReduceAnd(n, convergedLocally);
      LemmaConvergedInPartsFull(world, cNumber, maxIts, N, tolerance, F, n);
      n := n + 1;
      assert converged == SpecConverged
        (maxIts-n, maxIts, N, tolerance, RhsInit(N, F), SpecInitZeros(N)) by {
        reveal SpecConverged;
      }
      LemmaConvergenceNumber(maxIts - n, maxIts, N, tolerance, RhsInit(N, F),
        SpecInitZeros(N));
    }


    LemmaConvergenceNumber(maxIts - n, maxIts, N, tolerance, RhsInit(N, F),
        SpecInitZeros(N));
    assert n == cNumber;
    var part := u;
    if (rank == 0) {
      u := new ArrayOfReals2D(N, N, 0.0);
      u.LemmaFreeToWriteNarrower(N, N + (N - 2) * N);
    }
    assert world.BarrierID() + 1 == cNumber + 1;
    LemmaBarrierId(world, maxIts, cNumber, N, tolerance, F, cNumber + 1);
    LemmaOrder(world, world.BarriersFull(world.BarrierID() + 1), cNumber);
    assert part.FreeToRead(N, N + step * N) by {
      calc {
        N + step * N;
        == {LemmaMulIsDistributive(N, 1, step);}
        (1 + step) * N;
        < {LemmaMulInequality(1 + step, step + 2, N);}
        (step + 2) * N;
        == part.dim1 * N;
        == part.length;
      }
      part.LemmaFreeToWriteNarrower(N, N + step * N);
      part.LemmaFreeToWriteStronger(N, N + step * N);
    }
    LemmaGatherBarrierSpec(maxIts, cNumber, N, tolerance, F, size);
    calc {
      (step * N) * size;
      == {LemmaMulIsCommutative(step, N);
          LemmaMulIsAssociative(N, step, size);}
         N * (step * size);
      == {LemmaMulIsCommutative(step, size);}
         N * (size * step);
      == N * (size * ((N - 2) / size));
      == {assert (N - 2) % size == 0;
          LemmaFundamentalDivMod(N - 2, size);
          assert (N - 2) == size * ((N - 2) / size);}
         N * (N - 2);
      == {LemmaMulIsCommutative(N, N - 2);}
         (N - 2) * N;
    }
    
    assert EqualSlice(part, 
      SpecOuterHelperWithConvergence
         (maxIts-n, maxIts, N, tolerance, RhsInit(N,F), SpecInitZeros(N)).0, 
      N, 1, part.dim1 - 1, step * rank) by {
      reveal EqualSlice;
      reveal EqualWithPadding;
      reveal Spec.Spec;
    }
    LemmaEqualWithPaddingFlatten(part, 
      SpecOuterHelperWithConvergence
         (maxIts-n, maxIts, N, tolerance, RhsInit(N,F), SpecInitZeros(N)).0,
      N, step * rank, 1, step, 1);
    LemmaParallelGatherHelper(
      part.Repr[1 * N..1 * N + step * N], 
      u.Flatten(SpecOuterHelperWithConvergence
         (maxIts-n, maxIts, N, tolerance, RhsInit(N,F), SpecInitZeros(N)).0,
        N),
      N, step, rank, size);

    var oldRepr2D := u.Repr2D;
    var oldRepr := u.Repr;
    world.Gather(0, part, u, N, step * N, N, (N - 2) * N, n);
    u.LemmaFreeToWriteStronger(0, u.length);
    if rank == 0 {
      assert u.Repr2D == SpecOuterHelperWithConvergence
         (maxIts-n, maxIts, N, tolerance, RhsInit(N,F), SpecInitZeros(N)).0 by {
        LemmaEqualWithPaddingFlattenConverse(
          u, SpecOuterHelperWithConvergence
          (maxIts-n, maxIts, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0,
          N, 0, 1, N - 2, 1 * N,  (N - 2) * N);
        u.LemmaRepr2DPartiallyChanged(oldRepr2D, oldRepr, 1, (N - 2));
        reveal BorderIsZero;
        reveal EqualSlice;
        assert forall i :: 0 <= i < N ==> 
         u.Repr2D[i] == 
          SpecOuterHelperWithConvergence
          (maxIts-n, maxIts, N, tolerance, RhsInit(N, F), 
           SpecInitZeros(N)).0[i];
      }
      LemmaSpecAfterConvergence(u, converged, N, maxIts, tolerance, F, n);
    }
  }
}