include "../DafnyMPI/Externs/MPIResource.dfy"
include "../DafnyMPI/Arrays2D.dfy"
include "Spec.dfy"
include "RK4Impl.dfy"

module SequentialBackend {

  import opened MPIResource
  import opened Arrays2D
  import opened Spec
  import opened RK4Impl

  lemma EqualInChunksLemma
    (u:ArrayOfReals2D, uSpec:seq<seq<real>>)
    requires u.IsValid()
    requires u.dim1 >= 9
    requires u.dim2 >= 9
    requires |uSpec| == u.dim1
    requires forall i :: 0 <= i < |uSpec| ==> |uSpec[i]| == u.dim2
    requires EqualWithPadding(u, uSpec, u.dim1, u.dim2, 4, 0, 0)
    requires AllInRange(u, 0, 4, 0, u.dim2, 0.0)
    requires AllInRange(u, u.dim1 - 4, u.dim1, 0, u.dim2, 0.0)
    requires AllInRange(u, 0, u.dim1, u.dim2 - 4, u.dim2, 0.0)
    requires AllInRange(u, 0, u.dim1, 0, 4, 0.0)
    requires BorderIsZero(uSpec, u.dim1, u.dim2)
    ensures u.Repr2D == uSpec 
  {
    reveal Arrays2D.AllInRange;
    reveal Arrays2D.AllOutRange;
    reveal EqualWithPadding;
    reveal Spec.BorderIsZero;
    assert forall i, j :: 0 <= i < u.dim1 && 0 <= j < u.dim2 
            ==> u.Repr2D[i][j] == uSpec[i][j];
    assert forall i :: 0 <= i < u.dim1
            ==> u.Repr2D[i] == uSpec[i];
  }

  method Sequential(
    nx:nat, ny:nat, nt:nat, dim1:nat, dim2:nat, dx:real, dt:real) 
    returns (u:ArrayOfReals2D) 
    requires dx * dx != 0.0
    requires dim1 >= 9
    requires dim2 >= 9
    ensures u.Repr2D == Spec.Spec(nx, ny, nt, dim1, dim2, dx, dt)
    ensures u.IsValid()
    ensures u.FreeToRead(0, u.length)
    ensures u.FreeToWrite(0, u.length)
    ensures u.dim1 == dim1
    ensures u.dim2 == dim2
  {
    var initial := SpecInit(nx, ny, dim1, dim2);
    u := FromSeq(initial, dim1, dim2);
    reveal SpecOuterHelper;
    reveal ArrayOfReals2D.FreeToReadStatic;
    reveal ArrayOfReals2D.FreeToWriteStatic;
    for n := 0 to nt 
      invariant u.dim1 == dim1
      invariant u.dim2 == dim2
      invariant u.Repr2D == SpecOuterHelper(nt-n, nt, initial, dim1, dim2, dx, dt)
      invariant u.IsValid()
      invariant u.FreeToWrite(0, u.length)
      invariant u.FreeToRead(0, u.length)
    {
      reveal Arrays2D.AllInRange;
      reveal Arrays2D.AllOutRange;
      reveal EqualWithPadding;
      reveal Spec.BorderIsZero;
      ghost var uReprOld := u.Repr2D;
      LemmaEqualWithPaddingSelf(u, 0);
      u := RK4Impl.RK4Step(u, u.Repr2D, u.Dim1(), u.Dim2(), dx, dt, 0, 0);
      LemmaNoWriteLockBlockTrivial(u, 0, 4, 0, dim2);
      LemmaNoReadLockBlockTrivial(u, 0, 4, 0, dim2);
      Arrays2D.SetRange(u, 0, 4, 0,     dim2, 0.0);
      LemmaNoWriteLockBlockTrivial(u, dim1 - 4, dim1, 0, dim2);
      LemmaNoReadLockBlockTrivial(u, dim1 - 4, dim1, 0, dim2);
      Arrays2D.SetRange(u, dim1 - 4, dim1, 0, dim2, 0.0);
      LemmaNoWriteLockBlockTrivial(u, 0, dim1, 0, 4);
      LemmaNoReadLockBlockTrivial(u, 0, dim1, 0, 4);
      Arrays2D.SetRange(u, 0, dim1, 0, 4, 0.0);
      LemmaNoWriteLockBlockTrivial(u, 0, dim1, dim2 - 4, dim2);
      LemmaNoReadLockBlockTrivial(u, 0, dim1, dim2 - 4, dim2);
      Arrays2D.SetRange(u, 0, dim1, dim2 - 4, dim2, 0.0);
      EqualInChunksLemma(u, 
        SpecOuterHelper(nt-n-1, nt, initial, dim1, dim2, dx, dt));
    }
    assert u.Repr2D == Spec.Spec(nx, ny, nt, dim1, dim2, dx, dt) by {
      reveal Spec.Spec;
    }
  }

}