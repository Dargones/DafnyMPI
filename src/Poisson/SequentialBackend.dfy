include "../DafnyMPI/Externs/MPIResource.dfy"
include "../DafnyMPI/Arrays2D.dfy"
include "Spec.dfy"
include "Shared.dfy"

module SequentialBackend {

  import opened MPIResource
  import opened Arrays2D
  import opened Spec
  import opened Shared

  lemma EqualInChunksLemma
    (N:nat, u:ArrayOfReals2D, uSpec:seq<seq<real>>)
    requires u.IsValid()
    requires |uSpec| == N
    requires forall i :: 0 <= i < |uSpec| ==> |uSpec[i]| == N
    requires u.dim2 == N
    requires u.dim1 == N
    requires u.dim1 >= 1
    requires EqualWithPadding(u, uSpec, N, N, 1, 0, 0)
    requires AllInRange(u, 0, 1, 0, N, 0.0)
    requires AllInRange(u, u.dim1 - 1, u.dim1, 0, N, 0.0)
    requires AllInRange(u, 0, u.dim1, N - 1, N, 0.0)
    requires AllInRange(u, 0, u.dim1, 0, 1, 0.0)
    requires BorderIsZero(N, uSpec)
    ensures u.Repr2D == uSpec 
  {
    reveal Arrays2D.AllInRange;
    reveal Arrays2D.AllOutRange;
    reveal EqualWithPadding;
    reveal Spec.BorderIsZero;
    assert forall i :: 0 <= i < u.dim1
            ==> u.Repr2D[i] == uSpec[i];
  }

  method Sequential
    (N:nat, maxIts:nat, tolerance:real, F: (int, int) -> real) 
    returns (u:ArrayOfReals2D, converged:bool)
    requires N >= 3
    ensures (u.Repr2D, converged) == Spec.Spec(N, maxIts, tolerance, F)
    ensures u.IsValid()
    ensures u.FreeToRead(0, u.length)
    ensures u.FreeToWrite(0, u.length)
    ensures u.dim1 == N
    ensures u.dim2 == N
  {
    var rhs := FromSeq(RhsInit(N, F), N, N);
    u := Zeros(N, N);
    reveal SpecOuterHelper;
    reveal SequenceIsSquare;
    reveal SpecOuterHelperWithConvergence;
    reveal SpecConverged;
    reveal ArrayOfReals2D.FreeToReadStatic;
    reveal ArrayOfReals2D.FreeToWriteStatic;
    assert u.Repr2D == SpecInitZeros(N) by {
      LemmaSpecInitZeros(N); 
      assert forall i :: 0 <= i < N ==> u.Repr2D[i] == SpecInitZeros(N)[i];
    }
    var n := 0;
    converged := false;
    while n < maxIts && !converged 
      modifies u
      invariant u != rhs
      invariant u.dim1 == N
      invariant u.dim2 == N
      invariant n <= maxIts
      invariant u.Repr2D == SpecOuterHelperWithConvergence
        (maxIts-n, maxIts, N, tolerance, rhs.Repr2D, SpecInitZeros(N)).0
      invariant converged == SpecConverged
        (maxIts-n, maxIts, N, tolerance, rhs.Repr2D, SpecInitZeros(N))
      invariant u.IsValid()
      invariant u.FreeToWrite(0, u.length)
      invariant u.FreeToRead(0, u.length)
    {
      n := n + 1;
      var uOld := u;
      reveal EqualWithPadding;
      reveal Arrays2D.AllInRange;
      reveal Arrays2D.AllOutRange;
      reveal Spec.BorderIsZero;
      var uOldRepr := u.Repr2D;
      u := Shared.JacobiFull(N, uOld, rhs, 0, u.Repr2D, rhs.Repr2D);
      LemmaNoWriteLockBlockTrivial(u, 0, 1, 0, N);
      LemmaNoReadLockBlockTrivial(u, 0, 1, 0, N);
      Arrays2D.SetRange(u, 0, 1, 0,     N, 0.0);
      LemmaNoWriteLockBlockTrivial(u, N - 1, N, 0, N);
      LemmaNoReadLockBlockTrivial(u, N - 1, N, 0, N);
      Arrays2D.SetRange(u, N - 1, N, 0, N, 0.0);
      LemmaNoWriteLockBlockTrivial(u, 0, N, 0, 1);
      LemmaNoReadLockBlockTrivial(u, 0, N, 0, 1);
      Arrays2D.SetRange(u, 0, N, 0, 1, 0.0);
      LemmaNoWriteLockBlockTrivial(u, 0, N, N - 1, N);
      LemmaNoReadLockBlockTrivial(u, 0, N, N - 1, N);
      Arrays2D.SetRange(u, 0, N, N - 1, N, 0.0);
      EqualInChunksLemma(N, u, Spec.JacobiFull(N, uOldRepr, rhs.Repr2D));
      converged := Convergence(N, N, tolerance, u, uOld);
    }
    LemmaSpecAfterConvergence(u, converged, N, maxIts, tolerance, F, n);
  }

}