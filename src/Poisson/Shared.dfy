include "../DafnyMPI/Externs/MPIResource.dfy"
include "../DafnyMPI/Externs/ExternUtils.dfy"
include "../DafnyMPI/Arrays2D.dfy"
include "Spec.dfy"

module Shared {

  import opened MPIResource
  import opened Arrays2D
  import opened Spec
  import ExternUtils

  lemma LemmaSpecAfterConvergence
    (u:ArrayOfReals2D, converged:bool, N:nat, maxIts:nat, tolerance:real, 
     F:(int, int) -> real, n:nat)
    requires n == maxIts || converged
    requires n <= maxIts
    requires N >= 3
    requires u.Repr2D == SpecOuterHelperWithConvergence
        (maxIts-n, maxIts, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0
    requires converged == SpecConverged
        (maxIts-n, maxIts, N, tolerance, RhsInit(N, F), SpecInitZeros(N))
    ensures (u.Repr2D, converged) == Spec.Spec(N, maxIts, tolerance, F)
  {
    reveal Spec.Spec;
    reveal Spec.SpecOuterHelperWithConvergence;
    reveal Spec.SpecConverged;
    if converged {
      for i := n to maxIts 
        invariant i <= maxIts
        invariant u.Repr2D == SpecOuterHelperWithConvergence
        (maxIts-i, maxIts, N, tolerance, RhsInit(N, F), SpecInitZeros(N)).0
        invariant converged == SpecConverged
        (maxIts-i, maxIts, N, tolerance, RhsInit(N, F), SpecInitZeros(N))
      {}
    }
  }

  method Convergence
    (N:nat, M:nat, tolerance:real, a:ArrayOfReals2D, b:ArrayOfReals2D)
    returns (converged?:bool)
    requires a.IsValid()
    requires b.IsValid()
    requires a.FreeToRead(0, a.length)
    requires b.FreeToRead(0, b.length)
    requires N >= 3
    requires M >= 3
    requires a.dim1 == N
    requires a.dim2 == M
    requires b.dim1 == N
    requires b.dim2 == M
    ensures SequenceIsRectangle(N, M, a.Repr2D)
    ensures SequenceIsRectangle(N, M, b.Repr2D)
    ensures converged? <==> Converged(N, M, tolerance, a.Repr2D, b.Repr2D)
  {
    reveal Converged;
    reveal AbsSpec;
    reveal NegateSpec;
    reveal MaxSpec;
    reveal ArrayOfReals2D.FreeToReadStatic;
    reveal ArrayOfReals2D.FreeToWriteStatic;
    var negated := MulConst(b, -1.0);
    var sum := AddArrays(a, negated);
    var abs := Abs(sum);
    var absSpec := AbsSpec(N, M, 
      AddSpec(N, M, a.Repr2D, NegateSpec(N, M, b.Repr2D)));
    LemmaDiff(N, M, tolerance, a.Repr2D, b.Repr2D, absSpec);
    assert forall i :: 0 <= i < N ==> abs.Repr2D[i] == absSpec[i];
    var max := Max(abs);
    return max < tolerance;
  }

  method JacobiFull
    (N:nat, u:ArrayOfReals2D, rhs:ArrayOfReals2D, sx:nat,
     ghost uSpec:seq<seq<real>>, ghost rhsSpec:seq<seq<real>>) 
    returns (uNew: ArrayOfReals2D)
    requires u.IsValid()
    requires rhs.IsValid()
    requires u.FreeToRead(0, u.length)
    requires rhs.FreeToRead(0, rhs.length)
    requires u.dim1 > 2
    requires u.dim1 == rhs.dim1
    requires u.dim2 == rhs.dim2
    requires u.dim2 == N
    requires N >= u.dim1 + sx
    requires N >= 3
    requires SequenceIsSquare(N, uSpec)
    requires SequenceIsSquare(N, rhsSpec)
    requires BorderIsZero(N, uSpec)
    requires EqualWithPadding(u, uSpec, N, N, 0, sx, 0)
    requires EqualWithPadding(rhs, rhsSpec, N, N, 0, sx, 0)
    ensures fresh(uNew)
    ensures uNew.IsValid()
    ensures uNew.dim1 == u.dim1
    ensures uNew.dim2 == N
    ensures uNew.FreeToRead(0, uNew.length)
    ensures uNew.FreeToWrite(0, uNew.length)
    ensures SequenceIsSquare(N, Spec.JacobiFull(N, uSpec, rhsSpec))
    ensures EqualWithPadding(uNew, 
      Spec.JacobiFull(N, uSpec, rhsSpec), N, N, 1, sx, 0)
  {
    reveal ArrayOfReals2D.FreeToReadStatic;
    reveal ArrayOfReals2D.FreeToWriteStatic;
    reveal RollHelper;
    var rollXLeft :=  Roll(u, -1, 0);
    var rollXRight := Roll(u, 1, 0);
    var rollYLeft :=  Roll(u, 0, -1);
    var rollYRight := Roll(u, 0, 1);
    var sum := AddArrays(rollXLeft, rollXRight);
    sum := AddArrays(sum, rollYLeft);
    sum := AddArrays(sum, rollYRight);
    var h:real := 1.0 / ((N - 1) as real);
    var rhsMul := MulConst(rhs, - (h * h));
    sum := AddArrays(sum, rhsMul);
    uNew := MulConst(sum, 0.25);
    reveal EqualWithPadding;
    reveal JacobiPoint;
  }

  function Rhs(x:int, y:int, N:nat):real 
    requires N > 0
  {
    ExternUtils.Sin(2.0 * ExternUtils.Pi() * (x as real) / (N as real)) * 
    ExternUtils.Sin(2.0 * ExternUtils.Pi() * (y as real) / (N as real))
  }
}