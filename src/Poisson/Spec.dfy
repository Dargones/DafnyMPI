module Spec {

ghost function {:opaque} Spec
  (N:nat, maxIts:nat, tolerance:real, F: (int, int) -> real):
  (r:(seq<seq<real>>, bool))
  requires N >= 3
  ensures SequenceIsSquare(N, r.0)
  ensures BorderIsZero(N, r.0)
{
  SpecOuterHelperWithConvergence
    (0, maxIts, N, tolerance, RhsInit(N, F), SpecInitZeros(N))
}

ghost function ConvergenceNumber
  (it:nat, maxIts:nat, N:nat, tolerance:real, 
   Rhs:seq<seq<real>>, init:seq<seq<real>>): (n:nat)
  requires SequenceIsSquare(N, init)
  requires SequenceIsSquare(N, Rhs)
  requires BorderIsZero(N, init)
  requires N >= 3
  decreases maxIts - it
  ensures it < maxIts ==> (n > 0 && n <= maxIts - it)
{
  reveal SpecConverged;
  if it >= maxIts 
  then 0
  else if SpecConverged(it + 1, maxIts, N, tolerance, Rhs, init)
  then ConvergenceNumber(it + 1, maxIts, N, tolerance, Rhs, init)
  else 1 + ConvergenceNumber(it + 1 ,maxIts, N, tolerance, Rhs, init)
}

lemma LemmaConvergenceNumber
  (it:nat, maxIts:nat, N:nat, tolerance:real, 
   Rhs:seq<seq<real>>, init:seq<seq<real>>)
  requires SequenceIsSquare(N, init)
  requires SequenceIsSquare(N, Rhs)
  requires BorderIsZero(N, init)
  requires N >= 3
  requires it <= maxIts
  requires !SpecConverged(it + 1, maxIts, N, tolerance, Rhs, init)
  ensures (SpecConverged(it, maxIts, N, tolerance, Rhs, init) || it == 0) ==> 
    maxIts - it == ConvergenceNumber(0, maxIts, N, tolerance, Rhs, init)
  ensures (!SpecConverged(it, maxIts, N, tolerance, Rhs, init) && it != 0) ==> 
    maxIts - it < ConvergenceNumber(0, maxIts, N, tolerance, Rhs, init)
{
  reveal SpecConverged;
  if it < maxIts {
    for i := it + 1 to maxIts 
      invariant !SpecConverged(i, maxIts, N, tolerance, Rhs, init)
      invariant ConvergenceNumber(it, maxIts, N, tolerance, Rhs, init) == 
                ConvergenceNumber(i, maxIts, N, tolerance, Rhs, init) + (i - it)
    {}
  }
  if SpecConverged(it, maxIts, N, tolerance, Rhs, init) {
    for i := it downto 0 
      invariant SpecConverged(i, maxIts, N, tolerance, Rhs, init)
      invariant ConvergenceNumber(i, maxIts, N, tolerance, Rhs, init) == 
                ConvergenceNumber(it, maxIts, N, tolerance, Rhs, init)
    {}
  } else if (it != 0) {
    for i := it - 1 downto 0 
      invariant ConvergenceNumber(i, maxIts, N, tolerance, Rhs, init) > 
                maxIts - it
    {}
  }
}

function {:opaque} RhsInit
  (N:nat, F: (int, int) -> real): (r:seq<seq<real>>)
  ensures SequenceIsSquare(N, r)
{
  seq(N, i => seq(N, j => F(i, j)))
}

lemma LemmaRhsInit(N:nat, F: (int, int) -> real) 
  ensures forall i, j :: (0 <= i < N && 0 <= j < N) 
            ==> RhsInit(N, F)[i][j] == F(i, j)
{
  reveal RhsInit;
}

ghost function {:opaque} SpecOuterHelperWithConvergence
  (it:nat, maxIts:nat, N:nat, tolerance:real, 
   Rhs:seq<seq<real>>, init:seq<seq<real>>): (r:(seq<seq<real>>, bool))
  requires SequenceIsSquare(N, Rhs)
  requires SequenceIsSquare(N, init)
  requires BorderIsZero(N, init)
  requires N >= 3
  decreases maxIts - it
  ensures SequenceIsSquare(N, r.0)
  ensures BorderIsZero(N, r.0)
{
  reveal SpecConverged;
  if SpecConverged(it + 1, maxIts, N, tolerance, Rhs, init)
  then (SpecOuterHelperWithConvergence
         (it + 1, maxIts, N, tolerance, Rhs, init).0, true)
  else (SpecOuterHelper(it, maxIts, N, Rhs, init), 
        SpecConverged(it, maxIts, N, tolerance, Rhs, init))
}

ghost predicate {:opaque} SpecConverged
  (it:nat, maxIts:nat, N:nat, tolerance:real, 
   Rhs:seq<seq<real>>, init:seq<seq<real>>) 
  requires SequenceIsSquare(N, Rhs)
  requires SequenceIsSquare(N, init)
  requires BorderIsZero(N, init)
  requires N >= 3
  decreases maxIts - it
{
  && it < maxIts
  && (|| Converged(N, N, tolerance, SpecOuterHelper(it, maxIts, N, Rhs, init),
                              SpecOuterHelper(it + 1, maxIts, N, Rhs, init))
      || SpecConverged(it + 1, maxIts, N, tolerance, Rhs, init))
}

ghost function {:opaque} SpecOuterHelper
  (it:nat, maxIts:nat, N:nat, Rhs:seq<seq<real>>, init:seq<seq<real>>): 
  (r:seq<seq<real>>)
  requires SequenceIsSquare(N, Rhs)
  requires SequenceIsSquare(N, init)
  requires BorderIsZero(N, init)
  requires N >= 3
  decreases maxIts - it
  ensures SequenceIsSquare(N, r)
  ensures BorderIsZero(N, r)
{
  if it >= maxIts
  then init
  else JacobiFull(N, SpecOuterHelper(it + 1, maxIts, N, Rhs, init), Rhs)
}

ghost predicate {:opaque} Converged
  (N:nat, M:nat, tolerance:real, a:seq<seq<real>>, b:seq<seq<real>>)
  requires N >= 1
  requires M >= 1
  requires SequenceIsRectangle(N, M, a)
  requires SequenceIsRectangle(N, M, b)
{
  MaxSpec(N, M, 
    AbsSpec(N, M, AddSpec(N, M, a, NegateSpec(N, M, b)))) < tolerance
}

ghost predicate {:opaque} ConvergedInRange(
  N:nat, M:nat, tolerance:real,
  a:seq<seq<real>>, b:seq<seq<real>>, low:nat, high:nat)
  requires N >= 1
  requires M >= 1
  requires low < high <= N
  requires SequenceIsRectangle(N, M, a)
  requires SequenceIsRectangle(N, M, b)
{
  forall i, j :: (low <= i < high && 0 <= j < M) ==> 
      (if a[i][j] - b[i][j] > 0.0 
            then a[i][j] - b[i][j] else b[i][j] - a[i][j]) < tolerance
}

lemma LemmaConvergedInRangeSum(N:nat, M:nat, tolerance:real,
  a:seq<seq<real>>, b:seq<seq<real>>, low1:nat, high1:nat, low2:nat, high2:nat)
  requires N >= 1
  requires M >= 1
  requires low1 < low2 <= high1 < high2 <= N
  requires SequenceIsRectangle(N, M, a)
  requires SequenceIsRectangle(N, M, b)
  requires ConvergedInRange(N, M, tolerance, a, b, low1, high1)
  requires ConvergedInRange(N, M, tolerance, a, b, low2, high2)
  ensures ConvergedInRange(N, M, tolerance, a, b, low1, high2)
{
  reveal ConvergedInRange;
}

lemma LemmaConvergedInRangeNarrower(N:nat, M:nat, tolerance:real,
  a:seq<seq<real>>, b:seq<seq<real>>, low1:nat, high1:nat, low2:nat, high2:nat)
  requires N >= 1
  requires M >= 1
  requires low1 <= low2 < high2 <= high1 <= N
  requires SequenceIsRectangle(N, M, a)
  requires SequenceIsRectangle(N, M, b)
  requires ConvergedInRange(N, M, tolerance, a, b, low1, high1)
  ensures ConvergedInRange(N, M, tolerance, a, b, low2, high2)
{
  reveal ConvergedInRange;
}

lemma LemmaConverged
  (N:nat, M:nat, tolerance:real, a:seq<seq<real>>, b:seq<seq<real>>)
  requires N >= 1
  requires M >= 1
  requires SequenceIsRectangle(N, M, a)
  requires SequenceIsRectangle(N, M, b)
  ensures Converged(N, M, tolerance, a, b) <==> 
    ConvergedInRange(N, M, tolerance, a, b, 0, N)
{
  reveal ConvergedInRange;
  LemmaDiff(N, M, tolerance, a, b, 
    AbsSpec(N, M, AddSpec(N, M, a, NegateSpec(N, M, b))));
  reveal Converged;
}

lemma LemmaConvergedSplit
  (N:nat, M:nat, tolerance:real, 
   a:seq<seq<real>>, b:seq<seq<real>>, low:nat, high:nat)
  requires N >= 1
  requires M >= 1
  requires low < high <= N
  requires SequenceIsRectangle(N, M, a)
  requires SequenceIsRectangle(N, M, b)
  ensures Converged(high - low, M, tolerance, a[low..high], b[low..high]) <==>
    ConvergedInRange(N, M, tolerance, a, b, low, high)
{
  reveal ConvergedInRange;
  LemmaConverged(high - low, M, tolerance, a[low..high], b[low..high]);
  if Converged(high - low, M, tolerance, a[low..high], b[low..high]) {
    assert forall i, j :: (low <= i < high && 0 <= j < M) ==> 
      (if a[i][j] - b[i][j] > 0.0 
            then a[i][j] - b[i][j] else b[i][j] - a[i][j]) < tolerance;
  }
}

lemma LemmaDiff
  (N:nat, M:nat, tolerance:real, a:seq<seq<real>>, b:seq<seq<real>>, d:seq<seq<real>>)
  requires SequenceIsRectangle(N, M, a)
  requires SequenceIsRectangle(N, M, b)
  requires d == AbsSpec(N, M, AddSpec(N, M, a, NegateSpec(N, M, b)))
  ensures forall i, j :: (0 <= i < N && 0 <= j < M) ==>
    d[i][j] == (if a[i][j] - b[i][j] > 0.0 
            then a[i][j] - b[i][j] else b[i][j] - a[i][j])
{
  reveal AbsSpec;
  reveal AddSpec;
  reveal NegateSpec;
}

ghost function {:opaque} NegateSpec
  (N:nat, M:nat, a:seq<seq<real>>): (r:seq<seq<real>>)
  requires SequenceIsRectangle(N, M, a)
  ensures SequenceIsRectangle(N, M, r)
{
  seq(N, i => seq(M, j => if 0 <= i < N && 0 <= j < M 
                          then -a[i][j] else 0.0))
}

ghost function {:opaque} AddSpec
  (N:nat, M:nat, a:seq<seq<real>>, b:seq<seq<real>>): (r:seq<seq<real>>)
  requires SequenceIsRectangle(N, M, a)
  requires SequenceIsRectangle(N, M, b)
  ensures SequenceIsRectangle(N, M, r)
{
  seq(N, i => seq(M, j => if 0 <= i < N && 0 <= j < M
                          then a[i][j] + b[i][j] else 0.0))
}

ghost function {:opaque} AbsSpec
  (N:nat, M:nat, a:seq<seq<real>>): (r:seq<seq<real>>)
  requires SequenceIsRectangle(N, M, a)
  ensures SequenceIsRectangle(N, M, r)
{
  seq(N, i => seq(M, j => if 0 <= i < N && 0 <= j < M
                          then if a[i][j] > 0.0
                               then a[i][j] 
                               else -a[i][j]
                          else 0.0))
}

ghost function {:opaque} MaxSpec
  (N:nat, M:nat, s:seq<seq<real>>): real
  requires SequenceIsRectangle(N, M, s)
  requires N >= 1
  requires M >= 1
  ensures forall i, j :: (0 <= i < N && 0 <= j < M) ==> MaxSpec(N, M, s) >= s[i][j]
  ensures exists i, j :: 0 <= i < N && 0 <= j < M && MaxSpec(N, M, s) == s[i][j]
{
  MaxRecursive(N, M, 0, 0, s[0][0], s)
}

ghost function {:opaque} MaxRecursive
  (N:nat, M:nat, i:nat, j:nat, curr:real, s:seq<seq<real>>): (r: real)
  requires SequenceIsRectangle(N, M, s)
  requires 0 <= i <= N
  requires 0 <= j <= M
  requires exists i', j' :: 0 <= i' < N && 0 <= j' < M && curr == s[i'][j']
  decreases N - i, M - j
  ensures forall i', j' :: (i + 1 <= i' < N && 0 <= j' < M) ==> r >= s[i'][j']
  ensures i < N ==> forall j' :: j <= j' < M ==> r >= s[i][j']
  ensures exists i', j' :: 0 <= i' < N && 0 <= j' < M && r == s[i'][j']
  ensures r >= curr
{
  if i == N then curr 
  else if j == M then MaxRecursive(N, M, i + 1, 0, curr, s)
  else if s[i][j] > curr then MaxRecursive(N, M, i, j + 1, s[i][j], s)
  else MaxRecursive(N, M, i, j + 1, curr, s)
}

ghost function {:opaque} JacobiFull
  (N:nat, curr:seq<seq<real>>, Rhs:seq<seq<real>>): (r:seq<seq<real>>)
  requires SequenceIsSquare(N, curr)
  requires BorderIsZero(N, curr)
  requires SequenceIsSquare(N, Rhs)
  requires N >= 3
  ensures SequenceIsSquare(N, r)
  ensures BorderIsZero(N, r)
  ensures forall i, j :: (1 <= i < N - 1 && 1 <= j < N - 1) 
            ==> r[i][j] == JacobiPoint(N, i, j, curr, Rhs)
{
  JacobiRecursive(N, 1, 1, curr, curr, Rhs)
}

ghost function {:opaque} JacobiRecursive
  (N:nat, i:nat, j:nat, 
   curr:seq<seq<real>>, prev:seq<seq<real>>, Rhs:seq<seq<real>>):
  (r:seq<seq<real>>)
  requires SequenceIsSquare(N, curr)
  requires BorderIsZero(N, curr)
  requires SequenceIsSquare(N, prev)
  requires BorderIsZero(N, prev)
  requires SequenceIsSquare(N, Rhs)
  requires N >= 3
  requires 1 <= i <= N - 1
  requires 1 <= j <= N - 1
  decreases N - i, N - j
  ensures SequenceIsSquare(N, r)
  ensures BorderIsZero(N, r)
  ensures forall i', j' :: (i + 1 <= i' < N - 1 && 1 <= j' < N - 1) 
            ==> r[i'][j'] == JacobiPoint(N, i', j', prev, Rhs)
  ensures forall i', j' :: (i <= i' < N - 1 && j <= j' < N - 1) 
            ==> r[i'][j'] == JacobiPoint(N, i', j', prev, Rhs)
  ensures forall i', j' :: (i <= i' < i + 1 && 1 <= j' < j) 
            ==> r[i'][j'] == curr[i'][j']
  ensures forall i', j' :: (1 <= i' < i && 1 <= j' < N - 1) 
            ==> r[i'][j'] == curr[i'][j']
{
  reveal BorderIsZero;
  if i == N - 1 then curr 
  else if j == N - 1 then JacobiRecursive(N, i + 1, 1, curr, prev, Rhs)
  else JacobiRecursive(N, i, j + 1, 
      curr[i := curr[i][j := JacobiPoint(N, i, j, prev, Rhs)]], prev, Rhs)
}

ghost function {:opaque} JacobiPoint
  (N:nat, i:nat, j:nat, prev:seq<seq<real>>, Rhs:seq<seq<real>>):real
  requires N >= 3
  requires 1 <= i <= N - 2
  requires 1 <= j <= N - 2
  requires SequenceIsSquare(N, prev)
  requires SequenceIsSquare(N, Rhs)
{
  var h:real := 1.0 / ((N - 1) as real);
  (prev[i+1][j] + prev[i-1][j] + 
   prev[i][j+1] + prev[i][j-1] + Rhs[i][j] * (- (h * h))) * 0.25
}

ghost function {:opaque} SpecInitZeros(N:nat): (r:seq<seq<real>>)
  ensures SequenceIsSquare(N, r)
  ensures BorderIsZero(N, r)
{
  reveal BorderIsZero;
  seq(N, i => seq(N, j => 0.0))
}

lemma LemmaSpecInitZeros(N:nat) 
  ensures forall i, j :: (0 <= i < N && 0 <= j < N) 
            ==> SpecInitZeros(N)[i][j] == 0.0
{
  reveal SpecInitZeros;
}

ghost predicate {:opaque} BorderIsZero(N:nat, s:seq<seq<real>>) 
  requires SequenceIsSquare(N, s)
{
  forall i, j :: ((0 <= i < N) && (0 <= j < N) 
               && (i == 0 || i == N - 1 || j == 0 || j == N - 1))
    ==> s[i][j] == 0.0
}

ghost predicate SequenceIsSquare(N:nat, s:seq<seq<real>>) {
  && |s| == N
  && forall i :: 0 <= i < N ==> |s[i]| == N
}

ghost predicate SequenceIsRectangle(N:nat, M:nat, s:seq<seq<real>>) {
  && |s| == N
  && forall i :: 0 <= i < N ==> |s[i]| == M
}

}