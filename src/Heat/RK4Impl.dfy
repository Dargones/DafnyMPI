include "../DafnyMPI/Externs/MPIResource.dfy"
include "../DafnyMPI/Arrays2D.dfy"
include "Spec.dfy"

module RK4Impl {

  import opened MPIResource
  import opened Arrays2D
  import opened Spec

  lemma LemmaArrayMult(
    u1:ArrayOfReals2D, 
    u2:ArrayOfReals2D, 
    s:seq<seq<real>>, dim1:nat, dim2:nat, c:real, padding:nat, sx:nat, sy:nat) 
    requires u1.IsValid()
    requires u2.IsValid()
    requires u1.dim1 == u2.dim1
    requires u1.dim2 == u2.dim2
    requires dim1 >= u1.dim1 + sx
    requires dim2 >= u1.dim2 + sy
    requires |s| == dim1
    requires forall i :: 0 <= i < |s| ==> |s[i]| == dim2
    requires forall i, j :: (padding <= i < u2.dim1 - padding 
                          && padding <= j < u2.dim2 - padding)
                          ==> u2.Repr2D[i][j] == u1.Repr2D[i][j] * c
    requires EqualWithPadding(u1, s, dim1, dim2, padding, sx, sy)
    requires |s| == dim1
    ensures EqualWithPadding(u2, 
      Spec.MulConst(s, dim1, dim2, c), dim1, dim2, padding, sx, sy)
  {
    reveal EqualWithPadding;
  }

  lemma LemmaAddArrays(
    u1:ArrayOfReals2D, 
    u2:ArrayOfReals2D, 
    u3:ArrayOfReals2D,
    dim1:nat, dim2:nat,
    s1:seq<seq<real>>, s2:seq<seq<real>>, padding:nat, sx:nat, sy:nat) 
    requires u1.IsValid()
    requires u2.IsValid()
    requires u3.IsValid()
    requires u1.dim1 == u2.dim1
    requires u1.dim2 == u2.dim2
    requires u1.dim1 == u3.dim1
    requires u1.dim2 == u3.dim2
    requires dim1 >= u1.dim1 + sx
    requires dim2 >= u1.dim2 + sy
    requires |s1| == dim1
    requires forall i :: 0 <= i < |s1| ==> |s1[i]| == dim2
    requires |s2| == dim1
    requires forall i :: 0 <= i < |s2| ==> |s2[i]| == dim2
    requires forall i, j :: (padding <= i < u3.dim1 - padding 
                          && padding <= j < u3.dim2 - padding)
                 ==> u3.Repr2D[i][j] == u1.Repr2D[i][j] + u2.Repr2D[i][j]
    requires EqualWithPadding(u1, s1, dim1, dim2, padding, sx, sy)
    requires EqualWithPadding(u2, s2, dim1, dim2, padding, sx, sy)
    ensures EqualWithPadding(u3, 
      Spec.AddArrays(s1, s2, dim1, dim2), dim1, dim2, padding, sx, sy)
  {
    reveal EqualWithPadding;
  }

  lemma LemmaRhs
    (u:ArrayOfReals2D, uNew:ArrayOfReals2D, laplacian:ArrayOfReals2D, dx:real, 
     uSpec:seq<seq<real>>, dim1:nat, dim2:nat, padding:nat, sx:nat, sy:nat)
    requires dx * dx != 0.0 
    requires u.IsValid()
    requires laplacian.IsValid()
    requires uNew.IsValid()
    requires u.dim1 == laplacian.dim1
    requires u.dim2 == laplacian.dim2
    requires u.dim1 == uNew.dim1
    requires u.dim2 == uNew.dim2
    requires dim1 >= u.dim1 + sx
    requires dim2 >= u.dim2 + sy
    requires |uSpec| == dim1
    requires forall i :: 0 <= i < |uSpec| ==> |uSpec[i]| == dim2
    requires EqualWithPadding(u, uSpec, dim1, dim2, padding, sx, sy)
    requires forall i, j :: (padding + 1 <= i < u.dim1 - padding - 1 
                          && padding + 1 <= j < u.dim2 - padding - 1) 
               ==> (laplacian.Repr2D[i][j] 
                == Laplacian(uSpec, dim1, dim2, i + sx, j + sy, 1.0/(dx * dx)))
    requires forall i, j :: (0 <= i < u.dim1 && 0 <= j < u.dim2) 
                ==> uNew.Repr2D[i][j] == laplacian.Repr2D[i][j]
    ensures forall i, j :: (padding + 1 <= i < u.dim1 - padding - 1 
                         && padding + 1 <= j < u.dim2 - padding - 1) 
              ==> uNew.Repr2D[i][j] == 
                  Spec.Rhs(uSpec, dim1, dim2, i + sx, j + sy, dx)
  {
    reveal Spec.Rhs;
    reveal EqualWithPadding;
  }

  lemma LemmaLaplacianHelper
    (sum:ArrayOfReals2D, laplacian:ArrayOfReals2D, dx:real, dxSquare:real, 
     uSpec:seq<seq<real>>, dim1:nat, dim2:nat, padding:nat, sx:nat, sy:nat)
    requires dx * dx != 0.0 
    requires dxSquare == 1.0 / (dx * dx)
    requires laplacian.IsValid()
    requires sum.IsValid()
    requires laplacian.dim1 == sum.dim1
    requires laplacian.dim2 == sum.dim2
    requires dim1 >= sum.dim1 + sx
    requires dim2 >= sum.dim2 + sy
    requires |uSpec| == dim1
    requires forall i :: 0 <= i < |uSpec| ==> |uSpec[i]| == dim2
    requires forall i, j :: (0 <= i < sum.dim1 && 0 <= j < sum.dim2) 
                ==> laplacian.Repr2D[i][j] == sum.Repr2D[i][j] * dxSquare
    requires forall i, j :: (padding <= i < sum.dim1 - padding 
                          && padding <= j < sum.dim2 - padding) 
                ==> sum.Repr2D[i][j] == 
                    RhsHelperSum(uSpec, dim1, dim2, i + sx,j + sy)
    ensures forall i, j :: (padding <= i < sum.dim1 - padding 
                         && padding <= j < sum.dim2 - padding) 
                ==> (laplacian.Repr2D[i][j] 
                 == Laplacian(uSpec, dim1, dim2, i + sx, j + sy, 1.0/(dx * dx)))
  {
    reveal Laplacian;
    reveal EqualWithPadding;
  }

  lemma LemmaRhsHelper
    (u:ArrayOfReals2D, uSpec:seq<seq<real>>, sum:ArrayOfReals2D, 
     rollXLeft:ArrayOfReals2D, rollXRight:ArrayOfReals2D,
     rollYLeft:ArrayOfReals2D, rollYRight:ArrayOfReals2D, 
     dim1:nat, dim2:nat, padding:nat, sx:nat, sy:nat) 
    requires u.dim1 > 1
    requires u.dim2 > 1
    requires u.dim1 == sum.dim1
    requires u.dim1 == rollXLeft.dim1
    requires u.dim1 == rollXRight.dim1
    requires u.dim1 == rollYLeft.dim1
    requires u.dim1 == rollYRight.dim1
    requires u.dim2 == sum.dim2
    requires u.dim2 == rollXLeft.dim2
    requires u.dim2 == rollXRight.dim2
    requires u.dim2 == rollYLeft.dim2
    requires u.dim2 == rollYRight.dim2
    requires dim1 >= u.dim1 + sx
    requires dim2 >= u.dim2 + sy
    requires |uSpec| == dim1
    requires forall i :: 0 <= i < |uSpec| ==> |uSpec[i]| == dim2
    requires padding + 1 <= u.dim1 - padding - 1
    requires padding + 1 <= u.dim2 - padding - 1
    requires u.IsValid()
    requires sum.IsValid()
    requires rollXLeft.IsValid()
    requires rollXRight.IsValid()
    requires rollYLeft.IsValid()
    requires rollYRight.IsValid()
    requires EqualWithPadding(u, uSpec, dim1, dim2, padding, sx, sy)
    requires forall i, j :: (0 <= i < u.dim1 && 0 <= j < u.dim2) 
               ==> rollYLeft.Repr2D[i][j] == if j < |u.Repr2D[i]| - 1 
                                           then u.Repr2D[i][j + 1] 
                                           else u.Repr2D[i][0]
    // very annoying but for whatever reason Danfy doesn't select the
    // right trigger on rollXLeft
    requires forall i, j {:trigger rollXLeft.Repr2D[i][j]} :: 
               (0 <= i < u.dim1 && 0 <= j < u.dim2) 
               ==> rollXLeft.Repr2D[i][j] == if i < |u.Repr2D| - 1 
                                           then u.Repr2D[i + 1][j] 
                                           else u.Repr2D[0][j]
    requires forall i, j :: (0 <= i < u.dim1 && 0 <= j < u.dim2) 
               ==> rollXRight.Repr2D[i][j] == if i > 0 
                                            then u.Repr2D[i - 1][j] 
                                            else u.Repr2D[u.dim1 - 1][j]
    requires forall i, j :: (0 <= i < u.dim1 && 0 <= j < u.dim2) 
               ==> rollYRight.Repr2D[i][j] == if j > 0 
                                            then u.Repr2D[i][j - 1] 
                                            else u.Repr2D[i][u.dim2 - 1]
    requires forall i, j :: (0 <= i < u.dim1 && 0 <= j < u.dim2) 
                ==> sum.Repr2D[i][j] == rollXRight.Repr2D[i][j] 
                                    + rollXLeft.Repr2D[i][j] 
                                    + rollYRight.Repr2D[i][j] 
                                    + rollYLeft.Repr2D[i][j]
    ensures forall i, j :: (padding + 1 <= i < u.dim1 - padding - 1 
                         && padding + 1 <= j < u.dim2 - padding - 1) 
             ==> sum.Repr2D[i][j]
                 == RhsHelper(uSpec, dim1, dim2, i + sx,j + sy)
  {
    for i := padding + 1 to u.dim1 - padding - 1
      invariant forall i', j' :: (padding + 1 <= i' < i 
                               && padding + 1 <= j' < u.dim2 - padding - 1) 
                  ==> (sum.Repr2D[i'][j'] 
                    == RhsHelper(uSpec, dim1, dim2, i' + sx, j' + sy))
    {
      for j := padding + 1 to u.dim2 - padding - 1
        invariant forall i', j' :: (padding + 1 <= i' < i 
                                 && padding + 1 <= j' < u.dim2 - padding - 1) 
                     ==> (sum.Repr2D[i'][j'] 
                       == RhsHelper(uSpec, dim1, dim2, i' + sx, j' + sy))
        invariant forall j' :: && padding + 1 <= j' < j
                     ==> (sum.Repr2D[i][j'] 
                       == RhsHelper(uSpec, dim1, dim2, i + sx, j' + sy))
      {
        reveal EqualWithPadding;
        var west :=  if i + sx > 0 then uSpec[i-1 + sx][j + sy] else 0.0;
        assert west == rollXRight.Repr2D[i][j];
        var east :=  if i + sx < |uSpec| - 1 
                     then uSpec[i+1 +sx][j + sy] else 0.0;
        assert east == rollXLeft.Repr2D[i][j];
        var south := if j + sy > 0 then uSpec[i + sx][j-1 + sy] else 0.0;
        assert south == rollYRight.Repr2D[i][j];
        var north := if j + sy < |uSpec[i + sx]| - 1 
                     then uSpec[i + sx][j+1 + sy] else 0.0;
        assert north == rollYLeft.Repr2D[i][j];
        reveal RhsHelper;
        assert sum.Repr2D[i][j] == RhsHelper(uSpec, dim1, dim2, i + sx, j + sy);
      }
    }
  }

  method Rhs
    (u:ArrayOfReals2D, ghost uSpec:seq<seq<real>>, dim1:nat, dim2:nat,
     dx:real, padding:nat, sx:nat, sy:nat)
    returns (uNew:ArrayOfReals2D)
    requires dx * dx != 0.0
    requires u.dim1 >= padding
    requires u.dim2 >= padding
    requires padding + 1 <= u.dim1 - padding - 1
    requires padding + 1 <= u.dim2 - padding - 1
    requires u.dim1 > 1
    requires u.dim2 > 1
    requires u.IsValid()
    requires u.FreeToWrite(0, u.length)
    requires dim1 >= u.dim1 + sx
    requires dim2 >= u.dim2 + sy
    requires |uSpec| == dim1
    requires forall i :: 0 <= i < |uSpec| ==> |uSpec[i]| == dim2
    requires EqualWithPadding(u, uSpec, dim1, dim2, padding, sx, sy)
    ensures uNew.dim1 == u.dim1
    ensures uNew.dim2 == u.dim2
    ensures uNew.IsValid()
    ensures EqualWithPadding(uNew, 
       RhsFull(uSpec, dim1, dim2, dx), dim1, dim2, padding+1, sx, sy)
    ensures uNew.FreeToWrite(0, uNew.length)
  {
    reveal ArrayOfReals2D.FreeToWriteStatic;
    reveal ArrayOfReals2D.FreeToReadStatic;
    reveal EqualWithPadding;
    reveal RhsHelperSum;
    reveal RhsHelper;
    var rollXLeft :=  Roll(u, -1, 0);
    var rollXRight := Roll(u, 1, 0);
    var rollYLeft :=  Roll(u, 0, -1);
    var rollYRight := Roll(u, 0, 1);
    var sum := Arrays2D.AddArrays(rollXLeft, rollXRight);
    sum := Arrays2D.AddArrays(sum, rollYLeft);
    sum := Arrays2D.AddArrays(sum, rollYRight);
    reveal Arrays2D.RollHelper;
    LemmaRhsHelper(u, uSpec, sum, rollXLeft, rollXRight, rollYLeft, rollYRight, 
                   dim1, dim2, padding, sx, sy);
    var uTimes4   :=  Arrays2D.MulConst(u, -4.0);
    sum := Arrays2D.AddArrays(sum, uTimes4);
    assert forall i, j :: (padding + 1 <= i < u.dim1 - padding - 1 
                        && padding + 1 <= j < u.dim2 - padding - 1) 
             ==> sum.Repr2D[i][j] 
                 == RhsHelperSum(uSpec, dim1, dim2, i + sx, j + sy);
    var dxSq := 1.0 / (dx * dx);
    var laplacian := Arrays2D.MulConst(sum, dxSq);
    LemmaLaplacianHelper(sum, laplacian, dx, dxSq, 
                         uSpec, dim1, dim2, padding+1, sx, sy);
    uNew := laplacian;
    LemmaRhs(u, uNew, laplacian, dx, uSpec, dim1, dim2, padding, sx, sy);
  }

  method {:timeLimit 40} RK4Step
    (u:ArrayOfReals2D, ghost uSpec:seq<seq<real>>, dim1:nat, dim2:nat,
     dx:real, dt:real, sx:nat, sy:nat) 
    returns (uNew:ArrayOfReals2D)
    requires u.IsValid()
    requires u.dim1 >= 9
    requires u.dim2 >= 9
    requires u.FreeToWrite(0, u.length)
    requires dim1 >= u.dim1 + sx
    requires dim2 >= u.dim2 + sy
    requires |uSpec| == dim1 
    requires forall i :: 0 <= i < |uSpec| ==> |uSpec[i]| == dim2
    requires dx * dx != 0.0
    requires EqualWithPadding(u, uSpec, dim1, dim2, 0, sx, sy)
    ensures uNew.IsValid()
    ensures uNew.dim1 == u.dim1
    ensures uNew.dim2 == u.dim2
    ensures EqualWithPadding(uNew, 
      Spec.RK4Step(uSpec, dim1, dim2, dx, dt), dim1, dim2, 4, sx, sy)
    ensures fresh(uNew)
    ensures uNew.FreeToWrite(0, uNew.length)
  {
    reveal ArrayOfReals2D.FreeToWriteStatic;
    reveal ArrayOfReals2D.FreeToReadStatic;
    var k1Step1 := Rhs(u, uSpec, dim1, dim2, dx, 0, sx, sy);
    var k1 := Arrays2D.MulConst(k1Step1, dt);
    LemmaArrayMult(k1Step1, k1, 
                   RhsFull(uSpec, dim1, dim2, dx), dim1, dim2, dt, 1, sx, sy);
    assert EqualWithPadding(k1, 
      K1(uSpec, dim1, dim2, dx, dt), dim1, dim2, 1, sx, sy) by {
      reveal K1;
      reveal EqualWithPadding;
    }
    var tmp := K1(uSpec, dim1, dim2, dx, dt);

    var k2Step1 := Arrays2D.MulConst(k1, 0.5);
    LemmaArrayMult(k1, k2Step1, tmp, dim1, dim2, 0.5, 1, sx, sy);
    tmp := Spec.MulConst(tmp, dim1, dim2, 0.5);

    var k2Step2 := Arrays2D.AddArrays(u, k2Step1);
    LemmaEqualWithPaddingInc(u, uSpec, dim1, dim2, 0, 1, sx, sy);
    LemmaAddArrays(u, k2Step1, k2Step2, 
                   dim1, dim2, uSpec, tmp, 1, sx, sy);
    tmp := Spec.AddArrays(uSpec, tmp, dim1, dim2);

    var k2Step3 := Rhs(k2Step2, tmp, dim1, dim2, dx, 1, sx, sy);
    tmp := RhsFull(tmp, dim1, dim2, dx);

    var k2 := Arrays2D.MulConst(k2Step3, dt);
    LemmaArrayMult(k2Step3, k2, tmp, dim1, dim2, dt, 2, sx, sy);
    assert EqualWithPadding(k2, 
      K2(uSpec, dim1, dim2, dx, dt), dim1, dim2, 2, sx, sy) by {
      reveal K2;
      reveal EqualWithPadding;
    }
    tmp := K2(uSpec, dim1, dim2, dx, dt);
    
    var k3Step1 := Arrays2D.MulConst(k2, 0.5);
    LemmaArrayMult(k2, k3Step1, tmp, dim1, dim2, 0.5, 2, sx, sy);
    tmp := Spec.MulConst(tmp, dim1, dim2, 0.5);

    var k3Step2 := Arrays2D.AddArrays(u, k3Step1);
    LemmaEqualWithPaddingInc(u, uSpec, dim1, dim2, 0, 2, sx, sy);
    LemmaAddArrays(u, k3Step1, k3Step2, 
                   dim1, dim2, uSpec, tmp, 2, sx, sy);
    tmp := Spec.AddArrays(uSpec, tmp, dim1, dim2);

    var k3Step3 := Rhs(k3Step2, tmp, dim1, dim2, dx, 2, sx, sy);
    tmp := RhsFull(tmp, dim1, dim2, dx);

    var k3 := Arrays2D.MulConst(k3Step3, dt);
    LemmaArrayMult(k3Step3, k3, tmp, dim1, dim2, dt, 3, sx, sy);
    assert EqualWithPadding(k3, 
      K3(uSpec, dim1, dim2, dx, dt), dim1, dim2, 3, sx, sy) by {
      reveal K3;
      reveal EqualWithPadding;
    }
    tmp := K3(uSpec, dim1, dim2, dx, dt);

    var k4Step1 := Arrays2D.AddArrays(k3, u);
    LemmaEqualWithPaddingInc(u, uSpec, dim1, dim2, 0, 3, sx, sy);
    LemmaAddArrays(u, k3, k4Step1, dim1, dim2, uSpec, tmp, 3, sx, sy);
    tmp := Spec.AddArrays(uSpec, tmp, dim1, dim2);

    var k4Step2 := Rhs(k4Step1, tmp, dim1, dim2, dx, 3, sx, sy);
    tmp := RhsFull(tmp, dim1, dim2, dx);

    var k4 := Arrays2D.MulConst(k4Step2, dt);
    LemmaArrayMult(k4Step2, k4, tmp, dim1, dim2, dt, 4, sx, sy);
    assert EqualWithPadding(k4, 
      K4(uSpec, dim1, dim2, dx, dt), dim1, dim2, 4, sx, sy) by {
      reveal K4;
      reveal EqualWithPadding;
    }
    tmp := K4(uSpec, dim1, dim2, dx, dt);

    var sumStep1 := Arrays2D.AddArrays(k2, k3);
    LemmaEqualWithPaddingInc(k2, 
      K2(uSpec, dim1, dim2, dx, dt), dim1, dim2, 2, 4, sx, sy);
    LemmaEqualWithPaddingInc(k3, 
      K3(uSpec, dim1, dim2, dx, dt), dim1, dim2, 3, 4, sx, sy);
    LemmaAddArrays(k2, k3, sumStep1, dim1, dim2, 
                     K2(uSpec, dim1, dim2, dx, dt), 
                     K3(uSpec, dim1, dim2, dx, dt), 4, sx, sy);
    tmp := Spec.AddArrays(K2(uSpec, dim1, dim2, dx, dt),
                          K3(uSpec, dim1, dim2, dx, dt), 
                          dim1, dim2);

    var sumStep2 := Arrays2D.MulConst(sumStep1, 2.0);
    LemmaArrayMult(sumStep1, sumStep2, tmp, dim1, dim2, 2.0, 4, sx, sy);
    tmp := Spec.MulConst(tmp, dim1, dim2, 2.0);

    var sumStep3 := Arrays2D.AddArrays(sumStep2, k1);
    LemmaEqualWithPaddingInc(k1, 
      K1(uSpec, dim1, dim2, dx, dt), dim1, dim2, 1, 4, sx, sy);
    LemmaAddArrays(sumStep2, k1, sumStep3, dim1, dim2, 
                  tmp, K1(uSpec, dim1, dim2, dx, dt), 4, sx, sy);
    tmp := Spec.AddArrays(tmp, K1(uSpec, dim1, dim2, dx, dt), 
                          dim1, dim2);

    var sumStep4 := Arrays2D.AddArrays(sumStep3, k4);
    LemmaAddArrays(sumStep3, k4, sumStep4, dim1, dim2, 
                  tmp, K4(uSpec, dim1, dim2, dx, dt), 4, sx, sy);
    tmp := Spec.AddArrays(tmp, 
                          K4(uSpec, dim1, dim2, dx, dt), dim1, dim2);

    var sum := Arrays2D.MulConst(sumStep4, 1.0/6.0);
    LemmaArrayMult(sumStep4, sum, tmp, dim1, dim2, 1.0/6.0, 4, sx, sy);
    tmp := Spec.MulConst(tmp, dim1, dim2, 1.0/6.0);

    uNew := Arrays2D.AddArrays(u, sum);
    LemmaEqualWithPaddingInc(u, uSpec, dim1, dim2, 0, 4, sx, sy);
    LemmaAddArrays(u, sum, uNew, dim1, dim2, uSpec, tmp, 4, sx, sy);
    tmp := Spec.AddArrays(uSpec, tmp, dim1, dim2);

    reveal Spec.RK4Step;
    reveal EqualWithPadding;
  }
}