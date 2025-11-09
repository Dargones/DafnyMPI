module Spec {

ghost function {:opaque} RhsHelper
  (area:seq<seq<real>>, dim1:nat, dim2:nat, i:nat, j:nat):real 
  requires |area| == dim1
  requires forall i' :: 0 <= i' < dim1 ==> |area[i']| == dim2
  requires 0 <= i < dim1 
  requires 0 <= j < dim2
{
  var west :=  if i > 0 then area[i-1][j] else 0.0;
  var east :=  if i < |area| - 1 then area[i+1][j] else 0.0;
  var south := if j > 0 then area[i][j-1] else 0.0;
  var north := if j < |area[i]| - 1 then area[i][j+1] else 0.0;
  west + east + south + north
}

ghost  function {:opaque} RhsHelperSum
  (area:seq<seq<real>>, dim1:nat, dim2:nat, i:nat, j:nat):real 
  requires |area| == dim1
  requires forall i' :: 0 <= i' < dim1 ==> |area[i']| == dim2
  requires 0 <= i < dim1 
  requires 0 <= j < dim2
{
  RhsHelper(area, dim1, dim2, i, j) - 4.0 * area[i][j]
}

ghost function {:opaque} Laplacian
  (area:seq<seq<real>>, dim1:nat, dim2:nat, i:nat, j:nat, mul:real):real 
  requires |area| == dim1
  requires forall i' :: 0 <= i' < dim1 ==> |area[i']| == dim2
  requires 0 <= i < dim1 
  requires 0 <= j < dim2
{
  RhsHelperSum(area, dim1, dim2, i, j) * mul
}

ghost function {:opaque} Rhs
  (area:seq<seq<real>>, dim1:nat, dim2:nat, i:nat, j:nat, dx:real):real 
  requires dx * dx != 0.0
  requires |area| == dim1
  requires forall i' :: 0 <= i' < dim1 ==> |area[i']| == dim2
  requires 0 <= i < dim1 
  requires 0 <= j < dim2
{
  Laplacian(area, dim1, dim2, i, j, 1.0 / (dx * dx))
}

ghost function {:opaque} RhsRecursive
  (acc:seq<seq<real>>,
   u:seq<seq<real>>,
   dim1:nat, dim2:nat, 
   i:nat, j:nat, 
   dx:real):(r:seq<seq<real>>)
  requires |u| == dim1
  requires |acc| == dim1
  requires forall i' :: 0 <= i' < dim1 ==> |u[i']| == dim2
  requires forall i' :: 0 <= i' < dim1 ==> |acc[i']| == dim2
  requires 0 <= i <= dim1
  requires 0 <= j <= dim2
  requires dx * dx != 0.0
  requires forall i', j' :: (0 <= i' < i && 0 <= j' < dim2)
              ==> acc[i'][j'] == Rhs(u, dim1, dim2, i', j', dx)
  requires i != dim1 ==> 
    (forall j' :: (0 <= j' < j)
      ==> acc[i][j'] == Rhs(u, dim1, dim2, i, j', dx))
  decreases dim1 - i, dim2 - j
  ensures |r| == dim1
  ensures forall i' :: 0 <= i' < dim1 ==> |r[i']| == dim2
  ensures forall i', j' :: (0 <= i' < dim1 && 0 <= j' < dim2)
              ==> r[i'][j'] == Rhs(u, dim1, dim2, i', j', dx)
{
  if      i == dim1 then acc
  else if j == dim2 then RhsRecursive(acc, u, dim1, dim2, i + 1, 0, dx)
  else                   RhsRecursive(acc[i := acc[i]
                                         [j := Rhs(u, dim1, dim2, i, j, dx)]], 
                                      u, dim1, dim2, i, j + 1, dx)
}

ghost function {:opaque} RhsFull(u:seq<seq<real>>, dim1:nat, dim2:nat, dx:real)
  :(r:seq<seq<real>>)
  requires |u| == dim1
  requires forall i :: 0 <= i < dim1 ==> |u[i]| == dim2
  requires dx * dx != 0.0
  ensures |r| == dim1
  ensures forall i :: 0 <= i < dim1 ==> |r[i]| == dim2
  ensures forall i, j :: (0 <= i < dim1 && 0 <= j < dim2)
              ==> r[i][j] == Rhs(u, dim1, dim2, i, j, dx)
{
  reveal Rhs;
  RhsRecursive(u, u, dim1, dim2, 0, 0, dx)
}

ghost function {:opaque} MulConst(u:seq<seq<real>>, dim1:nat, dim2:nat, c:real)
  :(r:seq<seq<real>>)
  requires |u| == dim1
  requires forall i :: 0 <= i < dim1 ==> |u[i]| == dim2
  ensures |r| == dim1
  ensures forall i :: 0 <= i < dim1 ==> |r[i]| == dim2
  ensures forall i, j :: (0 <= i < dim1 && 0 <= j < dim2) ==> 
    r[i][j] == u[i][j] * c
  ensures BorderIsZero(u, dim1, dim2) ==> BorderIsZero(r, dim1, dim2)
{
  reveal BorderIsZero;
  seq<seq<real>>(dim1, 
    i => seq<real>(dim2, 
      j => if 0 <= i < dim1 && 0 <= j < dim2 then u[i][j] * c else 0.0))
}

ghost function {:opaque} AddArraysWithPadding
  (u1:seq<seq<real>>, u2:seq<seq<real>>, dim1:nat, dim2:nat)
  :(r:seq<seq<real>>)
  requires |u1| == dim1
  requires |u2| == dim1
  requires forall i :: 0 <= i < dim1 ==> |u1[i]| == dim2
  requires forall i :: 0 <= i < dim1 ==> |u2[i]| == dim2
  ensures |r| == dim1
  ensures forall i :: 0 <= i < dim1 ==> |r[i]| == dim2
  ensures forall i, j :: (4 <= i < dim1 - 4 && 4 <= j < dim2 - 4) ==> 
    r[i][j] == u1[i][j] + u2[i][j]
  ensures BorderIsZero(u1, dim1, dim2) ==> BorderIsZero(r, dim1, dim2)
{
  reveal BorderIsZero;
  seq<seq<real>>(dim1, 
    i => seq<real>(dim2, 
      j => if 4 <= i < dim1 - 4 && 4 <= j < dim2 - 4 
           then u1[i][j] + u2[i][j] 
           else 0.0))
}

ghost function {:opaque} AddArrays
  (u1:seq<seq<real>>, u2:seq<seq<real>>, dim1:nat, dim2:nat)
  :(r:seq<seq<real>>)
  requires |u1| == dim1
  requires |u2| == dim1
  requires forall i :: 0 <= i < dim1 ==> |u1[i]| == dim2
  requires forall i :: 0 <= i < dim1 ==> |u2[i]| == dim2
  ensures |r| == dim1
  ensures forall i :: 0 <= i < dim1 ==> |r[i]| == dim2
  ensures forall i, j :: (0 <= i < dim1 && 0 <= j < dim2) ==> 
    r[i][j] == u1[i][j] + u2[i][j]
  ensures BorderIsZero(u1, dim1, dim2) && BorderIsZero(u2, dim1, dim2) 
      ==> BorderIsZero(r, dim1, dim2)
{
  reveal BorderIsZero;
  seq<seq<real>>(dim1, 
    i => seq<real>(dim2, 
      j => if 0 <= i < dim1 && 0 <= j < dim2 then u1[i][j] + u2[i][j] else 0.0))
}

ghost function {:opaque} K1
  (u:seq<seq<real>>, dim1:nat, dim2:nat, dx:real, dt:real)
  :(r:seq<seq<real>>)
  requires |u| == dim1
  requires forall i :: 0 <= i < dim1 ==> |u[i]| == dim2
  requires dx * dx != 0.0
  ensures |r| == dim1
  ensures forall i :: 0 <= i < dim1 ==> |r[i]| == dim2
{
  MulConst(RhsFull(u, dim1, dim2, dx), dim1, dim2, dt)
}

ghost function {:opaque} 
  K2(u:seq<seq<real>>, dim1:nat, dim2:nat, dx:real, dt:real)
  :(r:seq<seq<real>>)
  requires |u| == dim1
  requires forall i :: 0 <= i < dim1 ==> |u[i]| == dim2
  requires dx * dx != 0.0
  ensures |r| == dim1
  ensures forall i :: 0 <= i < dim1 ==> |r[i]| == dim2
{
  MulConst(
    RhsFull(
      AddArrays(
        u, 
        MulConst(
          K1(u, dim1, dim2, dx, dt), 
          dim1, dim2, 0.5), 
        dim1, dim2), 
      dim1, dim2, dx), 
    dim1, dim2, dt)
}

ghost function {:opaque} 
  K3(u:seq<seq<real>>, dim1:nat, dim2:nat, dx:real, dt:real)
  :(r:seq<seq<real>>)
  requires |u| == dim1
  requires forall i :: 0 <= i < dim1 ==> |u[i]| == dim2
  requires dx * dx != 0.0
  ensures |r| == dim1
  ensures forall i :: 0 <= i < dim1 ==> |r[i]| == dim2
{
  MulConst(
    RhsFull(
      AddArrays(
        u, 
        MulConst(
          K2(u, dim1, dim2, dx, dt), 
          dim1, dim2, 0.5), 
        dim1, dim2), 
      dim1, dim2, dx), 
    dim1, dim2, dt)
}

ghost function {:opaque} 
  K4(u:seq<seq<real>>, dim1:nat, dim2:nat, dx:real, dt:real)
  :(r:seq<seq<real>>)
  requires |u| == dim1
  requires forall i :: 0 <= i < dim1 ==> |u[i]| == dim2
  requires dx * dx != 0.0
  ensures |r| == dim1
  ensures forall i :: 0 <= i < dim1 ==> |r[i]| == dim2
{
  MulConst(
    RhsFull(
      AddArrays(
        u, 
        K3(u, dim1, dim2, dx, dt), 
        dim1, dim2), 
      dim1, dim2, dx), 
    dim1, dim2, dt)
}

ghost function {:opaque} RK4Step
  (u:seq<seq<real>>, dim1:nat, dim2:nat, dx:real, dt:real)
  :(r:seq<seq<real>>)
  requires |u| == dim1
  requires forall i :: 0 <= i < dim1 ==> |u[i]| == dim2
  requires dx * dx != 0.0
  ensures |r| == dim1
  ensures forall i :: 0 <= i < dim1 ==> |r[i]| == dim2
  ensures BorderIsZero(u, dim1, dim2) ==> BorderIsZero(r, dim1, dim2)
{
  var kCombined := MulConst(
    AddArrays(
      AddArrays( 
        MulConst(
          AddArrays(
            K2(u, dim1, dim2, dx, dt),  
            K3(u, dim1, dim2, dx, dt), 
            dim1, dim2), 
          dim1, dim2, 2.0), 
        K1(u, dim1, dim2, dx, dt), 
        dim1, dim2),
      K4(u, dim1, dim2, dx, dt), 
      dim1, dim2), 
    dim1, dim2, 1.0/6.0);
  AddArraysWithPadding(u, kCombined, dim1, dim2)
}

ghost function {:opaque} SpecOuterHelper(
  n:nat, 
  nt:nat, 
  u:seq<seq<real>>,
  dim1:nat,
  dim2:nat,
  dx:real,
  dt:real)
  :(r:seq<seq<real>>)
  requires |u| == dim1
  requires forall row :: row in u ==> |row| == dim2
  requires dx * dx != 0.0
  requires BorderIsZero(u, dim1, dim2)
  decreases nt - n 
  ensures |r| == dim1
  ensures forall row :: row in r ==> |row| == dim2
  ensures BorderIsZero(r, dim1, dim2)
{
  if n >= nt 
  then u
  else var prev := SpecOuterHelper(n + 1, nt, u, dim1, dim2, dx, dt);
  RK4Step(prev, dim1, dim2, dx, dt)
}

ghost function {:opaque} Spec
  (nx:nat, ny:nat, nt:nat, dim1:nat, dim2:nat, dx:real, dt:real) 
  :(r:seq<seq<real>>)
  requires dx * dx != 0.0
  requires dim1 >= 9
  requires dim2 >= 9
  ensures |r| == dim1
  ensures forall row :: row in r ==> |row| == dim2
  ensures BorderIsZero(r, dim1, dim2)
{
  SpecOuterHelper(0, nt, SpecInit(nx, ny, dim1, dim2), dim1, dim2, dx, dt)
}

ghost predicate {:opaque} BorderIsZero(u:seq<seq<real>>, dim1:nat, dim2:nat) 
  requires |u| == dim1
  requires forall row :: row in u ==> |row| == dim2
{
  forall i, j :: 
    (0 <= i < dim1 && 0 <= j < dim2
      && (i < 4 || i >= dim1 - 4 || j < 4 || j >= dim2 - 4))
    ==> u[i][j] == 0.0
}

function {:axiom} {:opaque} SpecInit(nx:nat, ny:nat, dim1:nat, dim2:nat)
  :(r:seq<seq<real>>)
  requires dim1 >= 9
  requires dim2 >= 9
  ensures |r| == dim1
  ensures forall row :: row in r ==> |row| == dim2
  ensures BorderIsZero(r, dim1, dim2)
{
  reveal BorderIsZero;
  seq(dim1, i => seq(dim2, j => ValueAtPoint(i, j, dim1, dim2)))
}

function absDiff(a:int, b:int):nat {
  if a > b then a - b else b - a
}

function ValueAtPoint(i:int, j:int, dim1:nat, dim2:nat):real
  requires dim1 >= 9
  requires dim2 >= 9
  ensures (0 <= i < dim1 && 0 <= j < dim2
      && (i < 4 || i >= dim1 - 4 || j < 4 || j >= dim2 - 4))
    ==> ValueAtPoint(i, j, dim1, dim2) == 0.0
{
  if (i < 4 || i >= dim1 - 4 || j < 4 || j >= dim2 - 4) 
  then 0.0
  else if (i > dim1 / 4) && (i < 3 * dim1 / 4) 
       && (j > dim2 / 4) && (j < 3 * dim2 / 4)
       then 1.0
       else 0.0
}
  
}