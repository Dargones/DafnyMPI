include "Externs/MPIResource.dfy"

module Arrays1D {

  import opened MPIResource

  method Ones(length:nat) 
    returns (arr:ArrayOfReals) 
    ensures arr.length == length
    ensures forall i :: 0 <= i < |arr.Repr| ==> arr.Repr[i] == 1.0
    ensures fresh(arr)
    ensures arr.IsValid()
    ensures arr.FreeToWrite(0, arr.length)
  {
    arr := new ArrayOfReals(length, 1.0);
  }

  method Zeros(length:nat) 
    returns (arr:ArrayOfReals) 
    ensures arr.length == length
    ensures forall i :: 0 <= i < |arr.Repr| ==> arr.Repr[i] == 0.0
    ensures fresh(arr)
    ensures arr.IsValid()
    ensures arr.FreeToWrite(0, arr.length)
  {
    arr := new ArrayOfReals(length, 0.0);
  }

  method Copy(arr:ArrayOfReals) returns (arr2:ArrayOfReals) 
    requires arr.IsValid()
    requires arr.FreeToRead(0, arr.length)
    ensures arr2.Repr == arr.Repr
    ensures fresh(arr2)
    ensures arr2.IsValid()
    ensures arr2.FreeToWrite(0, arr.length)
  {
    reveal ArrayOfReals.FreeToReadStatic;
    reveal ArrayOfReals.FreeToWriteStatic;
    arr2 := Zeros(arr.Length());
    for i := 0 to arr.Length() 
      invariant arr2.IsValid()
      invariant arr2.FreeToWrite(0, arr.length)
      invariant arr2.length == arr.length
      invariant arr2.Repr[..i] == arr.Repr[..i]
    {
      arr2.Set(i, arr.Get(i));
    }
  }

  method SetRange(arr:ArrayOfReals, lower:nat, upper:nat, val:real)
    requires lower <= upper <= |arr.Repr|
    requires arr.IsValid()
    requires arr.FreeToWrite(lower, upper)
    modifies arr
    ensures arr.IsValid()
    ensures arr.WriteLock == old(arr.WriteLock)
    ensures arr.ReadLocks == old(arr.ReadLocks)
    ensures forall i :: lower <= i < upper ==> arr.Repr[i] == val
    ensures forall i :: (0 <= i < lower || |arr.Repr| > i >= upper) 
                    ==> arr.Repr[i] == old(arr.Repr[i])
  {
    reveal ArrayOfReals.FreeToReadStatic;
    reveal ArrayOfReals.FreeToWriteStatic;
    for i := lower to upper 
      invariant arr.WriteLock == old(arr.WriteLock)
      invariant arr.ReadLocks == old(arr.ReadLocks)
      invariant |arr.Repr| == old(|arr.Repr|)
      invariant forall j :: (0 <= j < lower || |arr.Repr| > j >= upper) 
                        ==> arr.Repr[j] == old(arr.Repr[j])
      invariant forall j :: lower <= j < i ==> arr.Repr[j] == val
    {
      arr.Set(i, val);
    }
  }

  method Slice
    (arr1:ArrayOfReals, lower:nat, upper:nat)
    returns (arr2:ArrayOfReals)
    requires lower < upper <= arr1.length
    requires arr1.IsValid()
    requires arr1.FreeToRead(lower, upper)
    ensures arr2.IsValid()
    ensures fresh(arr2)
    ensures arr2.length == upper - lower
    ensures forall i :: (0 <= i < arr2.length)
                        ==> arr2.Repr[i] == arr1.Repr[i + lower]
    ensures arr2.FreeToWrite(0, arr2.length)
  {
    reveal ArrayOfReals.FreeToReadStatic;
    reveal ArrayOfReals.FreeToWriteStatic;
    arr2 := new ArrayOfReals(upper-lower, 0.0);
    for i := 0 to upper - lower
      invariant arr2.IsValid()
      invariant arr2.length == upper-lower
      invariant arr2.FreeToWrite(0, arr2.length)
      invariant forall j :: 0 <= j < i ==> arr2.Repr[j] == arr1.Repr[j + lower] 
    {
      arr2.Set(i, arr1.Get(i + lower));       
    }
  }

  method EditConst
    (arr1:ArrayOfReals, F:real -> real) 
    returns (arr2:ArrayOfReals)
    requires arr1.IsValid()
    requires arr1.FreeToRead(0, arr1.length)
    ensures arr2.length == arr1.length
    ensures arr2.IsValid()
    ensures fresh(arr2)
    ensures forall i :: 0 <= i < arr1.length ==> 
      arr2.Repr[i] == F(arr1.Repr[i])
    ensures arr2.FreeToWrite(0, arr2.length)
  {
    reveal ArrayOfReals.FreeToReadStatic;
    reveal ArrayOfReals.FreeToWriteStatic;
    arr2 := new ArrayOfReals(arr1.Length(), 0.0);
    for i := 0 to arr1.Length()
      invariant arr2.IsValid()
      invariant arr2.length == arr1.length
      invariant arr2.FreeToWrite(0, arr2.length)
      invariant forall j :: 0 <= j < i ==> arr2.Repr[j] == F(arr1.Repr[j])
    {
      arr2.Set(i, F(arr1.Get(i)));       
    }
  }

  method AddConst(arr1:ArrayOfReals, c:real) 
    returns (arr2:ArrayOfReals)
    requires arr1.IsValid()
    requires arr1.FreeToRead(0, arr1.length)
    ensures arr2.length == arr1.length
    ensures arr2.IsValid()
    ensures arr2.FreeToWrite(0, arr2.length)
    ensures fresh(arr2)
    ensures forall i :: 0 <= i < arr1.length ==> 
      arr2.Repr[i] == arr1.Repr[i] + c
  {
    arr2 := EditConst(arr1, r => r + c);
  }

  method MulConst(arr1:ArrayOfReals, c:real) 
    returns (arr2:ArrayOfReals)
    requires arr1.IsValid()
    requires arr1.FreeToRead(0, arr1.length)
    ensures arr2.length == arr1.length
    ensures arr2.IsValid()
    ensures arr2.FreeToWrite(0, arr1.length)
    ensures fresh(arr2)
    ensures forall i :: 0 <= i < arr1.length ==> 
      arr2.Repr[i] == arr1.Repr[i] * c
  {
    arr2 := EditConst(arr1, r => r * c);
  }

  method MergeArrays
    (arr1:ArrayOfReals, arr2:ArrayOfReals, F:(real, real) -> real) 
    returns (arr3:ArrayOfReals)
    requires arr1.IsValid()
    requires arr2.IsValid()
    requires arr1.FreeToRead(0, arr1.length)
    requires arr2.FreeToRead(0, arr2.length)
    requires arr2.length == arr1.length
    ensures arr3.IsValid()
    ensures fresh(arr3)
    ensures arr3.length == arr1.length
    ensures arr3.FreeToWrite(0, arr3.length)
    ensures forall i :: 0 <= i < arr3.length ==> 
      arr3.Repr[i] == F(arr1.Repr[i], arr2.Repr[i])
  {
    reveal ArrayOfReals.FreeToReadStatic;
    reveal ArrayOfReals.FreeToWriteStatic;
    arr3 := new ArrayOfReals(arr1.Length(), 0.0);
    for i := 0 to arr1.Length()
      invariant arr3.IsValid()
      invariant arr3.length == arr1.length
      invariant arr3.FreeToWrite(0, arr3.length)
      invariant forall j :: 0 <= j < i 
                    ==> arr3.Repr[j] == F(arr1.Repr[j], arr2.Repr[j])
    {
      arr3.Set(i, F(arr1.Get(i), arr2.Get(i)));       
    }
  }

  method AddArrays
    (arr1:ArrayOfReals, arr2:ArrayOfReals, F:(real, real) -> real) 
    returns (arr3:ArrayOfReals)
    requires arr1.IsValid()
    requires arr2.IsValid()
    requires arr1.FreeToRead(0, arr1.length)
    requires arr2.FreeToRead(0, arr2.length)
    requires arr2.length == arr1.length
    ensures arr3.IsValid()
    ensures arr3.FreeToWrite(0, arr3.length)
    ensures fresh(arr3)
    ensures arr3.length == arr1.length
    ensures forall i :: 0 <= i < arr3.length ==> 
      arr3.Repr[i] == arr1.Repr[i] + arr2.Repr[i]
  {
    arr3 := MergeArrays(arr1, arr2, (r1, r2) => r1 + r2);
  }

  method MulArrays
    (arr1:ArrayOfReals, arr2:ArrayOfReals, F:(real, real) -> real) 
    returns (arr3:ArrayOfReals)
    requires arr1.IsValid()
    requires arr2.IsValid()
    requires arr1.FreeToRead(0, arr1.length)
    requires arr2.FreeToRead(0, arr2.length)
    requires arr2.length == arr1.length
    ensures arr3.IsValid()
    ensures arr3.FreeToWrite(0, arr3.length)
    ensures fresh(arr3)
    ensures arr3.length == arr1.length
    ensures forall i :: 0 <= i < arr3.length ==> 
      arr3.Repr[i] == arr1.Repr[i] * arr2.Repr[i]
  {
    arr3 := MergeArrays(arr1, arr2, (r1, r2) => r1 * r2);
  }

  method RollInternal(arr1:ArrayOfReals, dist:nat) 
    returns (arr2:ArrayOfReals)
    requires arr1.IsValid()
    requires dist < arr1.length
    requires arr1.FreeToRead(0, arr1.length)
    ensures arr2.IsValid()
    ensures arr2.FreeToWrite(0, arr2.length)
    ensures fresh(arr2)
    ensures arr2.length == arr1.length
    ensures forall i :: dist <= i < arr2.length ==> 
      arr2.Repr[i] == arr1.Repr[i - dist]
    ensures forall i :: 0 <= i < dist ==> 
      arr2.Repr[i] == arr1.Repr[i + arr1.length - dist]
  {
    reveal ArrayOfReals.FreeToReadStatic;
    reveal ArrayOfReals.FreeToWriteStatic;
    arr2 := new ArrayOfReals(arr1.Length(), 0.0);
    for i := 0 to dist
      invariant arr2.IsValid()
      invariant arr2.length == arr1.length
      invariant arr2.FreeToWrite(0, arr2.length)
      invariant forall j :: 0 <= j < i 
                    ==> arr2.Repr[j] == arr1.Repr[j + arr1.length - dist]
    {
      arr2.Set(i, arr1.Get(i + arr1.Length() - dist));       
    }
    for i := dist to arr1.Length()
      invariant arr2.IsValid()
      invariant arr2.length == arr1.length
      invariant arr2.FreeToWrite(0, arr2.length)
      invariant forall j :: 0 <= j < dist
                    ==> arr2.Repr[j] == arr1.Repr[j + arr1.length - dist]
      invariant forall j :: dist <= j < i
                    ==> arr2.Repr[j] == arr1.Repr[j - dist]
    {
      arr2.Set(i, arr1.Get(i - dist));       
    }
  }

  method Roll(arr1:ArrayOfReals, dist:int) 
    returns (arr2:ArrayOfReals)
    requires arr1.IsValid()
    requires arr1.FreeToRead(0, arr1.length)
    requires -(arr1.length as int) < dist < arr1.length
    ensures arr2.IsValid()
    ensures arr2.FreeToWrite(0, arr2.length)
    ensures fresh(arr2)
    ensures arr2.length == arr1.length
    ensures var distReal := if dist >= 0 then dist else arr1.length + dist;
      forall i :: distReal <= i < arr2.length ==> 
        arr2.Repr[i] == arr1.Repr[i - distReal]
    ensures var distReal := if dist >= 0 then dist else arr1.length + dist;
      forall i :: 0 <= i < distReal ==> 
        arr2.Repr[i] == arr1.Repr[i + arr1.length - distReal]
  {
    var distReal := if dist >= 0 then dist else arr1.Length() + dist;
    arr2 := RollInternal(arr1, distReal);
  }

  method SetSlice
    (arr1:ArrayOfReals, arr2:ArrayOfReals, 
      lower1:nat, upper1:nat, lower2:nat, upper2:nat)
    requires lower1 <= upper1 <= arr1.length
    requires lower2 <= upper2 <= arr2.length
    requires upper1 - lower1 == upper2 - lower2
    requires arr1 != arr2
    requires arr1.IsValid()
    requires arr2.IsValid()
    requires arr1.FreeToWrite(lower1, upper1)
    requires arr2.FreeToRead(lower2, upper2)
    modifies arr1
    ensures arr1.WriteLock == old(arr1.WriteLock)
    ensures arr1.ReadLocks == old(arr1.ReadLocks)
    ensures arr1.IsValid()
    ensures forall i :: lower1 <= i < upper1 ==> 
      arr1.Repr[i] == arr2.Repr[i - lower1 + lower2]
    ensures forall i :: (0 <= i < lower1 || |arr1.Repr| > i >= upper1) 
                    ==> arr1.Repr[i] == old(arr1.Repr[i])
  {
    reveal ArrayOfReals.FreeToReadStatic;
    reveal ArrayOfReals.FreeToWriteStatic;
    for i := lower1 to upper1
      invariant arr1.WriteLock == old(arr1.WriteLock)
      invariant arr1.ReadLocks == old(arr1.ReadLocks)
      invariant |arr1.Repr| == old(|arr1.Repr|)
      invariant forall j :: (0 <= j < lower1 || |arr1.Repr| > j >= upper1) 
                        ==> arr1.Repr[j] == old(arr1.Repr[j])
      invariant forall j :: lower1 <= j < i ==> 
        arr1.Repr[j] == arr2.Repr[j - lower1 + lower2]
    {
      arr1.Set(i, arr2.Get(i - lower1 + lower2));
    }
  }

  method Abs(arr1:ArrayOfReals) returns (arr2:ArrayOfReals) 
    requires arr1.IsValid()
    requires arr1.FreeToRead(0, arr1.length)
    ensures arr2.IsValid()
    ensures fresh(arr2)
    ensures arr2.length == arr1.length
    ensures forall i :: 0 <= i < arr1.length ==> 
      arr2.Repr[i] == if arr1.Repr[i] > 0.0
                      then arr1.Repr[i] else -arr1.Repr[i]
    ensures arr2.FreeToWrite(0, arr2.length)
  {
    arr2 := EditConst(arr1, x => if x > 0.0 then x else -x);
  }

  method Max(arr:ArrayOfReals) returns (max:real) 
    requires arr.IsValid()
    requires arr.FreeToRead(0, arr.length)
    requires arr.length != 0
    ensures forall i:: 0 <= i < arr.length ==> arr.Repr[i] <= max 
    ensures exists i:: 0 <= i < arr.length && arr.Repr[i] == max 
  {
    reveal ArrayOfReals.FreeToReadStatic;
    max := arr.Get(0);
    for i := 0 to arr.Length() 
      invariant forall i' :: 0 <= i' < i ==> arr.Repr[i'] <= max 
      invariant exists i' :: (0 <= i' < arr.length && arr.Repr[i'] == max)
    {
      if arr.Get(i) > max {
        max := arr.Get(i);
      }
    }
  }
}