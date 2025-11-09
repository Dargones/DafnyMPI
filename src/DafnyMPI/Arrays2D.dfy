include "Externs/MPIResource.dfy"
include "Arrays1D.dfy"

module Arrays2D {

  import Arrays1D
  import opened MPIResource
  import opened Std.Arithmetic.Mul
  import opened Std.Arithmetic.DivMod

  method Ones(dim1:nat, dim2:nat) 
    returns (arr:ArrayOfReals2D) 
    ensures arr.dim1 == dim1
    ensures arr.dim2 == dim2
    ensures arr.IsValid()
    ensures forall i,j :: 
      (0 <= i < dim1 && 0 <= j < dim2) ==> arr.Repr2D[i][j] == 1.0
    ensures fresh(arr)
    ensures arr.FreeToWrite(0, arr.length)
  {
    arr := new ArrayOfReals2D(dim1, dim2, 1.0);
  }

  method Zeros(dim1:nat, dim2:nat)
    returns (arr:ArrayOfReals2D) 
    ensures arr.dim1 == dim1
    ensures arr.dim2 == dim2
    ensures arr.IsValid()
    ensures forall i,j :: 
      (0 <= i < dim1 && 0 <= j < dim2) ==> arr.Repr2D[i][j] == 0.0
    ensures fresh(arr)
    ensures arr.FreeToWrite(0, arr.length)
  {
    arr := new ArrayOfReals2D(dim1, dim2, 0.0);
  }

  method GetRow(arr:ArrayOfReals2D, i:nat) returns (arr2:ArrayOfReals)
    requires i < arr.dim1 
    requires arr.IsValid()
    requires assert (i + 1) * arr.dim2 <= arr.length by {
              LemmaMulInequality(i+1, arr.dim1, arr.dim2);
            } 
             arr.FreeToRead(i * arr.dim2, (i + 1) * arr.dim2)
    ensures fresh(arr2)
    ensures arr2.IsValid()
    ensures arr2.FreeToWrite(0, arr2.length)
    ensures arr.Repr2D[i] == arr2.Repr
  {
    reveal ArrayOfReals2D.FreeToWriteStatic;
    reveal ArrayOfReals2D.FreeToReadStatic;
    arr2 := Arrays1D.Zeros(arr.Dim2());
    for j := 0 to arr.Dim2() 
      modifies arr2
      invariant arr2.IsValid()
      invariant arr2.FreeToWrite(0, arr2.length)
      invariant forall j' :: 0 <= j' < j ==> arr2.Repr[j'] == arr.Repr2D[i][j']
    {
      arr2.Set(j, arr.Get(i,j));
    }
    assert |arr2.Repr| == |arr.Repr2D[i]|;
    assert forall j' :: 0 <= j' < |arr.Repr2D[i]| ==> 
      arr2.Repr[j'] == arr.Repr2D[i][j'];
  }

  method SetRow(arr:ArrayOfReals2D, i:nat, val:ArrayOfReals)
    requires i < arr.dim1
    requires arr.IsValid()
    requires assert i + 1 <= arr.dim1; 
             assert (i+1) * arr.dim2 <= arr.dim1 * arr.dim2; 
             arr.FreeToWrite(i * arr.dim2, (i + 1) * arr.dim2)
    requires arr.dim2 == val.length
    requires val.IsValid()
    requires val.FreeToRead(0, val.length)
    modifies arr
    ensures arr.IsValid()
    ensures forall i' :: 
      (&& 0 <= i' < arr.dim1 
        && (i' != i)) 
      ==> arr.Repr2D[i'] == old(arr.Repr2D[i'])
    ensures arr.Repr2D[i] == val.Repr
    ensures arr.WriteLock == old(arr.WriteLock)
    ensures arr.ReadLocks == old(arr.ReadLocks)
  {
    reveal ArrayOfReals2D.FreeToWriteStatic;
    reveal ArrayOfReals2D.FreeToReadStatic;
    assert i + 1 <= arr.dim1; 
    assert (i+1) * arr.dim2 <= arr.dim1 * arr.dim2;
    for j := 0 to val.Length() 
      modifies arr
      invariant arr.IsValid()
      invariant forall i' :: 
        (&& 0 <= i' < arr.dim1 && (i' != i)) 
        ==> arr.Repr2D[i'] == old(arr.Repr2D[i'])
      invariant forall j' :: 0 <= j' < j ==> arr.Repr2D[i][j'] == val.Repr[j']
      invariant arr.WriteLock == old(arr.WriteLock)
      invariant arr.ReadLocks == old(arr.ReadLocks)
      invariant arr.FreeToWrite(i * arr.dim2, (i + 1) * arr.dim2)
    {
      arr.Set(i, j, val.Get(j));
    }
  }

  method Copy(arr:ArrayOfReals2D) returns (arr2:ArrayOfReals2D) 
    requires arr.IsValid()
    requires arr.FreeToRead(0, arr.length)
    ensures arr2.IsValid()
    ensures arr2.Repr2D == arr.Repr2D
    ensures arr2.FreeToWrite(0, arr2.length)
    ensures fresh(arr2)
  {
    arr2 := EditConst(arr, x => x);
    assert forall i :: 0 <= i < |arr.Repr2D| ==> arr.Repr2D[i] == arr2.Repr2D[i];
  }

  method FromSeq(Repr2D:seq<seq<real>>, dim1:nat, dim2:nat) 
    returns (arr:ArrayOfReals2D) 
    requires ArrayOfReals2D.IsValidRepr(Repr2D, dim1, dim2)
    ensures arr.IsValid()
    ensures arr.Repr2D == Repr2D
    ensures arr.FreeToWrite(0, arr.length)
    ensures arr.dim1 == dim1
    ensures arr.dim2 == dim2
    ensures fresh(arr)
  {
    reveal ArrayOfReals2D.FreeToWriteStatic;
    reveal ArrayOfReals2D.FreeToReadStatic;
    arr := new ArrayOfReals2D(dim1, dim2, 0.0);
    for i := 0 to dim1
      modifies arr
      invariant arr.dim1 == dim1
      invariant arr.dim2 == dim2
      invariant arr.IsValid()
      invariant arr.FreeToWrite(0, arr.length)
      invariant forall i' :: (0 <= i' < i) 
                      ==> arr.Repr2D[i'] == Repr2D[i']
    {
      for j := 0 to dim2
        modifies arr
        invariant arr.dim1 == dim1
        invariant arr.dim2 == dim2
        invariant arr.IsValid()
        invariant arr.FreeToWrite(0, arr.length)
        invariant forall i', j' :: (0 <= i' < i && 0 <= j' < arr.Dim2()) 
                      ==> arr.Repr2D[i'][j'] == Repr2D[i'][j']
        invariant forall j' :: (0 <= j' < j) 
                      ==> arr.Repr2D[i][j'] == Repr2D[i][j']
      {
        calc {
          i * arr.dim2 + j;
          < i * arr.dim2 + arr.dim2;
          == (i + 1) * arr.dim2;
          <= {LemmaMulInequality(i + 1, arr.dim1, arr.dim2);}
             arr.dim1 * arr.dim2;
          == arr.length;
        }
        assert arr.ReadLocks[i * arr.dim2 + j] == 0;
        assert !arr.WriteLock[i * arr.dim2 + j];
        arr.Set(i, j, Repr2D[i][j]);    
      }   
    }
  }

  /* Helper Function for SetRange */
  ghost predicate {:opaque} AllInRange
    (arr:ArrayOfReals2D, 
      i1:nat, i2:nat, j1:nat, j2:nat, val:real)
    reads arr
    requires arr.IsValid()
    requires i1 <= i2 <= arr.dim1
    requires j1 <= j2 <= arr.dim2 
  {
    forall i, j :: 
      (&& (i1 <= i < i2)
        && (j1 <= j < j2)) ==> 
        arr.Repr2D[i][j] == val
  }

  /* Helper Function for SetRange */
  ghost predicate {:opaque} AllOutRange
    (Repr2D:seq<seq<real>>, oldRepr2D:seq<seq<real>>, dim1:nat, dim2:nat, i1:nat, i2:nat, j1:nat, j2:nat) 
    requires ArrayOfReals2D.IsValidRepr(Repr2D, dim1, dim2)
    requires ArrayOfReals2D.IsValidRepr(oldRepr2D, dim1, dim2)
  {
    forall i, j :: 
      (&& (0 <= i < dim1)
        && (0 <= j < dim2)
        && (|| 0    <= i <  i1 
            || dim1 >  i >= i2
            || 0    <= j <  j1 
            || dim2 >  j >= j2)) 
      ==> Repr2D[i][j] == oldRepr2D[i][j]
  }

  lemma LemmaEqualRepr
    (Repr:seq<real>, aRepr2D:seq<seq<real>>, bRepr2D:seq<seq<real>>, dim1:nat, dim2:nat) 
    requires ArrayOfReals2D.IsValidReprFull(aRepr2D, Repr, dim1, dim2)
    requires ArrayOfReals2D.IsValidReprFull(bRepr2D, Repr, dim1, dim2)
    ensures aRepr2D == bRepr2D
  {
    assert forall i :: 0 <= i < |aRepr2D| 
            ==> aRepr2D[i] == bRepr2D[i];
  }

  lemma LemmaNoWriteLockBlockTrivial
    (arr:ArrayOfReals2D, ilow:nat, ihigh:nat, jlow:nat, jhigh:nat) 
    requires ilow <= ihigh <= arr.dim1
    requires jlow <= jhigh <= arr.dim2
    requires arr.IsValid()
    requires arr.FreeToWrite(0, arr.length) 
    ensures NoWriteLockBlock(arr, ilow, ihigh, jlow, jhigh)
  {
    reveal ArrayOfReals2D.FreeToWriteStatic;
    reveal ArrayOfReals2D.FreeToReadStatic;
    reveal NoWriteLockBlock;
  }

  lemma LemmaNoReadLockBlockTrivial
    (arr:ArrayOfReals2D, ilow:nat, ihigh:nat, jlow:nat, jhigh:nat) 
    requires ilow <= ihigh <= arr.dim1
    requires jlow <= jhigh <= arr.dim2
    requires arr.IsValid()
    requires arr.FreeToWrite(0, arr.length) 
    ensures NoReadLockBlock(arr, ilow, ihigh, jlow, jhigh)
  {
    reveal ArrayOfReals2D.FreeToWriteStatic;
    reveal ArrayOfReals2D.FreeToReadStatic;
    reveal NoReadLockBlock;
  }

  ghost predicate {:opaque} NoWriteLockBlock
    (arr:ArrayOfReals2D, ilow:nat, ihigh:nat, jlow:nat, jhigh:nat) 
    requires ilow <= ihigh <= arr.dim1
    requires jlow <= jhigh <= arr.dim2
    requires arr.IsValid()
    reads arr
  {
    /*forall i, j :: ilow <= i < ihigh && jlow <= j < jhigh
              ==> calc {i * arr.dim2 + j;
                        < i * arr.dim2 + arr.dim2;
                        == (i + 1) * arr.dim2; 
                        <= {LemmaMulInequality(i + 1, arr.dim1, arr.dim2);}
                           arr.dim1 * arr.dim2; 
                        == arr.length;} 
                 !arr.WriteLock[i * arr.dim2 + j]*/
    calc {(ihigh - 1) * arr.dim2 + jhigh;
       <= (ihigh - 1) * arr.dim2 + arr.dim2;
       == ihigh * arr.dim2; 
       <= {LemmaMulInequality(ihigh, arr.dim1, arr.dim2);}
       arr.dim1 * arr.dim2; 
       == arr.length;} 
    forall i :: ilow * arr.dim2 + jlow <= i < (ihigh - 1) * arr.dim2 + jhigh
      ==> !arr.WriteLock[i] // less precise but should work for most cases
  }

  ghost predicate {:opaque} NoReadLockBlock
    (arr:ArrayOfReals2D, ilow:nat, ihigh:nat, jlow:nat, jhigh:nat) 
    requires ilow <= ihigh <= arr.dim1
    requires jlow <= jhigh <= arr.dim2
    requires arr.IsValid()
    reads arr
  {
    /*forall i, j :: ilow <= i < ihigh && jlow <= j < jhigh
              ==> calc {i * arr.dim2 + j;
                        < i * arr.dim2 + arr.dim2;
                        == (i + 1) * arr.dim2; 
                        <= {LemmaMulInequality(i + 1, arr.dim1, arr.dim2);}
                           arr.dim1 * arr.dim2; 
                        == arr.length;} 
                 arr.ReadLocks[i * arr.dim2 + j] == 0*/
    calc {(ihigh - 1) * arr.dim2 + jhigh;
       <= (ihigh - 1) * arr.dim2 + arr.dim2;
       == ihigh * arr.dim2; 
       <= {LemmaMulInequality(ihigh, arr.dim1, arr.dim2);}
       arr.dim1 * arr.dim2; 
       == arr.length;} 
    forall i :: ilow * arr.dim2 + jlow <= i < (ihigh - 1) * arr.dim2 + jhigh
      ==> arr.ReadLocks[i] == 0 // less precise but should work for most cases
  }

  method SetRange(arr:ArrayOfReals2D, i1:nat, i2:nat, j1:nat, j2:nat, val:real)
    requires arr.IsValid()
    requires i1 <= i2 <= arr.dim1
    requires j1 <= j2 <= arr.dim2
    requires NoWriteLockBlock(arr, i1, i2, j1, j2)
    requires NoReadLockBlock(arr, i1, i2, j1, j2)
    modifies arr
    ensures arr.IsValid()
    ensures AllInRange(arr, i1, i2, j1, j2, val)
    ensures AllOutRange(arr.Repr2D, old(arr.Repr2D), arr.dim1, arr.dim2, i1, i2, j1, j2)
    ensures arr.ReadLocks == old(arr.ReadLocks)
    ensures arr.WriteLock == old(arr.WriteLock)
  {
    reveal AllOutRange;
    reveal AllInRange;
    ghost var oldRepr := arr.Repr2D;
    for k := i1 to i2 
      invariant arr.IsValid()
      invariant arr.ReadLocks == old(arr.ReadLocks)
      invariant arr.WriteLock == old(arr.WriteLock)
      invariant AllOutRange(arr.Repr2D, oldRepr, arr.dim1, arr.dim2, i1, i2, j1, j2)
      invariant AllInRange(arr, i1, k, j1, j2, val)
    {
      for l := j1 to j2 
        invariant arr.IsValid()
        invariant arr.ReadLocks == old(arr.ReadLocks)
        invariant arr.WriteLock == old(arr.WriteLock)
        invariant AllOutRange(arr.Repr2D, oldRepr, arr.dim1, arr.dim2, i1, i2, j1, j2)
        invariant AllInRange(arr, i1, k, j1, j2, val)
        invariant AllInRange(arr, i1, k + 1, j1, l, val)
      {
        assert arr.IsValidStronger();
        reveal NoWriteLockBlock;
        reveal NoReadLockBlock;
        arr.Set(k, l, val);
      }
    }
  }

  method Slice
    (arr1:ArrayOfReals2D, ilow:nat, ihigh:nat, jlow:nat, jhigh:nat)
    returns (arr2:ArrayOfReals2D)
    requires ilow < ihigh <= arr1.dim1
    requires jlow < jhigh <= arr1.dim2
    requires arr1.IsValid()
    requires NoWriteLockBlock(arr1, ilow, ihigh, jlow, jhigh)
    ensures arr2.IsValid()
    ensures fresh(arr2)
    ensures arr2.dim1 == ihigh - ilow
    ensures arr2.dim2 == jhigh - jlow
    ensures forall i, j :: (0 <= i < arr2.dim1 && 0 <= j < arr2.dim2)
                        ==> arr2.Repr2D[i][j] == arr1.Repr2D[i + ilow][j + jlow]
    ensures arr2.FreeToWrite(0, arr2.length)
  {
    reveal ArrayOfReals2D.FreeToWriteStatic;
    reveal ArrayOfReals2D.FreeToReadStatic;
    arr2 := new ArrayOfReals2D(ihigh - ilow, jhigh - jlow, 0.0);
    for i := 0 to ihigh - ilow
      invariant arr2.IsValid()
      invariant arr2.dim1 == ihigh - ilow
      invariant arr2.dim2 == jhigh - jlow 
      invariant arr2.FreeToWrite(0, arr2.length)
      invariant arr1 != arr2
      modifies arr2
      invariant forall i' :: (0 <= i' < i) ==> |arr2.Repr2D[i']| == jhigh - jlow
      invariant forall i', j' :: (0 <= i' < i && 0 <= j' < jhigh - jlow) 
                      ==> arr2.Repr2D[i'][j'] == arr1.Repr2D[i' + ilow][j' + jlow] 
    {
      for j := 0 to jhigh - jlow 
        invariant arr2.IsValid()
        invariant arr2.dim1 == ihigh - ilow
        invariant arr2.dim2 == jhigh - jlow 
        invariant arr2.FreeToWrite(0, arr2.length)
        invariant arr1 != arr2
        modifies arr2
        invariant forall i', j' :: (0 <= i' < i && 0 <= j' < jhigh - jlow) 
                      ==> arr2.Repr2D[i'][j'] == arr1.Repr2D[i' + ilow][j' + jlow] 
        invariant forall j' :: (0 <= j' < j) 
                      ==> arr2.Repr2D[i][j'] == arr1.Repr2D[i + ilow][j' + jlow]
      {
        calc {
          (i + ilow) * arr1.dim2 + (j + jlow);
          < (i + ilow) * arr1.dim2 + arr1.dim2;
          == ((i + ilow) + 1) * arr1.dim2;
          <= {LemmaMulInequality((i + ilow) + 1, arr1.dim1, arr1.dim2);}
             arr1.dim1 * arr1.dim2;
          == arr1.length;
        }
        calc {
          i * arr2.dim2 + j;
          < i * arr2.dim2 + arr2.dim2;
          == (i + 1) * arr2.dim2;
          <= {LemmaMulInequality(i + 1, arr2.dim1, arr2.dim2);}
             arr2.dim1 * arr2.dim2;
          == arr2.length;
        }
        reveal NoWriteLockBlock;
        assert ilow * arr1.dim2 + jlow 
            <= (i + ilow) * arr1.dim2 + (j + jlow) 
            < (ihigh - 1) * arr1.dim2 + jhigh;
        arr2.Set(i, j, arr1.Get(i + ilow, j + jlow));   
      }   
    }
  }

  method EditConst
    (arr1:ArrayOfReals2D, F: real -> real)
    returns (arr2:ArrayOfReals2D)
    requires arr1.IsValid()
    requires arr1.FreeToRead(0, arr1.length)
    ensures arr2.IsValid()
    ensures fresh(arr2)
    ensures arr2.dim1 == arr1.dim1
    ensures arr2.dim2 == arr1.dim2
    ensures forall i, j :: (0 <= i < arr2.dim1 && 0 <= j < arr2.dim2)
                        ==> arr2.Repr2D[i][j] == F(arr1.Repr2D[i][j])
    ensures arr2.FreeToWrite(0, arr2.length)
  {
    reveal ArrayOfReals2D.FreeToWriteStatic;
    reveal ArrayOfReals2D.FreeToReadStatic;
    arr2 := new ArrayOfReals2D(arr1.Dim1(), arr1.Dim2(), 0.0);
    for i := 0 to arr1.Dim1()
      modifies arr2
      invariant arr1 != arr2
      invariant arr2.IsValid()
      invariant arr2.dim1 == arr1.dim1
      invariant arr2.dim2 == arr1.dim2
      invariant arr2.FreeToWrite(0, arr2.length)
      invariant arr1.FreeToRead(0, arr1.length)
      invariant forall i', j' :: (0 <= i' < i && 0 <= j' < arr1.Dim2()) 
                      ==> arr2.Repr2D[i'][j'] == F(arr1.Repr2D[i'][j'])
    {
      for j := 0 to arr1.Dim2()
        modifies arr2
        invariant arr1 != arr2
        invariant arr2.IsValid()
        invariant arr2.dim1 == arr1.dim1
        invariant arr2.dim2 == arr1.dim2
        invariant arr2.FreeToWrite(0, arr2.length)
        invariant arr1.FreeToRead(0, arr1.length)
        invariant forall i', j' :: (0 <= i' < i && 0 <= j' < arr1.Dim2()) 
                      ==> arr2.Repr2D[i'][j'] == F(arr1.Repr2D[i'][j'])
        invariant forall j' :: (0 <= j' < j) 
                      ==> arr2.Repr2D[i][j'] == F(arr1.Repr2D[i][j'])
      {
        assert arr2.IsValidStronger();
        assert arr2.ReadLocks[i * arr2.dim2 + j] == 0;
        assert !arr2.WriteLock[i * arr2.dim2 + j];
        assert !arr1.WriteLock[i * arr1.dim2 + j];
        arr2.Set(i, j,F(arr1.Get(i, j)));    
      }   
    }
  }

  method AddConst(arr1:ArrayOfReals2D, c:real)
    returns (arr2:ArrayOfReals2D)
    requires arr1.IsValid()
    requires arr1.FreeToRead(0, arr1.length)
    ensures arr2.IsValid()
    ensures fresh(arr2)
    ensures arr2.dim1 == arr1.dim1
    ensures arr2.dim2 == arr1.dim2
    ensures forall i, j :: (0 <= i < arr2.dim1 && 0 <= j < arr2.dim2)
                        ==> arr2.Repr2D[i][j] == arr1.Repr2D[i][j] + c
    ensures arr2.FreeToWrite(0, arr2.length)
  {
    arr2 := EditConst(arr1, r => r + c);
  }

  method MulConst(arr1:ArrayOfReals2D, c:real)
    returns (arr2:ArrayOfReals2D)
    requires arr1.IsValid()
    requires arr1.FreeToRead(0, arr1.length)
    ensures arr2.IsValid()
    ensures fresh(arr2)
    ensures arr2.dim1 == arr1.dim1
    ensures arr2.dim2 == arr1.dim2
    ensures forall i, j :: (0 <= i < arr2.dim1 && 0 <= j < arr2.dim2)
                        ==> arr2.Repr2D[i][j] == arr1.Repr2D[i][j] * c
    ensures arr2.FreeToWrite(0, arr2.length)
  {
    arr2 := EditConst(arr1, r => r * c);
  }

  method MergeArrays
    (arr1:ArrayOfReals2D, arr2:ArrayOfReals2D, F: (real, real) -> real)
    returns (arr3:ArrayOfReals2D)
    requires arr1.IsValid()
    requires arr2.IsValid()
    requires arr2.dim1 == arr1.dim1
    requires arr2.dim2 == arr1.dim2
    requires arr1.FreeToRead(0, arr1.length)
    requires arr2.FreeToRead(0, arr2.length)
    ensures fresh(arr3)
    ensures arr3.IsValid()
    ensures arr3.dim1 == arr1.dim1
    ensures arr3.dim2 == arr1.dim2
    ensures forall i, j :: (0 <= i < arr3.dim1 && 0 <= j < arr3.dim2)
                ==> arr3.Repr2D[i][j] == F(arr1.Repr2D[i][j], arr2.Repr2D[i][j])
    ensures arr3.FreeToWrite(0, arr3.length)
  {
    reveal ArrayOfReals2D.FreeToWriteStatic;
    reveal ArrayOfReals2D.FreeToReadStatic;
    arr3 := new ArrayOfReals2D(arr1.Dim1(), arr1.Dim2(), 0.0);
    for i := 0 to arr1.Dim1()
      modifies arr3
      invariant arr1 != arr3
      invariant arr2 != arr3
      invariant arr3.IsValid()
      invariant arr3.dim1 == arr1.dim1
      invariant arr3.dim2 == arr1.dim2
      invariant arr3.FreeToWrite(0, arr3.length)
      invariant arr1.FreeToRead(0, arr1.length)
      invariant arr2.FreeToRead(0, arr2.length)
      invariant forall i', j' :: (0 <= i' < i && 0 <= j' < arr1.Dim2()) 
                      ==> arr3.Repr2D[i'][j'] == F(arr1.Repr2D[i'][j'], 
                                                   arr2.Repr2D[i'][j'])
    {
      for j := 0 to arr1.Dim2()
        modifies arr3
        invariant arr1 != arr3
        invariant arr2 != arr3
        invariant arr3.IsValid()
        invariant arr3.dim1 == arr1.dim1
        invariant arr3.dim2 == arr1.dim2
        invariant arr3.FreeToWrite(0, arr3.length)
        invariant arr1.FreeToRead(0, arr1.length)
        invariant arr2.FreeToRead(0, arr2.length)
        invariant forall i', j' :: (0 <= i' < i && 0 <= j' < arr1.Dim2()) 
                      ==> arr3.Repr2D[i'][j'] == F(arr1.Repr2D[i'][j'],
                                                   arr2.Repr2D[i'][j'])
        invariant forall j' :: (0 <= j' < j) 
                      ==> arr3.Repr2D[i][j'] == F(arr1.Repr2D[i][j'],
                                                   arr2.Repr2D[i][j'])
      {
        assert arr3.ReadLocks[i * arr3.dim2 + j] == 0;
        assert !arr3.WriteLock[i * arr3.dim2 + j];
        assert !arr1.WriteLock[i * arr2.dim2 + j];
        assert !arr2.WriteLock[i * arr2.dim2 + j];
        arr3.Set(i, j,F(arr1.Get(i, j), arr2.Get(i, j)));    
      }   
    }
  }

  method AddArrays
    (arr1:ArrayOfReals2D, arr2:ArrayOfReals2D)
    returns (arr3:ArrayOfReals2D)
    requires arr1.IsValid()
    requires arr2.IsValid()
    requires arr2.dim1 == arr1.dim1
    requires arr2.dim2 == arr1.dim2
    requires arr1.FreeToRead(0, arr1.length)
    requires arr2.FreeToRead(0, arr2.length)
    ensures fresh(arr3)
    ensures arr3.IsValid()
    ensures arr3.dim1 == arr1.dim1
    ensures arr3.dim2 == arr1.dim2
    ensures forall i, j :: (0 <= i < arr3.dim1 && 0 <= j < arr3.dim2)
                ==> arr3.Repr2D[i][j] == arr1.Repr2D[i][j] + arr2.Repr2D[i][j]
    ensures arr3.FreeToWrite(0, arr3.length)
  {
    arr3 := MergeArrays(arr1, arr2, (r1, r2) => r1 + r2);
  }

  method MulArrays
    (arr1:ArrayOfReals2D, arr2:ArrayOfReals2D)
    returns (arr3:ArrayOfReals2D)
    requires arr1.IsValid()
    requires arr2.IsValid()
    requires arr2.dim1 == arr1.dim1
    requires arr2.dim2 == arr1.dim2
    requires arr1.FreeToRead(0, arr1.length)
    requires arr2.FreeToRead(0, arr2.length)
    ensures fresh(arr3)
    ensures arr3.IsValid()
    ensures arr3.dim1 == arr1.dim1
    ensures arr3.dim2 == arr1.dim2
    ensures forall i, j :: (0 <= i < arr3.dim1 && 0 <= j < arr3.dim2)
                ==> arr3.Repr2D[i][j] == arr1.Repr2D[i][j] * arr2.Repr2D[i][j]
    ensures arr3.FreeToWrite(0, arr3.length)
  {
    arr3 := MergeArrays(arr1, arr2, (r1, r2) => r1 * r2);
  }

  function {:opaque} RollHelper(i:nat, dim:nat, dist:nat):nat
    requires dist < dim
    requires i < dim
    ensures RollHelper(i, dim, dist) < dim
  {
    // Could have use % but that introduces non-linear arithmetic
    if i >= dist then i - dist else i + dim - dist
  }

  method RollInternal
    (arr1:ArrayOfReals2D, dist1:nat, dist2:nat) 
    returns (arr2:ArrayOfReals2D)
    requires arr1.IsValid()
    requires arr1.FreeToRead(0, arr1.length)
    requires dist1 < arr1.dim1
    requires dist2 < arr1.dim2
    ensures arr2.IsValid()
    ensures fresh(arr2)
    ensures arr2.dim1 == arr1.dim1
    ensures arr2.dim2 == arr1.dim2
    ensures forall i, j :: (0 <= i < arr1.dim1 && 0 <= j < arr1.dim2) ==> 
      arr2.Repr2D[i][j] == arr1.Repr2D[RollHelper(i, arr1.dim1, dist1)]
                                      [RollHelper(j, arr1.dim2, dist2)]
    ensures arr2.FreeToWrite(0, arr2.length)
  {
    reveal ArrayOfReals2D.FreeToWriteStatic;
    reveal ArrayOfReals2D.FreeToReadStatic;
    arr2 := new ArrayOfReals2D(arr1.Dim1(), arr1.Dim2(), 0.0);
    for i := 0 to arr1.Dim1()
      modifies arr2
      invariant arr1 != arr2
      invariant arr2.IsValid()
      invariant arr2.dim1 == arr1.dim1
      invariant arr2.dim2 == arr1.dim2
      invariant arr2.FreeToWrite(0, arr2.length)
      invariant arr1.FreeToRead(0, arr1.length)
      invariant forall i', j' :: (0 <= i' < i && 0 <= j' < arr1.dim2) ==> 
        arr2.Repr2D[i'][j'] == arr1.Repr2D[RollHelper(i', arr1.dim1, dist1)]
                                          [RollHelper(j', arr1.dim2, dist2)]
    {
      for j := 0 to arr1.Dim2()
        modifies arr2
        invariant arr1 != arr2
        invariant arr2.IsValid()
        invariant arr2.dim1 == arr1.dim1
        invariant arr2.dim2 == arr1.dim2
        invariant arr2.FreeToWrite(0, arr2.length)
        invariant arr1.FreeToRead(0, arr1.length)
        invariant forall i', j' :: (0 <= i' < i && 0 <= j' < arr1.dim2) ==> 
          arr2.Repr2D[i'][j'] == arr1.Repr2D[RollHelper(i', arr1.dim1, dist1)]
                                            [RollHelper(j', arr1.dim2, dist2)]
        invariant forall j' :: 0 <= j' < j ==> 
          arr2.Repr2D[i][j'] == arr1.Repr2D[RollHelper(i, arr1.dim1, dist1)]
                                           [RollHelper(j', arr1.dim2, dist2)]
      {
        calc {
          RollHelper(i, arr1.Dim1(), dist1) * arr1.dim2 + RollHelper(j, arr1.Dim2(), dist2);
          < 
          RollHelper(i, arr1.Dim1(), dist1) * arr1.dim2 + arr1.dim2;
          ==
          (RollHelper(i, arr1.Dim1(), dist1) + 1) * arr1.dim2;
          <= {LemmaMulInequality(RollHelper(i, arr1.Dim1(), dist1) + 1, arr1.dim1, arr1.dim2);}
          arr1.dim1 * arr1.dim2;
          == arr1.length;
        }
        calc {
          i * arr2.dim2 + j;
          < 
          i * arr2.dim2 + arr2.dim2;
          ==
          (i + 1) * arr2.dim2;
          <= {LemmaMulInequality(i + 1, arr2.dim1, arr2.dim2);}
          arr2.dim1 * arr2.dim2;
          == arr2.length;
        }
        arr2.Set(i, j, arr1.Get(RollHelper(i, arr1.Dim1(), dist1), 
                                RollHelper(j, arr1.Dim2(), dist2)));
      }     
    }
  }

  method Roll
    (arr1:ArrayOfReals2D, dist1:int, dist2:int) 
    returns (arr2:ArrayOfReals2D)
    requires arr1.IsValid()
    requires arr1.FreeToRead(0, arr1.length)
    requires -(arr1.dim1 as int) < dist1 < arr1.dim1
    requires -(arr1.dim2 as int) < dist2 < arr1.dim2
    ensures arr2.IsValid()
    ensures fresh(arr2)
    ensures arr2.dim1 == arr1.dim1
    ensures arr2.dim2 == arr1.dim2
    ensures 
      var dist1real := if dist1 >= 0 then dist1 else arr1.dim1 + dist1;
      var dist2real := if dist2 >= 0 then dist2 else arr1.dim2 + dist2;
      forall i, j :: (0 <= i < arr1.dim1 && 0 <= j < arr1.dim2) ==> 
      arr2.Repr2D[i][j] == arr1.Repr2D[RollHelper(i, arr1.dim1, dist1real)]
                                      [RollHelper(j, arr1.dim2, dist2real)]
    ensures arr2.FreeToWrite(0, arr2.length)
  {
    reveal RollHelper;
    var dist1real := if dist1 >= 0 then dist1 else arr1.Dim1() + dist1;
    var dist2real := if dist2 >= 0 then dist2 else arr1.Dim2() + dist2;
    arr2 := RollInternal(arr1, dist1real, dist2real);
  }

  method Abs(arr1:ArrayOfReals2D) returns (arr2:ArrayOfReals2D) 
    requires arr1.IsValid()
    requires arr1.FreeToRead(0, arr1.length)
    ensures arr2.IsValid()
    ensures fresh(arr2)
    ensures arr2.dim1 == arr1.dim1
    ensures arr2.dim2 == arr1.dim2
    ensures forall i, j :: (0 <= i < arr1.dim1 && 0 <= j < arr1.dim2) ==> 
      arr2.Repr2D[i][j] == if arr1.Repr2D[i][j] > 0.0
                           then arr1.Repr2D[i][j] else -arr1.Repr2D[i][j]
    ensures arr2.FreeToWrite(0, arr2.length)
  {
    arr2 := EditConst(arr1, x => if x > 0.0 then x else -x);
  }

  method Max(arr:ArrayOfReals2D) returns (max:real) 
    requires arr.IsValid()
    requires arr.FreeToRead(0, arr.length)
    requires arr.dim1 != 0 && arr.dim2 != 0
    ensures forall i, j :: (0 <= i < arr.dim1 && 0 <= j < arr.dim2) ==> 
      arr.Repr2D[i][j] <= max 
    ensures exists i, j :: 
      (0 <= i < arr.dim1 && 0 <= j < arr.dim2 && arr.Repr2D[i][j] == max)
  {
    reveal ArrayOfReals2D.FreeToReadStatic;
    max := arr.Get(0, 0);
    for i := 0 to arr.Dim1() 
      invariant forall i', j :: (0 <= i' < i && 0 <= j < arr.dim2) ==> 
        arr.Repr2D[i'][j] <= max 
      invariant exists i', j :: 
        (0 <= i' < arr.dim1 && 0 <= j < arr.dim2 && arr.Repr2D[i'][j] == max)
    {
      for j := 0 to arr.Dim2() 
        invariant forall j' :: 0 <= j' < j ==> 
          arr.Repr2D[i][j'] <= max 
        invariant forall i', j' :: (0 <= i' < i && 0 <= j' < arr.dim2) ==> 
          arr.Repr2D[i'][j'] <= max 
        invariant exists i', j' :: 
          (0 <= i' < arr.dim1 && 0 <= j' < arr.dim2 
          && arr.Repr2D[i'][j'] == max)
      {
        calc {
            i * arr.dim2 + j;
          < i * arr.dim2 + arr.dim2;
          == {LemmaMulIsDistributiveAddOtherWay(arr.dim2, i, 1);}
            (i + 1) * arr.dim2;
          <= {LemmaMulInequality(i + 1, arr.dim1, arr.dim2);}
            arr.dim1 * arr.dim2;
          == arr.length;
        }
        if arr.Get(i, j) > max {
          max := arr.Get(i, j);
        }
      }
    }
  }

  /* Helper Function for SetSlice */
  ghost predicate {:opaque} AllInSlice
    (arr1:ArrayOfReals2D, arr2:ArrayOfReals2D, 
      i11:nat, i12:nat, j11:nat, j12:nat,
      i21:nat, i22:nat, j21:nat, j22:nat)
    reads arr1, arr2
    requires arr1.IsValid()
    requires arr2.IsValid()
    requires i11 <= i12 <= arr1.dim1
    requires j11 <= j12 <= arr1.dim2 
    requires i21 <= i22 <= arr2.dim1
    requires j21 <= j22 <= arr2.dim2 
    requires i12 - i11 == i22 - i21
    requires j12 - j11 == j22 - j21
  {
    forall i, j :: 
      (&& (i11 <= i < i12)
        && (j11 <= j < j12)) ==> 
        arr1.Repr2D[i][j] == arr2.Repr2D[i - i11 + i21][j - j11 + j21]
  }

  ghost predicate {:opaque} EqualWithPadding
    (u:ArrayOfReals2D, uSpec:seq<seq<real>>, dim1:nat, dim2:nat, 
     padding:nat, sx:nat, sy:nat) 
    requires u.IsValid()
    reads u
    requires dim1 >= u.dim1 + sx
    requires dim2 >= u.dim2 + sy
    requires |uSpec| == dim1
    requires forall i :: 0 <= i < |uSpec| ==> |uSpec[i]| == dim2
  {
    forall i, j :: (padding <= i < u.dim1 - padding 
                 && padding <= j < u.dim2 - padding)
      ==> u.Repr2D[i][j] == uSpec[sx + i][sy + j]
  }

  ghost predicate {:opaque} EqualSlice
    (u:ArrayOfReals2D, uSpec:seq<seq<real>>, dim1:nat, 
     sliceFrom:nat, sliceTo:nat, sx:nat) 
    requires u.IsValid()
    reads u
    requires dim1 >= u.dim1 + sx
    requires u.dim1 >= sliceTo
    requires |uSpec| == dim1
    requires forall i :: 0 <= i < |uSpec| ==> |uSpec[i]| == u.dim2
  {
    forall i, j :: (sliceFrom <= i < sliceTo
                 && 0 <= j < u.dim2)
      ==> u.Repr2D[i][j] == uSpec[sx + i][j]
  }

  lemma LemmaEqualWithPaddingSelf
    (u:ArrayOfReals2D, padding:nat) 
    requires u.IsValid()
    ensures EqualWithPadding(u, u.Repr2D, u.dim1, u.dim2, padding, 0, 0)
  {
    reveal EqualWithPadding;
  }


  lemma LemmaEqualWithPaddingInc
    (u:ArrayOfReals2D, uSpec:seq<seq<real>>, dim1:nat, dim2:nat, 
     paddingOld:nat, paddingNew:nat, 
     sx:nat, sy:nat) 
    requires u.IsValid()
    requires dim1 >= u.dim1 + sx
    requires dim2 >= u.dim2 + sy
    requires |uSpec| == dim1
    requires forall i :: 0 <= i < |uSpec| ==> |uSpec[i]| == dim2
    requires paddingOld < paddingNew
    requires EqualWithPadding(u, uSpec, dim1, dim2, paddingOld, sx, sy)
    ensures EqualWithPadding(u, uSpec, dim1, dim2, paddingNew, sx, sy)
  {
    reveal EqualWithPadding;
  }

  lemma {:isolate_assertions} LemmaEqualWithPaddingFlatten
    (u:ArrayOfReals2D, uSpec:seq<seq<real>>, 
     dim1:nat, shift:nat, from:nat, len:nat, padding:nat)
    requires u.IsValid()
    requires |uSpec| == dim1
    requires forall i :: 0 <= i < |uSpec| ==> |uSpec[i]| == u.dim2
    requires dim1 >= shift + u.dim1
    requires u.dim1 >= from + len
    requires len > 0
    requires u.dim2 > 0
    requires from >= padding
    requires from + len <= u.dim1 - padding
    ensures from * u.dim2 + len * u.dim2 <= u.dim1 * u.dim2
    ensures shift * u.dim2 + from * u.dim2 + len * u.dim2 <= dim1 * u.dim2
    requires EqualSlice(u, uSpec, dim1, padding, u.dim1 - padding, shift)
    ensures                         (u.Repr[from * u.dim2..
                                            from * u.dim2 + len * u.dim2] == 
      u.Flatten(uSpec, u.dim2)[shift * u.dim2 + from * u.dim2..
                               shift * u.dim2 + from * u.dim2 + len * u.dim2])
  {
    assert shift * u.dim2 + from * u.dim2 < 
           shift * u.dim2 + from * u.dim2 + len * u.dim2 <= dim1 * u.dim2 by {
      assert len * u.dim2 > 0;
      assert shift * u.dim2 + from * u.dim2 < 
             shift * u.dim2 + from * u.dim2 + len * u.dim2;
      LemmaMulIsDistributiveAdd(u.dim2, shift, from);
      LemmaMulIsDistributiveAdd(u.dim2, shift + from, len);
      LemmaMulInequality(shift + from + len, dim1, u.dim2);
    }
    for i := 0 to len
      invariant forall j :: from * u.dim2 <= j < from * u.dim2 + i * u.dim2 
                  ==> && (j < u.dim1 * u.dim2)
                      && (shift * u.dim2 + j < dim1 * u.dim2)
                      && (u.Repr[j] == 
                          u.Flatten(uSpec, u.dim2)[shift * u.dim2 + j])
    {
      for j := 0 to u.dim2  
        invariant forall k :: from * u.dim2 <= k 
                            < from * u.dim2 + i * u.dim2 + j
                    ==> && (k < u.dim1 * u.dim2)
                        && (shift * u.dim2 + k < dim1 * u.dim2)
                        && (u.Repr[k] == 
                            u.Flatten(uSpec, u.dim2)[shift * u.dim2 + k])
      {
        calc {
            from * u.dim2 + i * u.dim2 + j;
          < from * u.dim2 + (len - 1) * u.dim2 + u.dim2;
          == {LemmaMulIsDistributiveAdd(u.dim2, from, len - 1);
              LemmaMulIsDistributiveAdd(u.dim2, from + len - 1, 1);}
            (from + len) * u.dim2;
          <= {LemmaMulInequality(from + len, u.dim1, u.dim2);}
             u.dim1 * u.dim2;
        } 
        calc {
          shift * u.dim2 + from * u.dim2 + i * u.dim2 + j;
          < shift * u.dim2 + u.dim1 * u.dim2;
          == {LemmaMulIsDistributiveAdd(u.dim2, shift, u.dim1);}
          (shift + u.dim1) * u.dim2;
          <= {LemmaMulInequality(shift + u.dim1, dim1, u.dim2);}
          dim1 * u.dim2;
        }
        var id := from * u.dim2 + i * u.dim2 + j;
        assert id == u.dim2 * (from + i) + j by {
          LemmaMulIsDistributiveAdd(u.dim2, from, i);
        }
        LemmaFundamentalDivModConverse(id, u.dim2, from + i, j);
        u.LemmaRepr2DtoRepr();
        assert u.Repr2D[from + i][j] == u.Repr[id];
        reveal EqualSlice;
        assert padding <= from + i < u.dim1 - padding;
        assert 0 <= j < u.dim2 - 0;
        assert u.Repr2D[from + i][j] == uSpec[shift + from + i][j];
      }
    }
  }

  lemma LemmaSequenceHelper(u1:seq<real>, u2:seq<real>, from:nat, len:nat, shift:nat, id:nat) 
    requires from + len <= |u1| 
    requires shift + from + len <= |u2|
    requires u1[from..from + len] == u2[shift + from..shift + from + len]
    requires id < len
    ensures u1[from + id] == u2[shift + from + id]
  {}

  lemma LemmaEqualWithPaddingFlattenConverse
    (u:ArrayOfReals2D, uSpec:seq<seq<real>>, 
     dim1:nat, shift:nat, from:nat, len:nat, fromFull:nat, lenFull:nat)
    requires u.IsValid()
    requires |uSpec| == dim1
    requires forall i :: 0 <= i < |uSpec| ==> |uSpec[i]| == u.dim2
    requires dim1 >= shift + u.dim1
    requires fromFull == from * u.dim2
    requires lenFull == len * u.dim2
    requires u.length >= fromFull + lenFull
    requires len > 0
    requires u.dim2 > 0
    requires from + len <= u.dim1
    requires 
     calc {
         fromFull + lenFull;
      == {LemmaMulIsDistributiveAdd(u.dim2, from, len);}
         (from + len) * u.dim2;
      <= {LemmaMulInequality(from+len, u.dim1, u.dim2);} 
         u.dim1 * u.dim2;
     }
     calc {
         shift * u.dim2 + fromFull + lenFull;
      == {LemmaMulIsDistributiveAdd(u.dim2, shift, from);
          LemmaMulIsDistributiveAdd(u.dim2, shift + from, len);}
         (shift + from + len) * u.dim2;
      <= {LemmaMulInequality(shift+from+len, dim1, u.dim2);} 
         dim1 * u.dim2;
     }
     (u.Repr[fromFull..fromFull + lenFull] == 
      u.Flatten(uSpec, u.dim2)[shift * u.dim2 + fromFull..
                             shift * u.dim2 + fromFull + lenFull])
    ensures EqualSlice(u, uSpec, |uSpec|, from, from+len, shift)
  {
    calc {
         fromFull + lenFull;
      == {LemmaMulIsDistributiveAdd(u.dim2, from, len);}
         (from + len) * u.dim2;
      <= {LemmaMulInequality(from+len, u.dim1, u.dim2);} 
         u.dim1 * u.dim2;
     }
     calc {
         shift * u.dim2 + fromFull + lenFull;
      == {LemmaMulIsDistributiveAdd(u.dim2, shift, from);
          LemmaMulIsDistributiveAdd(u.dim2, shift + from, len);}
         (shift + from + len) * u.dim2;
      <= {LemmaMulInequality(shift+from+len, dim1, u.dim2);} 
         dim1 * u.dim2;
     }
    for i := from to from+len
      invariant forall i', j :: (from <= i' < i && 0 <= j < u.dim2) 
                  ==> && shift + i' < |uSpec| 
                      && u.Repr2D[i'][j] == uSpec[shift + i'][j]
    {
      for j := 0 to u.dim2 
        invariant forall j' :: (0 <= j' < j) 
                    ==> u.Repr2D[i][j'] == uSpec[shift + i][j']
      {
        calc {
          i * u.dim2 + j; 
          < i * u.dim2 + u.dim2;
          == (i + 1) * u.dim2;
          <= {LemmaMulInequality(i+1, from+len, u.dim2);}
             (from + len) * u.dim2;
          <= {LemmaMulInequality(from+len, u.dim1, u.dim2);}
             u.dim1 * u.dim2;
        }
        assert u.Repr2D[i][j] == u.Repr[i * u.dim2 + j];
        var diff := i - from;
        assert i * u.dim2 + j == fromFull + diff * u.dim2 + j by {
          LemmaMulIsDistributiveAdd(u.dim2, from, diff);
        }
        assert diff <= len - 1;
        calc {
            diff * u.dim2 + j;
          <= {LemmaMulInequality(diff, len-1, u.dim2);}
            (len-1) * u.dim2 + j;
          < (len-1) * u.dim2 + u.dim2;
          == {LemmaMulIsDistributiveAdd(u.dim2, len-1, 1);}
            lenFull;
        }
        LemmaSequenceHelper(u.Repr, u.Flatten(uSpec, u.dim2), 
          fromFull, lenFull, shift * u.dim2, diff * u.dim2 + j);
      }
    }
    reveal EqualSlice;
  }
}