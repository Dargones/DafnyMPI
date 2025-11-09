module MPIResource {

  import opened Std.Arithmetic.Mul

  trait MPIResource<T> {
    ghost const length:nat // number of elements of type T in the resource
    ghost var Repr:seq<T>  // all elements in the resource in order
    ghost var WriteLock:seq<bool> // whether one can overwrite an element
    ghost var ReadLocks:seq<int>  // whether one can read from an element
    ghost predicate IsValid() reads this {
      && length == |WriteLock|
      && length == |ReadLocks|
      && length == |Repr|
      && IsValidStronger()
    }
    ghost predicate IsValidStronger() reads this // implemented by a subclass

    function GetContiguousView(from:nat, to:nat):MPIResource<T> reads this

    static lemma LemmaWriteNonOverlapping
      (oldWriteLock:seq<bool>, newWriteLock:seq<bool>, readLocks:seq<int>,
       writeFrom:nat, writeTo:nat, from:nat, to:nat, length:nat)
      requires |oldWriteLock| == length
      requires from <= to <= length
      requires writeFrom <= writeTo <= length
      requires to <= writeFrom || writeTo <= from 
      requires newWriteLock == 
               SetWriteLock(oldWriteLock, writeFrom, writeTo - writeFrom, true)
      ensures FreeToReadStatic(oldWriteLock, length, from, to) 
        ==> FreeToReadStatic(newWriteLock, length, from, to)
      ensures FreeToWriteStatic(oldWriteLock, readLocks, length, from, to) 
        ==> FreeToWriteStatic(newWriteLock, readLocks, length, from, to)
    {
      reveal FreeToReadStatic;
      reveal FreeToWriteStatic;
      LemmaSetWriteLockGeneral(newWriteLock, oldWriteLock,
                               writeFrom, writeTo - writeFrom, true);
    }

    static lemma LemmaReadNonOverlapping
      (oldReadLocks:seq<int>, newReadLocks:seq<int>, writeLock:seq<bool>,
       readFrom:nat, readTo:nat, from:nat, to:nat, length:nat, val:int)
      requires |oldReadLocks| == length
      requires from <= to <= length
      requires readFrom <= readTo <= length
      requires to <= readFrom || readTo <= from 
      requires newReadLocks == 
               UpdateReadLock(oldReadLocks, readFrom, readTo - readFrom, val)
      ensures FreeToWriteStatic(writeLock, oldReadLocks, length, from, to) 
        ==> FreeToWriteStatic(writeLock, newReadLocks, length, from, to)
    {
      reveal FreeToReadStatic;
      reveal FreeToWriteStatic;
      LemmaUpdateReadLocksGeneral(newReadLocks, oldReadLocks,
                                 readFrom, readTo - readFrom, val);
    }

    lemma LemmaFreeToReadNarrower(from:nat, to:nat)
      requires IsValid() 
      requires from <= to <= length
      requires FreeToRead(0, this.length)
      ensures FreeToRead(from, to)
    {
      reveal FreeToReadStatic;
    }

    lemma LemmaFreeToWriteNarrower(from:nat, to:nat)
      requires IsValid() 
      requires from <= to <= length
      requires FreeToWrite(0, this.length)
      ensures FreeToWrite(from, to)
    {
      reveal FreeToWriteStatic;
    }

    lemma LemmaFreeToWriteStronger(from:nat, to:nat)
      requires IsValid() 
      requires from <= to <= length
      requires FreeToWrite(from, to)
      ensures FreeToRead(from, to)
    {
      reveal FreeToWriteStatic;
      reveal FreeToReadStatic;
    }

    ghost predicate FreeToRead(from:nat, to:nat) 
      reads this
      requires |WriteLock| == length
      requires from <= to <= length
    {
      FreeToReadStatic(WriteLock, length, from, to)
    }

    ghost predicate FreeToWrite(from:nat, to:nat) 
      reads this
      requires |WriteLock| == length
      requires |ReadLocks| == length
      requires from <= to <= length
    {
      FreeToWriteStatic(WriteLock, ReadLocks, length, from, to)
    }

    static ghost predicate {:opaque} FreeToReadStatic
      (WriteLock:seq<bool>, length:nat, from:nat, to:nat) 
    {
      && |WriteLock| == length
      && from <= to <= length
      && forall i :: from <= i < to ==> !WriteLock[i]
    }

    static ghost predicate {:opaque} FreeToWriteStatic
      (WriteLock:seq<bool>, ReadLocks:seq<int>, length:nat, from:nat, to:nat) 
    {
      && |WriteLock| == length
      && |ReadLocks| == length
      && from <= to <= length
      && (forall i :: from <= i < to ==> !WriteLock[i])
      && (forall i :: from <= i < to ==> ReadLocks[i] == 0)
    }

    static lemma LemmaSetWriteLockGeneral
      (newLock:seq<bool>, oldLock:seq<bool>, from:nat, size:nat, val:bool)
      requires from + size <= |oldLock|
      requires newLock == SetWriteLock(oldLock, from, size, val)
      ensures forall i :: 0 <= i < from ==> newLock[i] == oldLock[i]
      ensures forall i :: from <= i < from + size ==> newLock[i] == val
      ensures forall i :: from + size <= i < |newLock| ==> newLock[i] == oldLock[i]
      ensures |newLock| == |oldLock|
    {}

    static lemma LemmaUpdateReadLocksGeneral
      (newLock:seq<int>, oldLock:seq<int>, from:nat, size:nat, val:int)
      requires from + size <= |oldLock|
      requires newLock == UpdateReadLock(oldLock, from, size, val)
      ensures forall i :: 0 <= i < from ==> newLock[i] == oldLock[i]
      ensures forall i :: from <= i < from + size ==> newLock[i] == oldLock[i] + val
      ensures forall i :: from + size <= i < |newLock| ==> newLock[i] == oldLock[i]
      ensures |newLock| == |oldLock|
    {}

    static lemma LemmaSetWriteLockCancel
      (writeLock:seq<bool>, readLocks:seq<int>, from:nat, len:nat)
      requires FreeToWriteStatic(writeLock, readLocks, |writeLock|, from, from+len)
      requires from + len <= |writeLock|
      ensures SetWriteLock(
        SetWriteLock(writeLock, from, len, true), from, len, false) == writeLock
    {
      reveal FreeToWriteStatic;
    }

    static lemma LemmaUpdateReadLockCancel(readLocks:seq<int>, from:nat, len:nat)
      requires from + len <= |readLocks|
      ensures UpdateReadLock(
        UpdateReadLock(readLocks, from, len, 1), from, len, -1) == readLocks
    {}

    static ghost function SetWriteLock
      (oldLock:seq<bool>, from:nat, size:nat, val:bool):(r:seq<bool>) 
      requires from + size <= |oldLock|
      ensures |r| == |oldLock|
    {
      oldLock[..from] + seq(size, i => val) + oldLock[from+size..]
    }

    static ghost function UpdateReadLock
      (oldLock:seq<int>, from:nat, size:nat, val:int):(r:seq<int> )
      requires from + size <= |oldLock|
      ensures |r| == |oldLock|
    {
      oldLock[..from] 
        + seq(size, i => if 0 <= i + from < |oldLock| 
                         then oldLock[i + from] + val 
                         else 0) 
        + oldLock[from+size..]
    }
    static ghost function SetElements
      (oldRepr:seq<T>, from:nat, size:nat, with:seq<T>): (r:seq<T>)
      requires |with| == size
      requires from + size <= |oldRepr|
      ensures |r| == |oldRepr|
      ensures r[from..from+size] == with
      ensures r[..from] == oldRepr[..from]
      ensures r[from+size..] == oldRepr[from + size..]
    {
      oldRepr[..from] + with + oldRepr[from+size..]
    }
    lemma RevertReadLock
      (oldLock:seq<int>, midLock:seq<int>, newLock:seq<int>, from:nat, size:nat) 
      requires from + size <= |oldLock|
      requires midLock == UpdateReadLock(oldLock, from, size, 1)
      requires newLock == UpdateReadLock(midLock, from, size, -1)
      ensures newLock == oldLock
    {}
  }

  class ArrayOfReals extends MPIResource<real> {

    ghost predicate IsValidStronger() 
      reads this
    { true }

    constructor {:extern} {:axiom} (length:nat, val:real) 
      ensures IsValid()
      ensures this.length == length
      ensures FreeToWrite(0, length)
      ensures forall i :: 0 <= i < |Repr| ==> Repr[i] == val

    // This is used exclusively by MPI
    function {:extern} {:axiom} GetContiguousView
      (from:nat, to:nat):MPIResource<real> reads this

    function {:extern} {:axiom} Length():nat
      reads this
      ensures Length() == length

    function {:extern} {:axiom} Get(i:nat):real 
      requires i < length
      requires IsValid()
      requires !WriteLock[i]
      reads this
      ensures Get(i) == Repr[i]

    method {:extern} {:axiom} Set(i:nat, val:real)
      requires IsValid()
      requires i < |Repr|
      requires !WriteLock[i]
      requires ReadLocks[i] == 0
      modifies this
      ensures IsValid()
      ensures forall j :: (0 <= j < |Repr| && i != j) 
                      ==> Repr[j] == old(Repr[j])
      ensures Repr[i] == val
      ensures WriteLock == old(WriteLock)
      ensures ReadLocks == old(ReadLocks)
  }

  class ArrayOfReals2D extends MPIResource<real> {

    ghost const dim1:nat
    ghost const dim2:nat

    ghost var Repr2D:seq<seq<real>>

    ghost predicate IsValidStronger() reads this {
      IsValidReprFull(Repr2D, Repr, dim1, dim2)
    }

    ghost static predicate IsValidReprFull
      (Repr2D:seq<seq<real>>, Repr:seq<real>, dim1:nat, dim2:nat) 
    {
      && IsValidRepr(Repr2D, dim1, dim2)
      && |Repr| == dim1 * dim2
      && (forall i, j :: (0 <= i < dim1 && 0 <= j < dim2) 
            ==> assert i * dim2 + dim2 == (i + 1) * dim2;
                Repr2D[i][j] == Repr[i * dim2 + j])
    }

    ghost static predicate IsValidRepr
       (Repr2D:seq<seq<real>>, dim1:nat, dim2:nat) 
    {
       && |Repr2D| == dim1 
       && (forall i :: 0 <= i < |Repr2D| ==> |Repr2D[i]| == dim2)
    }

    constructor {:extern} {:axiom} (dim1:nat, dim2:nat, val:real) 
      ensures IsValid()
      ensures this.dim1 == dim1
      ensures this.dim2 == dim2
      ensures FreeToWrite(0, this.length)
      ensures forall i,j :: 
      (0 <= i < dim1 && 0 <= j < dim2) ==> Repr2D[i][j] == val

    // This is used exclusively by MPI
    function {:extern} {:axiom} GetContiguousView
      (from:nat, to:nat):MPIResource<real> reads this

    function {:extern} {:axiom} Dim1():nat
      reads this
      ensures Dim1() == dim1

    function {:extern} {:axiom} Dim2():nat
      reads this
      ensures Dim2() == dim2

    function {:extern} {:axiom} Get(i:nat, j:nat):real 
      requires i < dim1
      requires j < dim2
      requires IsValid()
      requires assert i * dim2 + dim2 == (i + 1) * dim2; !WriteLock[i * dim2 + j]
      reads this
      ensures Get(i, j) == Repr2D[i][j]

    method {:extern} {:axiom} Set(i:nat, j:nat, val:real)
      requires IsValid()
      requires i < dim1
      requires j < dim2
      requires assert i * dim2 + dim2 == (i + 1) * dim2; !WriteLock[i * dim2 + j]
      requires ReadLocks[i * dim2 + j] == 0
      modifies this
      ensures IsValid()
      ensures forall i', j' :: 
        (0 <= i' < dim1 && 0 <= j' < dim2 && (i != i' || j != j')) 
          ==> Repr2D[i'][j'] == old(Repr2D[i'][j'])
      ensures Repr2D[i][j] == val
      ensures WriteLock == old(WriteLock)
      ensures ReadLocks == old(ReadLocks)

    ghost static function Flatten(s:seq<seq<real>>, dim2:nat):seq<real> 
      requires forall subseq :: subseq in s ==> |subseq| == dim2
      ensures |Flatten(s, dim2)| == |s| * dim2
      ensures forall i, j :: 0 <= i < |s| && 0 <= j < dim2 
                ==> calc {
                      i * dim2 + j;
                      < i * dim2 + dim2;
                      == (i + 1) * dim2;
                      <= |s| * dim2;
                    }
                    Flatten(s, dim2)[i * dim2 + j] == s[i][j]
    {
      if |s| == 0 then [] else s[0] + Flatten(s[1..], dim2)
    }

    lemma LemmaFreeToWrite2D(i:nat, j:nat)
      requires IsValid() 
      requires i < dim1
      requires j < dim2
      requires FreeToWrite(0, length)
      ensures i * dim2 + j < length
      ensures !WriteLock[i * dim2 + j] 
      ensures ReadLocks[i * dim2 + j] == 0
    {
      calc {
        i * dim2 + j;
        < i * dim2 + dim2;
        == (i + 1) * dim2;
        <= dim1 * dim2;
        == length;
      }
      reveal FreeToWriteStatic;
    }

    lemma LemmaRepr2DtoRepr() 
      requires IsValid()
      ensures Flatten(Repr2D, dim2) == Repr
    {
      if dim2 == 0 {
        return;
      }
      for i := 0 to length 
        invariant forall j :: 0 <= j < i ==> Flatten(Repr2D, dim2)[j] == Repr[j]
      {
        var q := i / dim2;
        var r := i % dim2;
        assert q * dim2 + r == i;
        assert q < dim1 by {
          if q >= dim1 {
            calc {
              i;
              == q * dim2 + r;
              >= q * dim2;
              >= {LemmaMulInequality(dim1, q, dim2);}
                dim1 * dim2;
              == length;
            }
            assert false;
          }
        }
        assert Flatten(Repr2D, dim2)[i] == Repr2D[q][r];
        assert Repr[i] == Repr2D[q][r];
      }
    }

    lemma LemmaRepr2DUnchanged(uRepr2D:seq<seq<real>>) 
      requires IsValidReprFull(uRepr2D, Repr, dim1, dim2)
      requires IsValid()
      ensures Repr2D == uRepr2D
    {
      assert forall i :: 0 <= i < |Repr2D| ==> Repr2D[i] == uRepr2D[i];
    }

    lemma LemmaRepr2DPartiallyChanged
      (oldRepr2D:seq<seq<real>>, oldRepr:seq<real>, from:nat, len:nat) 
      requires IsValidReprFull(oldRepr2D, oldRepr, dim1, dim2)
      requires IsValid()
      requires dim2 > 0
      requires from * dim2 + len * dim2 <= |oldRepr|
      requires Repr[..from * dim2] == oldRepr[..from * dim2]
      requires Repr[from * dim2 +len * dim2..] == 
               oldRepr[from * dim2 + len * dim2..]

      ensures from + len <= dim1
      ensures forall i, j :: 0 <= i < from && 0 <= j < dim2 
                ==> Repr2D[i][j] == oldRepr2D[i][j]
      ensures forall i, j :: from + len <= i < dim1 && 0 <= j < dim2 
                ==> Repr2D[i][j] == oldRepr2D[i][j]       
    {
      if from + len > dim1 {
        calc{
          from * dim2 + len * dim2;
          == {LemmaMulIsDistributiveAdd(dim1, from, len);}
          (from + len) * dim2;
          > {LemmaMulStrictInequality(dim1, from + len, dim2);}
          dim1 * dim2;
          == length;
        }
      }
      for i := 0 to from 
        invariant forall i', j :: 0 <= i' < i && 0 <= j < dim2 
                    ==> Repr2D[i'][j] == oldRepr2D[i'][j]
      {
        for j := 0 to dim2 
          invariant forall j' :: 0 <= j' < j
                      ==> Repr2D[i][j'] == oldRepr2D[i][j']
        {
          calc {
              i * dim2 + j;
            < i * dim2 + dim2;
            == (i + 1) * dim2;
            <= {LemmaMulInequality(i + 1, from, dim2);}
               from * dim2;
          }
        }
      }
      for i := from + len to dim1 
        invariant forall i', j :: from + len <= i' < i && 0 <= j < dim2 
                    ==> Repr2D[i'][j] == oldRepr2D[i'][j]
      {
        for j := 0 to dim2 
          invariant forall j' :: 0 <= j' < j
                      ==> Repr2D[i][j'] == oldRepr2D[i][j']
        {
          calc {
              i * dim2 + j;
            < i * dim2 + dim2;
            == (i + 1) * dim2;
            <= {LemmaMulInequality(i + 1, dim1, dim2);}
               dim1 * dim2;
          }
          calc {
              i * dim2 + j;
            >= {LemmaMulInequality(from + len, i, dim2);} 
               (from + len) * dim2 + j;
            >= (from + len) * dim2;
            == {LemmaMulIsDistributiveAdd(dim2, from, len);}
               from * dim2 + len * dim2;
          }
        }
      }
    }
  }

} 