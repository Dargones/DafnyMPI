include "MPIResource.dfy"

module MPI {

  import opened MPIResource
  import opened Std.Arithmetic.Mul

  type NatPlus = i: int | i >= -1

  datatype BarrierKind<T> = 
    Simple(nextTag:nat) 
  | Gather(root:nat, whole:seq<T>, nextTag:nat)
  | AllReduceAnd(value: int -> bool, nextTag:nat) // could add other operations

  method {:extern} {:axiom} GetMPISize() 
    returns (size:nat)

  class World<T> {

    // Specified on creation:
    const size:nat
    const rank:nat
    ghost const RelySend: (nat, nat) -> nat    // tag, size -> sender
    ghost const RelyRecv: (nat, nat) -> nat    // tag, size -> receiver
    ghost const RelyMess: (nat, nat) -> seq<T> // tag, size -> value
    ghost const Barriers: (nat, nat) -> BarrierKind<T>
    ghost const LastBarrier: nat -> nat        // size -> ID

    ghost function BarrierID():nat reads this
    ghost function Tag():NatPlus reads this
    ghost function SendBuffer():set<nat> reads this
    ghost function RecvBuffer():set<nat> reads this
    ghost predicate Finalized() reads this

    ghost function RelySendFull(tag:nat):nat 
      reads this
    { RelySend(tag, size) }

    ghost function RelyRecvFull(tag:nat):nat 
      reads this
    { RelyRecv(tag, size) }

    ghost function RelyMessFull(tag:nat):seq<T>
      reads this
    { RelyMess(tag, size) }

    ghost function BarriersFull(id:nat):nat
      reads this
    { Barriers(id, size).nextTag }

    static ghost predicate {:opaque} NoTagBeforeStatic
      (prev:NatPlus, tag:nat, size:nat, rank:nat,
       RelySend: (nat, nat) -> nat, RelyRecv: (nat, nat) -> nat) 
    {
      forall v :: prev < v < tag 
        ==> (RelyRecv(v, size) != rank && RelySend(v, size) != rank)
    }

    ghost predicate NoTagBefore(tag:nat) 
      reads this
    {
      NoTagBeforeStatic(Tag(), tag, size, rank, RelySend, RelyRecv)
    }

    lemma LemmaNoTagBeforeVacuous(tag:nat) 
      requires Tag() >= tag - 1
      ensures NoTagBefore(tag)
    {
      reveal NoTagBeforeStatic;
    }

    static ghost predicate BarriersNotTooFarApart
      (Barriers: (nat, nat) -> BarrierKind<T>, size:nat) {
      forall i :: i > 0 ==> Barriers(i, size).nextTag 
                            - Barriers(i - 1, size).nextTag < 32767
    }
    
    constructor {:axiom} {:extern} (size:nat,
                                    ghost RelyMess: (nat, nat) -> seq<T>, 
                                    ghost RelySend: (nat, nat) -> nat,
                                    ghost RelyRecv: (nat, nat) -> nat,
                                    ghost Barriers: (nat, nat) -> BarrierKind<T>,
                                    ghost LastBarrier: nat -> nat) 
      requires size > 1
      requires BarriersNotTooFarApart(Barriers, size)
      ensures rank < size
      ensures this.size == size
      ensures this.RelyMess == RelyMess
      ensures this.RelySend == RelySend
      ensures this.RelyRecv == RelyRecv
      ensures this.Barriers == Barriers
      ensures this.LastBarrier == LastBarrier
      ensures this.Tag() == -1
      ensures this.BarrierID() == 0
      ensures this.SendBuffer() == {}
      ensures this.RecvBuffer() == {}
      ensures LastBarrier(size) == 0 ==> Finalized()
      ensures LastBarrier(size) != 0 ==> !Finalized()

    method {:axiom} {:extern} ISend
      (res:MPIResource<T>, from:nat, size:nat, destination:nat, tag:nat)
      returns (handle:SendHandle<T>)
      requires !Finalized()
      requires RelySendFull(tag) == rank 
      requires RelyRecvFull(tag) == destination 
      requires tag !in SendBuffer()
      requires from + size <= res.length
      requires res.IsValid()
      requires res.FreeToRead(from, from+size)
      requires RelyMessFull(tag) == res.Repr[from..from+size]
      modifies this
      modifies res
      ensures SendBuffer() == old(SendBuffer()) + {tag}
      ensures RecvBuffer() == old(RecvBuffer())
      ensures Tag() == old(Tag())
      ensures BarrierID() == old(BarrierID())
      ensures handle.w == this
      ensures handle.tag == tag
      ensures handle.res == res
      ensures handle.from == from
      ensures handle.size == size
      ensures res.IsValid()
      ensures res.ReadLocks == res.UpdateReadLock(
        old(res.ReadLocks), from, size, 1)
      ensures res.WriteLock == old(res.WriteLock)
      ensures res.Repr == old(res.Repr)
      ensures !Finalized()

    method {:axiom} {:extern} Send
      (res:MPIResource<T>, from:nat, size:nat, destination:nat, tag:nat) 
      requires !Finalized()
      requires RelySendFull(tag) == rank 
      requires RelyRecvFull(tag) == destination 
      requires tag !in SendBuffer()
      requires tag > Tag()
      requires BarriersFull(BarrierID()) <= tag < BarriersFull(BarrierID() + 1)
      requires NoTagBefore(tag)
      requires from + size <= res.length
      requires res.IsValid()
      requires res.FreeToRead(from, from+size)
      requires RelyMessFull(tag) == res.Repr[from..from+size]
      modifies this
      modifies res
      ensures SendBuffer() == old(SendBuffer())
      ensures RecvBuffer() == old(RecvBuffer())
      ensures Tag() == tag
      ensures BarrierID() == old(BarrierID())
      ensures res.WriteLock == old(res.WriteLock)
      ensures res.ReadLocks == old(res.ReadLocks)
      ensures res.Repr == old(res.Repr)
      ensures res.IsValid()
      ensures !Finalized()
    {
      var handle := ISend(res, from, size, destination, tag);
      handle.Wait();
    }

    method {:axiom} {:extern} IRecv
      (dest:MPIResource<T>, from:nat, size:nat, source:nat, tag:nat) 
      returns (handle:RecvHandle<T>)
      requires !Finalized()
      requires RelySendFull(tag) == source
      requires RelyRecvFull(tag) == rank 
      requires tag !in RecvBuffer()
      requires from + size <= dest.length
      requires dest.IsValid()
      requires dest.FreeToWrite(from, from+size)
      modifies this
      modifies dest
      ensures SendBuffer() == old(SendBuffer())
      ensures RecvBuffer() == old(RecvBuffer()) + {tag}
      ensures Tag() == old(Tag())
      ensures BarrierID() == old(BarrierID())
      ensures handle.w == this
      ensures handle.tag == tag
      ensures handle.dest == dest
      ensures handle.from == from
      ensures handle.size == size
      ensures dest.IsValid()
      ensures dest.ReadLocks == old(dest.ReadLocks)
      ensures dest.WriteLock == dest.SetWriteLock(
        old(dest.WriteLock), from, size, true)
      ensures dest.Repr == old(dest.Repr)
      ensures !Finalized()

    method {:axiom} {:extern} Recv
      (dest:MPIResource<T>, from:nat, size:nat, source:nat, tag:nat)
      requires !Finalized()
      requires RelySendFull(tag) == source
      requires RelyRecvFull(tag) == rank 
      requires tag !in RecvBuffer()
      requires tag > Tag()
      requires NoTagBefore(tag)
      requires BarriersFull(BarrierID()) <= tag < BarriersFull(BarrierID() + 1)
      requires from + size <= dest.length
      requires size == |RelyMessFull(tag)|
      requires dest.IsValid()
      requires dest.FreeToWrite(from, from+size)
      modifies this
      modifies dest
      ensures RecvBuffer() == old(RecvBuffer())
      ensures SendBuffer() == old(SendBuffer())
      ensures Tag() == tag
      ensures BarrierID() == old(BarrierID())
      ensures dest.IsValid()
      ensures dest.Repr == dest.SetElements(
        old(dest.Repr), from, size, RelyMessFull(tag))
      ensures dest.WriteLock == old(dest.WriteLock)
      ensures dest.ReadLocks == old(dest.ReadLocks)
      ensures !Finalized()
    {
      reveal MPIResource<T>.FreeToReadStatic;
      reveal MPIResource<T>.FreeToWriteStatic;
      var handle := IRecv(dest, from, size, source, tag);
      handle.Wait();
    }

    method {:axiom} {:extern} Barrier(l:nat) 
      requires !Finalized()
      requires BarrierID() == l
      requires BarriersFull(BarrierID() + 1) > Tag()
      requires NoTagBefore(BarriersFull(BarrierID() + 1))
      requires SendBuffer() == {}
      requires RecvBuffer() == {}
      requires Barriers(l, size).Simple?
      modifies this
      ensures SendBuffer() == {}
      ensures RecvBuffer() == {}
      ensures BarrierID() == old(BarrierID()) + 1
      ensures Tag() == old(Tag())
      ensures BarrierID() == LastBarrier(size) ==> Finalized()
      ensures BarrierID() != LastBarrier(size) ==> !Finalized()

    ghost function RecursiveReduceAnd(l:nat, i:nat):bool 
      requires i <= size 
      requires Barriers(l, size).AllReduceAnd?
      decreases size - i
    {
      || i == size
      || (Barriers(l, size).value(i) && RecursiveReduceAnd(l, i + 1))
    }

    lemma LemmaRecursiveAnd(l:nat, i:nat)
      requires Barriers(l, size).AllReduceAnd?
      requires i < size 
      requires RecursiveReduceAnd(l, 0) 
      ensures Barriers(l, size).value(i)
    {
      for j := 0 to i 
        invariant RecursiveReduceAnd(l, 0) ==> RecursiveReduceAnd(l, j)
      {}
    }

    lemma LemmaRecursiveAndConverse(l:nat)
      requires Barriers(l, size).AllReduceAnd?
      requires forall i :: 0 <= i < size ==> Barriers(l, size).value(i)
      ensures RecursiveReduceAnd(l, 0) 
    {
      for j := size downto 0
        invariant RecursiveReduceAnd(l, j)
      {}
    }

    method {:axiom} {:extern} AllReduceAnd(l:nat, b:bool) returns (and:bool) 
      requires !Finalized()
      requires BarrierID() == l
      requires BarriersFull(BarrierID() + 1) > Tag()
      requires NoTagBefore(BarriersFull(BarrierID() + 1))
      requires SendBuffer() == {}
      requires RecvBuffer() == {}
      requires Barriers(l, size).AllReduceAnd?
      requires Barriers(l, size).value(rank) == b
      modifies this
      ensures SendBuffer() == {}
      ensures RecvBuffer() == {}
      ensures BarrierID() == old(BarrierID()) + 1
      ensures Tag() == old(Tag())
      ensures BarrierID() == LastBarrier(size) ==> Finalized()
      ensures BarrierID() != LastBarrier(size) ==> !Finalized()
      ensures and == RecursiveReduceAnd(l, 0)

    method {:axiom} {:extern} Gather
      (root:nat, part:MPIResource<T>, whole:MPIResource<T>, 
       partFrom:nat, partLen:nat, wholeFrom:nat, wholeLen:nat, l:nat) 
      requires !Finalized()
      requires BarrierID() == l
      requires BarriersFull(BarrierID() + 1) > Tag()
      requires NoTagBefore(BarriersFull(BarrierID() + 1))
      requires SendBuffer() == {}
      requires RecvBuffer() == {}
      requires Barriers(l, size).Gather?
      requires Barriers(l, size).root == root
      requires root < size
      requires rank < size
      requires part.IsValid()
      requires |Barriers(l, size).whole| == wholeLen 
      requires wholeLen == partLen * size
      requires part.length >= partFrom + partLen
      requires part.FreeToRead(partFrom, partFrom + partLen)
      requires (rank + 1) * partLen <= size * partLen
      requires part.Repr[partFrom..partFrom+partLen]
            == Barriers(l, size).whole[partLen * rank..partLen * (rank + 1)]
      requires (root == rank) ==> whole.IsValid()
      requires (root == rank) ==> whole != part
      requires (root == rank) ==> whole.length >= wholeFrom + wholeLen
      requires (root == rank) ==> whole.FreeToWrite(wholeFrom, 
                                                    wholeFrom + wholeLen)
      modifies this
      ensures SendBuffer() == {}
      ensures RecvBuffer() == {}
      ensures BarrierID() == old(BarrierID()) + 1
      ensures Tag() == old(Tag())
      ensures BarrierID() == LastBarrier(size) ==> Finalized()
      ensures BarrierID() != LastBarrier(size) ==> !Finalized()
      ensures part.IsValid()
      ensures part.Repr == old(part.Repr)
      ensures part.ReadLocks == old(part.ReadLocks)
      ensures part.WriteLock == old(part.WriteLock)
      ensures (root == rank) ==> whole.IsValid()
      ensures (root == rank) ==> whole.Repr == whole.SetElements(
        old(whole.Repr), wholeFrom, wholeLen, Barriers(l, size).whole)
      ensures (root == rank) ==> whole.ReadLocks == old(whole.ReadLocks)
      ensures (root == rank) ==> whole.WriteLock == old(whole.WriteLock)
  }

  

  datatype RecvHandle<T> = RecvHandle
    (w:World<T>, tag:nat, dest:MPIResource<T>, from:nat, size:nat) {
    method {:axiom} {:extern} Wait()
      requires !w.Finalized()
      requires tag > w.Tag()
      requires w.NoTagBefore(tag)
      requires          w.BarriersFull(w.BarrierID()) 
               <= tag < w.BarriersFull(w.BarrierID() + 1)
      requires w.rank == w.RelyRecvFull(tag) && tag in w.RecvBuffer()
      requires dest.IsValid()
      requires from + size <= dest.length
      requires size == |w.RelyMessFull(tag)|
      modifies w
      modifies dest
      ensures w.RecvBuffer() == old(w.RecvBuffer()) - {tag}
      ensures w.SendBuffer() == old(w.SendBuffer())
      ensures w.Tag() == tag
      ensures w.BarrierID() == old(w.BarrierID())
      ensures dest.IsValid()
      ensures dest.WriteLock == dest.SetWriteLock(
        old(dest.WriteLock), from, size, false)
      ensures dest.ReadLocks == old(dest.ReadLocks)
      ensures dest.Repr == dest.SetElements(
        old(dest.Repr), from, size, w.RelyMessFull(tag))
      ensures !w.Finalized()
  }

  datatype SendHandle<T> = SendHandle
    (w:World<T>, tag:nat, res:MPIResource<T>, from:nat, size:nat) {
    method {:axiom} {:extern} Wait()
      requires !w.Finalized()
      requires tag > w.Tag()
      requires w.NoTagBefore(tag)
      requires          w.BarriersFull(w.BarrierID()) 
               <= tag < w.BarriersFull(w.BarrierID() + 1)
      requires w.rank == w.RelySendFull(tag) && tag in w.SendBuffer()
      requires res.IsValid()
      requires from + size <= res.length
      modifies w
      modifies res
      ensures w.SendBuffer() == old(w.SendBuffer()) - {tag}
      ensures w.RecvBuffer() == old(w.RecvBuffer())
      ensures w.Tag() == tag
      ensures w.BarrierID() == old(w.BarrierID())
      ensures res.ReadLocks == res.UpdateReadLock(
        old(res.ReadLocks), from, size, -1)
      ensures res.Repr == old(res.Repr)
      ensures res.WriteLock == old(res.WriteLock)
      ensures res.IsValid()
      ensures !w.Finalized()
  }
}