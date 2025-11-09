include "../DafnyMPI/Externs/MPI.dfy"
include "../DafnyMPI/Externs/MPIResource.dfy"

module Example {

  import opened MPI
  import opened MPIResource

  function Spec(size:nat, F: int -> real, G: (real,real) -> real): (r:seq<real>)
    ensures |r| == size
    ensures (forall i :: 0 <= i < |r| ==> r[i] == G(F(i), F(i-1)))
  {
    if size == 0 
    then []
    else Spec(size - 1, F, G) + [(G(F(size - 1), F(size - 2)))]
  }

  method Main(size:nat, F: int -> real, G: (real,real) -> real) 
    returns (value:ArrayOfReals, cert:MPI.World<real>)
    requires 32767 > size > 1
    ensures cert.rank == 0 ==> value.Repr == Spec(size, F, G)
    ensures cert.Finalized()
  { 
    cert := new MPI.World<real>(
      size,                     // size
      (tag, size) => [F(tag)],  // message
      (tag, size) => tag,       // sender
      (tag, size) => tag+1,     // receiver
      (id:nat, size:nat) => MPI.BarrierKind.Gather
        (0, Spec(size, F, G), id * (if size == 0 then 0 else size - 1)),
      (size) => 1);        // last barrier
    var rank := cert.rank;
    var curr := new ArrayOfReals(1, F(rank));
    var prev := new ArrayOfReals(1, F(-1));
    reveal cert.NoTagBeforeStatic;
    reveal ArrayOfReals.FreeToWriteStatic;
    reveal ArrayOfReals.FreeToReadStatic;
    if rank == 0 {
      var req := cert.ISend(curr, 0, 1, rank+1, rank);
      req.Wait();
    } else if rank == size - 1 {
      var req := cert.IRecv(prev, 0, 1, rank-1, rank-1);
      req.Wait();
    } else {
      var req := cert.ISend(curr, 0, 1, rank+1, rank);
      var req2 := cert.IRecv(prev, 0, 1, rank-1, rank-1);
      req2.Wait();
      req.Wait();
    }
    var part := new ArrayOfReals(1, G(curr.Get(0), prev.Get(0)));
    value := part;
    if rank == 0 {
      value := new ArrayOfReals(size, 0.0);
    } 
    cert.Gather(0, part, value, 0, 1, 0, size, 0);
  }

}