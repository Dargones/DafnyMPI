include "MPIResource.dfy"

module ExternUtils {

  import opened MPIResource

  function {:axiom} {:extern} Sqrt(val:real) : real 
    requires val >= 0.0
    ensures val > 1.0 ==> Sqrt(val) < val
    ensures 0.0 < val < 1.0 ==> Sqrt(val) > val
    ensures (val == 1.0 || val == 0.0) ==> Sqrt(val) == val

  function {:axiom} {:extern} Sin(val:real) : real 
    ensures -1.0 <= Sin(val) <= 1.0

  function {:axiom} {:extern} Pi() : real 
    ensures Pi() != 0.0

  method {:axiom} {:extern} Plot1D
    (u:ArrayOfReals, filename:string, 
     minx:real, maxx:real, miny:real, maxy:real,
     xname:string, yname:string)
    requires u.IsValid()
    requires u.FreeToRead(0, u.length)

  method {:axiom} {:extern} Plot2D
    (u:ArrayOfReals2D, filename:string, 
     minx:real, maxx:real, miny:real, maxy:real, vmin:real, vmax:real,
     xname:string, yname:string)
     requires u.IsValid()
     requires u.FreeToRead(0, u.length)

  method {:axiom} {:extern} Plot2DV2
    (u:ArrayOfReals2D, filename:string, 
     minx:real, maxx:real, miny:real, maxy:real, 
     xname:string, yname:string)
     requires u.IsValid()
     requires u.FreeToRead(0, u.length)

}