module Spec {

  function {:opaque} SetRange(curr:seq<real>, low:nat, high:nat, value:real)
    :(r:seq<real>)
    requires low <= high <= |curr|
    decreases high - low
    ensures |r| == |curr|
    ensures forall i :: low <= i < high ==> r[i] == value
    ensures forall i :: (0 <= i < low || |r| > i >= high) 
                        ==> r[i] == curr[i]
  {
    if low >= high 
    then curr
    else SetRange(curr[low := value], low + 1, high, value)
  }

  function {:opaque} SpecInit(nx:nat, dx:real, low:real, high:real, value:real)
    :(r:seq<real>)
    requires dx > 0.0
    requires low > 0.0
    requires (low/dx).Floor <= (high / dx + 1.0).Floor < nx
    ensures |r| == nx
  {
    SetRange(
      seq<real>(nx, i => 1.0),
      (low/dx).Floor, 
      (high / dx + 1.0).Floor, 
      value)
  }

  function {:opaque} F(c:real, dt:real, dx:real): (real,real)->real 
    requires dx > 0.0
  {
    (one,two) => one - c * dt / dx * (one - two)
  }

  function {:opaque} Spec(nt:nat, initial:seq<real>, F:(real,real)->real) 
    :(r:seq<real>)
    ensures |r| == |initial|
  {
    SpecOuterHelper(0, nt, initial, F)
  }

  function {:opaque} SpecOuterHelper(
    n:nat, 
    nt:nat, 
    curr:seq<real>,
    F:(real,real)->real)
    :(r:seq<real>)
    decreases nt - n 
    ensures |r| == |curr|
  {
    if n >= nt 
    then curr 
    else var prev := SpecOuterHelper(n + 1, nt, curr, F);
    SpecInnerHelper(1, |curr|, prev, prev, F)
  }

  function {:opaque} SpecInnerHelper(
    low:nat, 
    high:nat,
    curr:seq<real>, 
    prev:seq<real>,
    F:(real,real)->real)
    :(r:seq<real>)
    requires low > 0
    requires high <= |curr|
    requires |prev| == |curr|
    decreases |curr| - low
    ensures |r| == |curr|
  {
    if low >= high then curr
    else SpecInnerHelper(low + 1, high, 
                         curr[low := F(prev[low], prev[low - 1])],
                        prev, F)
  }

  lemma SpecInnerLemma(
    low:nat, 
    high:nat,
    curr:seq<real>,
    prev:seq<real>,
    F:(real,real)->real,
    r:seq<real>
  ) 
    requires low > 0
    requires high <= |curr|
    requires |prev| == |curr|
    requires r == SpecInnerHelper(low, high, curr, prev, F)
    decreases high - low
    ensures forall i :: (low <= i < high 
      ==> r[i] == F(prev[i], prev[i - 1]))
    ensures forall i :: ((high <= i < |r|) ==> r[i] == curr[i])
    ensures forall i :: ((0 <= i < low && i < |r|) ==> r[i] == curr[i])
  {
    reveal SpecInnerHelper;
    if low < high - 1 {
      var newCurr := curr[low := F(prev[low], prev[low - 1])];
      var rTemp := SpecInnerHelper(low + 1, high, newCurr, prev, F);
      SpecInnerLemma(low + 1, high, newCurr, prev, F, rTemp);
    }
  }

  lemma SpecInnerLemmaCorollary(
    low:nat, 
    high:nat,
    curr:seq<real>, 
    prev:seq<real>,
    F:(real,real)->real
  ) 
    requires low > 0
    requires high <= |curr|
    requires |prev| == |curr|
    requires forall i :: ((low <= i < high) 
      ==> curr[i] == F(prev[i], prev[i - 1]))
    requires forall i :: ((0 <= i < low && i < |curr|) ==> curr[i] == prev[i])
    requires forall i :: ((high <= i < |curr|) ==> curr[i] == prev[i])
    decreases high - low
    ensures curr == SpecInnerHelper(low, high, prev, prev, F)
  {
    var newCurr := SpecInnerHelper(low, high, prev, prev, F);
    SpecInnerLemma(low, high, prev, prev, F, newCurr);
    assert forall i {:trigger newCurr[i]} :: (low <= i < high
      ==> newCurr[i] == F(prev[i], prev[i - 1]));
  }

  lemma SpecOuterLemma(
    n:nat, nt:nat, init:seq<real>, prev:seq<real>, 
    out:seq<real>, F:(real,real)->real)
    requires n < nt
    requires |init| > 0
    requires prev == SpecOuterHelper(nt - n, nt, init, F)
    requires out == SpecOuterHelper(nt - n - 1, nt, init, F)
    decreases nt - n
    ensures forall j:nat :: 0 < j < |init| ==> 
      out[j] == F(prev[j], prev[j - 1])
  {
    assert out == SpecInnerHelper(1, |init|, prev, prev, F) by {
      reveal SpecOuterHelper;
    }
    reveal SpecInnerHelper;
    ghost var curr := prev;
    for i := 1 to |init|
      invariant |curr| > 0
      invariant curr[0] == prev[0]
      invariant |curr| == |init|
      invariant out == SpecInnerHelper(i, |init|, curr, prev, F)
      invariant forall j :: 1 <= j < i ==> curr[j] == F(prev[j], prev[j - 1])
    {
      curr := curr[i := F(prev[i], prev[i - 1])];
      reveal SpecInnerHelper;
    }
  }

  lemma SpecOuterLemmaInit(
    n:nat, nt:nat, 
    init:seq<real>, out:seq<real>, F:(real, real) -> real)
    requires n <= nt
    requires |init| > 0
    requires out == SpecOuterHelper(n, nt, init, F)
    decreases nt - n
    ensures out[0] == init[0]
  {
    if (n == nt) {
      reveal SpecOuterHelper;
      assert out[0] == init[0];
    } else {
      var prev := SpecOuterHelper(n + 1, nt, init, F);
      assert out == SpecInnerHelper(1, |init|, prev, prev, F) by {
        reveal SpecOuterHelper;
      }
      reveal SpecInnerHelper;
      ghost var curr := prev;
      for i := 1 to |init| 
        invariant |curr| > 0
        invariant curr[0] == prev[0]
        invariant |curr| == |init|
        invariant out == SpecInnerHelper(i, |init|, curr, prev, F)
      {
        curr := curr[i := F(prev[i], prev[i - 1])];
        reveal SpecInnerHelper;
      }
      assert out == curr;
      assert curr[0] == prev[0];
      SpecOuterLemmaInit(n + 1, nt, init, prev, F);
    }
  }

  lemma SpecOuterLemmaCorollary(n:nat, nt:nat,  
                                lower:nat, upper:nat,
                                init:seq<real>, prev:seq<real>, u:seq<real>,
                                F:(real,real) -> real)
    requires n < nt
    requires |init| > 0
    requires lower < upper <= |init|
    requires |u| == upper - lower
    requires prev == SpecOuterHelper(nt - n, nt, init, F)
    requires forall j:nat :: 0 < j < upper - lower ==> 
      u[j] == F(prev[lower + j], prev[lower + j - 1])
    requires lower == 0 ==> u[0] == init[0]
    requires lower != 0 ==> u[0] == F(prev[lower], prev[lower - 1])
    ensures forall i:nat :: i < |u| ==> 
        u[i] == SpecOuterHelper(nt - n - 1, nt, init, F)[lower + i]
  {
    ghost var out := SpecOuterHelper(nt - n - 1, nt, init, F);
    SpecOuterLemma(n, nt, init, prev, out, F);
    SpecOuterLemmaInit(nt - n - 1, nt, init, out, F);
  }
}