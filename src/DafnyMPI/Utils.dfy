module Utils {

  function max(a:real, b:real):real {
    if a > b then a else b
  }

  function min(a:real, b:real):real {
    if a < b then a else b
  }

  function minNat(a:nat, b:nat):nat {
    if a < b then a else b
  }

  function maxNat(a:int):nat {
    if a >= 0 then a else 0
  }

  lemma Lemma2DSeqsAreEqual<T>
    (s1:seq<seq<T>>, s2:seq<seq<T>>, dim2:nat, F:(nat, nat) -> T)
    requires |s1| == |s2|
    requires forall i :: 0 <= i < |s1| ==> |s1[i]| == dim2
    requires forall i :: 0 <= i < |s2| ==> |s2[i]| == dim2
    requires forall i, j :: (0 <= i < |s1| && 0 <= j < dim2) ==>
      s1[i][j] == F(i, j)
    requires forall i, j :: (0 <= i < |s2| && 0 <= j < dim2) ==>
      s2[i][j] == F(i, j)
    ensures s1 == s2
  {
    assert forall i :: (0 <= i < |s1|) ==> s2[i] == s1[i];
  }
}