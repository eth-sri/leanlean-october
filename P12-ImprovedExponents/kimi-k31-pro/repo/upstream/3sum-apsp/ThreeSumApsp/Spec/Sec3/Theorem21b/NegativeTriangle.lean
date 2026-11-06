module

public import ThreeSumApsp.Spec.Sec3.Problems
public import ThreeSumApsp.Util.BinaryPrefixes

@[expose] public section

namespace ThreeSumApsp.Spec

/-- At the top level the prefixes are zero. -/
theorem map_prefQ_start {L : ℕ} {Z : List ℤ} (h : ∀ z ∈ Z, 0 ≤ z ∧ z < 2 ^ L) :
    Z.map (prefQ L) = affL 0 0 Z :=
  List.map_congr_left fun z hz => by simp [prefQ_start (h z hz).1 (h z hz).2]

end ThreeSumApsp.Spec
