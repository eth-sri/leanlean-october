module

public import PottsDiscontinuity.Duality.ZeroOne
public import PottsDiscontinuity.RCInfinite.PercolationZeroOne

/-! The proved zero–one law for infinite-volume random-cluster measures
(`RCInfinite/PercolationZeroOne.lean`), on the exact cluster events of the planar-duality
library (`Duality/`). -/

@[expose] public section

namespace PottsDiscontinuity.Duality
open FK MeasureTheory

lemma infiniteClusterAt_eq_infiniteAt (v : LatticeVertex) :
    infiniteClusterAt v = RCInfinite.infiniteAt v := rfl

/-- Positivity for the existence event is equivalent to positivity at the origin. -/
theorem existsInfiniteCluster_pos_iff_origin_pos (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ) :
    0 < μ existsInfiniteCluster ↔ 0 < μ (infiniteClusterAt 0) :=
  RCInfinite.infiniteCluster_pos_iff_origin_pos θ i μ hμ

end PottsDiscontinuity.Duality
