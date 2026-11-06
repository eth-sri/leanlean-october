module

public import PottsDiscontinuity.Potts.FinitePartitionLimits

/-! Expectations of the affine connection indicators in the spin identities. -/

public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory
noncomputable section
variable {A X : Type*} [Finite A] [MeasurableSpace X]
local instance algebraSetoidFintype : Fintype (Setoid A) := Fintype.ofFinite _

section
variable (μ : Measure X) [IsProbabilityMeasure μ] (r : X → Setoid A) (hr : ∀ R, MeasurableSet {x | r x = R})
include μ hr
theorem sum_partition_mass  :
    ∑ R : Setoid A, μ.real {x | r x = R} = 1 := by
  have hs := sum_measureReal_preimage_singleton (μ := μ) Finset.univ
    (fun R _ => hr R)
  aesop

theorem sum_partition_mass_indicator (P : Setoid A → Prop) :
    (∑ R : Setoid A, if P R then μ.real {x | r x = R} else 0) = μ.real {x | P (r x)} := by
  rw [← Finset.sum_filter]
  have hs := sum_measureReal_preimage_singleton (μ := μ) (Finset.univ.filter P)
    (fun R _ => hr R)
  aesop

/-- Average a corrected spin kernel over its exact finite connection partition. -/
theorem partitionExpectation_affine_indicator (P : Setoid A → Prop) (a b : ℝ) :
    partitionExpectation μ r (fun R => a + b * (if P R then 1 else 0)) =
      a + b * μ.real {x | P (r x)} := by
  unfold partitionExpectation
  have ht (R : Setoid A) : μ.real {x | r x = R} * (a + b * (if P R then 1 else 0)) =
      a * μ.real {x | r x = R} + b * (if P R then μ.real {x | r x = R} else 0) := by
    grind
  simp_rw [ht]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_partition_mass μ r hr, sum_partition_mass_indicator μ r hr P]
  ring
end

end
end PottsDiscontinuity.Potts
