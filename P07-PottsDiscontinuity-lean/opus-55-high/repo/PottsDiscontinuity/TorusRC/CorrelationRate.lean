module

public import PottsDiscontinuity.TorusRC.MeasureBridge
public import PottsDiscontinuity.CorrLength.RotatedFreeLimit

/-! # The unique correlation rate of the exact rotated free law (`CorrLength/`) -/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.TorusRC

open CorrLength

section
variable (q : Set.Ici (1 : ℝ))
/-- Fekete's theorem gives a unique real limit for the source rate sequence. -/
theorem critical_rotated_rate_existsUnique  :
    ∃! a : ℝ, Tendsto (fun n : ℕ =>
      -Real.log ((rotatedDiagonalConnectionProbability (torusRCBridgeParameters q) n : NNReal):ℝ) /
        ((2*n:ℕ):ℝ)) atTop (𝓝 a) := by
  obtain ⟨a,_,h,_⟩ := rotated_correlation_rate_exists (torusRCBridgeParameters q)
  refine ⟨a/2,h,?_⟩
  intro b hb
  exact tendsto_nhds_unique hb h

/-- The source ξ(q)⁻¹: the unique limit of -log φ⁰_L(0↔(0,2n))/(2n).
The existence and uniqueness proof holds for every q in the whole carrier. -/
noncomputable def inverseCorrelationLength  : ℝ :=
  Classical.choose (critical_rotated_rate_existsUnique q)

theorem tendsto_inverseCorrelationLength  :
    Tendsto (fun n : ℕ =>
      -Real.log ((rotatedDiagonalConnectionProbability (torusRCBridgeParameters q) n : NNReal):ℝ) /
        ((2*n:ℕ):ℝ)) atTop (𝓝 (inverseCorrelationLength q)) :=
  (Classical.choose_spec (critical_rotated_rate_existsUnique q)).1
end

end PottsDiscontinuity.TorusRC
