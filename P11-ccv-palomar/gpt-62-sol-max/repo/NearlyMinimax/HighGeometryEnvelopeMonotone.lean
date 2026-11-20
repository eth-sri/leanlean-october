module

public import NearlyMinimax.HighCompleteGeometry
public import NearlyMinimax.CompleteSourceSaddleParameters


@[expose] public section

/-! The true source activation budget dominates its unbalanced row mass,
and the complete geometry H increases with this budget. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
attribute [local instance] Classical.propDecidable

theorem SourceGeometry.envelope_mono_total {d : ℕ} (S : SourceGeometry d) (Chi : ℝ) {B1 B2 : ℝ}
    (hB1 : 0 ≤ B1) (hB : B1 ≤ B2) (n : ℕ) (U : Fin n → Covariate d) :
    S.envelope Chi B1 n U ≤ S.envelope Chi B2 n U := by
  rcases n with _|_|_|n <;> simp only [envelope, le_refl]
  split_ifs
  · exact le_rfl
  · gcongr <;> linarith

 theorem rowMass_le_balanced_source_activity {d k F : ℕ} {I : Type*} [Fintype I]
    {E : I → Type*} [∀ i, MeasurableSpace (E i)] (C : ModelConstants d)
    (R : HighUnionRowData d k F I E) (hR : 0 ≤ highRowTotalMass R.rowMass) :
    highRowTotalMass R.rowMass ≤ highRowTotalMass R.rowMass/highCenterMix C := by
  apply (le_div_iff₀ (highCenterMix_mem C).1).mpr
  exact mul_le_of_le_one_right hR (highCenterMix_mem C).2.le

end NearlyMinimax
