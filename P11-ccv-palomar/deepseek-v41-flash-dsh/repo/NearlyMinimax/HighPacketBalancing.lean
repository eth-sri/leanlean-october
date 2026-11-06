module

public import NearlyMinimax.HighReferenceBalancing
public import NearlyMinimax.PacketAbsoluteMoments

@[expose] public section

/-! The actual ordinary separated packet has a genuine centered reference
law; its slope centering follows from derivative-rule reflection. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace NearlyMinimax

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

variable (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (m r D q : ℕ) (C δ : ℝ)
  (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
  (hcost : Integrable (separatedMatrixCost A) σ)
  (hpos : 0 < highPacketMarkMass σ a b m r D q C A)

include hA hcost hpos

end Packet

variable {d : ℕ}

def highCenterResolutionThreshold (C : ModelConstants d) : ℝ :=
  max 2 (highCenterRadius C)⁻¹

theorem highCenterResolution_guards (C : ModelConstants d) (M : ℝ)
    (hM : highCenterResolutionThreshold C ≤ M) : 2 ≤ M ∧ 1 / M ≤ highCenterRadius C := by
  have hM2 := (le_max_left _ _).trans hM
  have hMr := (le_max_right _ _).trans hM
  have hM0 : 0 < M := by linarith
  refine ⟨hM2, ?_⟩
  apply (div_le_iff₀ hM0).mpr
  have hh := mul_le_mul_of_nonneg_left hMr (highCenterRadius_pos C).le
  rw [mul_inv_cancel₀ (highCenterRadius_pos C).ne'] at hh
  nlinarith

end NearlyMinimax
