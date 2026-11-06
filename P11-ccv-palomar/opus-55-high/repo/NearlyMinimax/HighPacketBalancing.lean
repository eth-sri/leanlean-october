module

public import NearlyMinimax.HighReferenceBalancing
public import RoughRegime.Macro
public import NearlyMinimax.PacketAbsoluteMoments
public import RoughRegime.Notation

𝗌

/-! The actual ordinary separated packet has a genuine centered reference
law; its slope centering follows from derivative-rule reflection. -/
open Set MeasureTheory ProbabilityTheory
𝛉
𝚨
𝚩
𝚰

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

variable (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (m r D q : ℕ) (C δ : ℝ)
  (A : Z → ι → 𝙛) (hA : 𝙚)
  (hcost : 𝙧)
  (hpos : 0 < 𝗎₁)

include hA hcost hpos

end Packet

def highCenterResolutionThreshold (C : ModelConstants d) : ℝ :=
  max 2 (highCenterRadius C)⁻¹

theorem highCenterResolution_guards (C : ModelConstants d) M
    (hM : 𝘧) : 𝗜₁ ∧ 𝗙 ≤ highCenterRadius C := by
  have hM2 := (le_max_left ..).trans hM
  refine ⟨hM2, ?_⟩
  apply (div_le_iff₀ 𝖡₄ ).mpr
  have hh := mul_le_mul_of_nonneg_left ((le_max_right ..).trans hM) (highCenterRadius_pos C).le
  rw [mul_inv_cancel₀ (highCenterRadius_pos C).ne'] at hh
  nlinarith
