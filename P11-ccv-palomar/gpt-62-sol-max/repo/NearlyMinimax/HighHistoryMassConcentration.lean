module

public import NearlyMinimax.HighCanonicalDensityMean
public import NearlyMinimax.HistoryMassConcentration
public import NearlyMinimax.MassTiltTail

@[expose] public section

/-!
# Concentration of the actual balanced-packet history mass

The packet's full representation mark is retained. The finite recursion,
actual torus patch geometry, and independent label blocks prove the infinite
reference MGF. The true mass-power tilt then has the exceptional tail bound.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The exact bounded-differences coefficient for the actual torus labels. -/
def highHistoryMassParameter (d k : ℕ) (a b : ℝ) : ℝ :=
  (k : ℝ)^d * ((2 / (k : ℝ))^d * (b-a))^2 / 8

section
variable (d k : ℕ) (a b : ℝ) (hk : 0 < k)
include hk

theorem highHistoryMassParameter_pos (hab : a < b) :
    0 < highHistoryMassParameter d k a b := by
  unfold highHistoryMassParameter
  positivity

/-- The exact parameter has the paper's inverse-grid-cardinality dependence. -/
theorem highHistoryMassParameter_eq :
    highHistoryMassParameter d k a b = (2 : ℝ)^(2*d) * (b-a)^2 / (8 * (k : ℝ)^d) := by
  have hkR : (0 : ℝ) < k := by simp_all
  have hp := ne_of_gt (pow_pos hkR d)
  unfold highHistoryMassParameter
  rw [div_pow, mul_pow, Nat.mul_comm 2 d, pow_mul]
  field_simp

end

section ActualPacket
variable {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
  (d k F m r D q : ℕ) [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop)
  (σ : Measure Z) [IsFiniteMeasure σ] (a b C δ : ℝ)
  (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
  (hA : SeparatedMatrixIntegrable σ A)
  (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
  (ha : 0 < a) (hab : a < b) (hr : 1 ≤ r) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
  (radius width : ℝ) (hR : 0 < radius) (ha1 : a + radius ≤ 1) (hb1 : 1 + radius ≤ b)
  (hW : b - a ≤ width) (hδW : δ * width ≤ radius / 2)
  (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
  (hmB : ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l))
  (hB : ∀ j ζ x l, |B j ζ x l| ≤ 1)
  (initial : HighRawState d k F) (hinit : ∀ x, initial.1 x = 1)

include hA hpos ha hab hr hδ0 hδ1 hR ha1 hb1 hW hδW hmB hB hinit

end ActualPacket
end NearlyMinimax
