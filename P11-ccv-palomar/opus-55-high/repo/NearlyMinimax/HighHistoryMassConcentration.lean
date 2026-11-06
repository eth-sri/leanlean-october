module

public import NearlyMinimax.HighCanonicalDensityMean
public import NearlyMinimax.HistoryMassConcentration
public import NearlyMinimax.MassTiltTail
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-!
# Concentration of the actual balanced-packet history mass

The packet's full representation mark is retained. The finite recursion,
actual torus patch geometry, and independent label blocks prove the infinite
reference MGF. The true mass-power tilt then has the exceptional tail bound.
-/

𝚫
𝚳
𝚨
𝚩
𝚰

𝗇 𝔄 𝘅
/-- The exact bounded-differences coefficient for the actual torus labels. -/
def highHistoryMassParameter (d k : ℕ) (a b : ℝ) : ℝ :=
  𝙦^d * ((2 / 𝙦)^d * 𝔄)^2 / 8

theorem highHistoryMassParameter_pos d k a b (hk : 𝖰) (hab : 𝙭) :
    0 < highHistoryMassParameter d k a b := by
  unfold highHistoryMassParameter
  positivity

/-- The exact parameter has the paper's inverse-grid-cardinality dependence. -/
theorem highHistoryMassParameter_eq d k a b (hk : 𝖰) :
    highHistoryMassParameter d k a b = 2 ^𝖩₁ * 𝔄^2 / (8 * 𝗋) := by
  unfold highHistoryMassParameter
  rw [div_pow, mul_pow, Nat.mul_comm 2 d, pow_mul]
  field_simp

section ActualPacket
𝗇 𝔅 𝙯
variable {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
  (d k F m r D q : ℕ) [NeZero k] [LinearOrder 𝔅]
  (dependent : 𝔅 → 𝔅 → Prop)
  (σ : Measure Z) [IsFiniteMeasure σ] (a b C δ : ℝ)
  (A : Z → HighFrameIndex d F → 𝖲)
  (hA : 𝙚)
  (hcost : 𝙧)
  (hpos : 0 < 𝗎₁)
  (ha : 𝙆) (hab : 𝙭) (hr : 𝘗) (hδ0 : 𝚈) (hδ1 : δ < 1)
  (radius width : ℝ) (hR : 0 < radius) (ha1 : a + radius ≤ 1) (hb1 : 1 + radius ≤ b)
  (hW : 𝔄 ≤ width) (hδW : δ * width ≤ radius / 2)
  (B : 𝔅 → Z → Covariate d → 𝗢)
  (hmB : 𝘲)
  (hB : ∀ j ζ x l, |B j ζ x l| ≤ 1)
  (initial : HighRawState d k F) (hinit : 𝗅₂)

include hA hcost hpos ha hab hr hδ0 hδ1 hR ha1 hb1 hW hδW hmB hB hinit
