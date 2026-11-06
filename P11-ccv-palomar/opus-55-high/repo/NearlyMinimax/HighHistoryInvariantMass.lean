module

public import NearlyMinimax.HighHistoryMassConcentration
public import NearlyMinimax.HistoryInvariantLaw
public import NearlyMinimax.HistoryPatchStateAppend
public import NearlyMinimax.HighCanonicalDensityMean
public import NearlyMinimax.HighPacketBalancing
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-!
# The actual balanced-packet invariant mass law

The source dependency relation is the genuine torus-neighbor relation.
-/
𝚫
𝚨
𝚩
𝚰

𝗇 𝔄 dependentLabelFinset 𝖫 j
𝗇 𝔇 𝚐
theorem highNeighbor_dependency_card (d k : ℕ) [NeZero k] j :
    (𝔄).card ≤ 𝔇 := by
  classical
  have he : 𝔄 =
      highNeighborLabels d k j := by
    simp [dependentLabelFinset]
  rw [he]
  exact highNeighborLabels_card_le d k j

/-- The true tilted exceptional mass probability is determined by the genuine mass law. -/
theorem massPowerTilt_abs_event_eq_of_massLaw [MeasurableSpace Ω]
    (μ ν : Measure Ω) m (hm : Measurable m) n
    (hlaw : μ.map m = ν.map m) ε :
    (massPowerTilt μ m n).real {ω | ε < |m ω - 1|} =
      (massPowerTilt ν m n).real {ω | ε < |m ω - 1|} := by
  have hS : MeasurableSet {z : ℝ | ε < |z - 1|} :=
    measurableSet_lt measurable_const (measurable_id.sub measurable_const).abs
  have he := congrArg (fun μ' => μ' {z : ℝ | ε < |z - 1|})
    $ massPowerTilt_massLaw_eq μ ν m hm n hlaw
  rw [Measure.map_apply hm hS, Measure.map_apply hm hS] at he
  exact congrArg ENNReal.toReal he

section ActualMassLaw
𝗇 𝔅 𝗎₁
variable {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
  (d k F m r D q : ℕ) [NeZero k] [LinearOrder 𝙯]
  (σ : Measure Z) [IsFiniteMeasure σ] (a b C δ : ℝ)
  (A : Z → HighFrameIndex d F → 𝖲)
  (hA : 𝙚)
  (hcost : 𝙧)
  (hpos : 0 < 𝔅)
  (hδ : 𝙮₂) (hδ1 : δ ≤ 1)
  (B : 𝙯 → Z → Covariate d → 𝗢)
  (hmB : 𝘲)
  (initial : HighRawState d k F) (hi : Measurable initial.1)
  (T : ℝ) (hT : 𝚞)
  (hsmall : T * (𝔅 / δ) / historyReferenceRho 𝔇 ≤
    1 / (2 + 8 * ((𝔇 : ℕ) : ℝ)^2))

include hA hcost hpos hδ hδ1 hmB hi hT hsmall

variable (ha : 𝙆) (hab : 𝙭) (hr : 𝘗) (hδlt : δ < 1)
  (radius width : ℝ) (hR : 0 < radius) (ha1 : a + radius ≤ 1) (hb1 : 1 + radius ≤ b)
  (hW : 𝘅 ≤ width) (hδW : δ * width ≤ radius / 2)
  (hB : ∀ j ζ x l, |B j ζ x l| ≤ 1) (hinit : 𝗅₂)

include ha hab hr hδlt hR ha1 hb1 hW hδW hB hinit
