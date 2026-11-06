module

public import NearlyMinimax.HighHistoryMassConcentration
public import NearlyMinimax.HistoryInvariantLaw
public import NearlyMinimax.HistoryPatchStateAppend
public import NearlyMinimax.HighMassAnnihilation

@[expose] public section

/-!
# The actual balanced-packet invariant mass law

The source dependency relation is the genuine torus-neighbor relation.
-/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem highNeighbor_dependency_card (d k : ℕ) [NeZero k] (j : HighWindowLabels d k) :
    (dependentLabelFinset (fun i j => j ∈ highNeighborLabels d k i) j).card ≤ 3^d := by
  classical
  have he : dependentLabelFinset (fun i j => j ∈ highNeighborLabels d k i) j =
      highNeighborLabels d k j := by
    ext i
    simp [dependentLabelFinset]
  rw [he]
  exact highNeighborLabels_card_le d k j

/-- The true tilted exceptional mass probability is determined by the genuine mass law. -/
theorem massPowerTilt_abs_event_eq_of_massLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (m : Ω → ℝ) (hm : Measurable m) (n : ℕ)
    (hlaw : μ.map m = ν.map m) (ε : ℝ) :
    (massPowerTilt μ m n).real {ω | ε < |m ω - 1|} =
      (massPowerTilt ν m n).real {ω | ε < |m ω - 1|} := by
  have hS : MeasurableSet {z : ℝ | ε < |z - 1|} :=
    measurableSet_lt measurable_const ((measurable_id.sub measurable_const).abs)
  have he := congrArg (fun μ' : Measure ℝ => μ' {z : ℝ | ε < |z - 1|})
    (massPowerTilt_massLaw_eq μ ν m hm n hlaw)
  rw [Measure.map_apply hm hS, Measure.map_apply hm hS] at he
  exact congrArg ENNReal.toReal he

section ActualMassLaw
variable {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
  (d k F m r D q : ℕ) [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (σ : Measure Z) [IsFiniteMeasure σ] (a b C δ : ℝ)
  (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
  (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
  (hcost : Integrable (separatedMatrixCost A) σ)
  (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
  (hδ : 0 < δ) (hδ1 : δ ≤ 1)
  (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
  (hmB : ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l))
  (initial : HighRawState d k F) (hi : Measurable initial.1)
  (T : ℝ) (hT : 0 ≤ T)
  (hsmall : T * (highPacketMarkMass σ a b m r D q C A / δ) / historyReferenceRho (3^d) ≤
    1 / (2 + 8 * ((3^d : ℕ) : ℝ)^2))

include hA hcost hpos hδ hδ1 hmB hi hT hsmall

variable (ha : 0 < a) (hab : a < b) (hr : 1 ≤ r) (hδlt : δ < 1)
  (radius width : ℝ) (hR : 0 < radius) (ha1 : a + radius ≤ 1) (hb1 : 1 + radius ≤ b)
  (hW : b - a ≤ width) (hδW : δ * width ≤ radius / 2)
  (hB : ∀ j ζ x l, |B j ζ x l| ≤ 1) (hinit : ∀ x, initial.1 x = 1)

include ha hab hr hδlt hR ha1 hb1 hW hδW hB hinit

end ActualMassLaw

end NearlyMinimax
