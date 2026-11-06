module

public import PottsDiscontinuity.FK.BoxTranslation
public import PottsDiscontinuity.Frozen.Defs.IsTranslationErgodic

@[expose] public section

open MeasureTheory Set

namespace PottsDiscontinuity.RCInfinite
open FK

/-- Translate a bond field by `a`; the new value at `e` is the old value at `e-a`. -/
abbrev edgeTranslate (a : LatticeVertex) : LatticeConfiguration ≃ LatticeConfiguration :=
  latticeConfigurationTranslate a

theorem edgeTranslate_measurable (a : LatticeVertex) : Measurable (edgeTranslate a) :=
  latticeConfigurationTranslate_measurable a

@[simp] theorem edgeTranslate_zero (ω : LatticeConfiguration) : edgeTranslate 0 ω = ω := by
  funext e
  have hz : latticeTranslate (0 : LatticeVertex) = id := funext latticeTranslate_zero
  simp [edgeTranslate, latticeConfigurationTranslate_apply, latticeTranslationIso,
    SimpleGraph.Iso.mapEdgeSet, SimpleGraph.Hom.mapEdgeSet, hz]

/-- Translation invariance and the null-or-conull property for measurable
strictly invariant events of the original bond configuration. -/
def IsEdgeTranslationErgodic (μ : Measure LatticeConfiguration) : Prop :=
  (∀ a : LatticeVertex, μ.map (edgeTranslate a) = μ) ∧
    ∀ A : Set LatticeConfiguration, MeasurableSet A →
      (∀ a : LatticeVertex, (edgeTranslate a) ⁻¹' A = A) → μ A = 0 ∨ μ Aᶜ = 0

theorem IsEdgeTranslationErgodic.zero_one {μ : Measure LatticeConfiguration}
    [IsProbabilityMeasure μ] (hμ : IsEdgeTranslationErgodic μ)
    {A : Set LatticeConfiguration} (hA : MeasurableSet A)
    (hinv : ∀ a : LatticeVertex, (edgeTranslate a) ⁻¹' A = A) :
    μ A = 0 ∨ μ A = 1 := by
  rcases hμ.2 A hA hinv with h | h
  · exact Or.inl h
  · right
    have hadd := measure_add_measure_compl (μ := μ) hA
    simpa [h] using hadd

end PottsDiscontinuity.RCInfinite
