module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierBounds

/-!
# Ellipticity normalization of the case-W decay

The source change of variables `σ̂ = λ^(1/3) σ`, `v̂ = λ^(-1/3) v`, `ẑ = z`.  This is not the
kinetic `r², r, r³` scaling.  This file proves the pointwise identities used by that
reduction: the normalized diffusion `B̂` has bounds `[1, κ]` when `B` has bounds `[λ, κλ]`,
the identity transport is unchanged, the frequency and the transported coordinate are
unchanged, and total variation is invariant under the velocity pushforward.  The identification
of the rescaled kernel by terminal-problem uniqueness is not part of this file.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

open MeasureTheory Set
open scoped ENNReal MatrixOrder








/-- Pushforward of a complex measure by a measurable equivalence preserves total variation. -/
theorem variation_map_equiv_univ {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (ν : ComplexMeasure α) :
    (ν.map e).variation univ = ν.variation univ := by
  rw [e.measurableEmbedding.variation_map, Measure.map_apply e.measurable MeasurableSet.univ,
    preimage_univ]

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
