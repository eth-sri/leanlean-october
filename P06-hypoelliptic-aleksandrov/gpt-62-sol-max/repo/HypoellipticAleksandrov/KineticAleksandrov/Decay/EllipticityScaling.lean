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

/-- The cube root `λ^(1/3)` of the ellipticity scale. -/
def lamCbrt (lam : ℝ) : ℝ := lam ^ (1 / 3 : ℝ)

theorem lamCbrt_pos {lam : ℝ} (hlam : 0 < lam) : 0 < lamCbrt lam :=
  Real.rpow_pos_of_pos hlam _

/-- The velocity part of the pushforward, `v ↦ λ^(-1/3) v`, as a measurable equivalence. -/
def lamVelocityEquiv (d : ℕ) {lam : ℝ} (hlam : 0 < lam) : PDE.Vec d ≃ᵐ PDE.Vec d :=
  (Homeomorph.smulOfNeZero (lamCbrt lam)⁻¹ (inv_ne_zero (lamCbrt_pos hlam).ne')).toMeasurableEquiv

@[simp] theorem lamVelocityEquiv_apply (d : ℕ) {lam : ℝ} (hlam : 0 < lam) (v : PDE.Vec d) :
    lamVelocityEquiv d hlam v = (lamCbrt lam)⁻¹ • v :=
  rfl

/-- The ambient pushforward map: velocity scaled, transported coordinate unchanged. -/
def lamAmbientEquiv (d : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    EvolutionAmbientState d ≃ᵐ EvolutionAmbientState d :=
  (lamVelocityEquiv d hlam).prodCongr (MeasurableEquiv.refl _)

@[simp] theorem lamAmbientEquiv_apply (d : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (w : EvolutionAmbientState d) :
    lamAmbientEquiv d hlam w = ((lamCbrt lam)⁻¹ • w.1, w.2) :=
  rfl

/-- Pushforward of a complex measure by a measurable equivalence preserves total variation. -/
theorem variation_map_equiv_univ {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (ν : ComplexMeasure α) :
    (ν.map e).variation univ = ν.variation univ := by
  rw [e.measurableEmbedding.variation_map, Measure.map_apply e.measurable MeasurableSet.univ,
    preimage_univ]

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
