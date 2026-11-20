module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Fourier
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-! # Variation and support of Fourier projection -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ)
    (q : EvolutionQuery Ω γ) (ξ : PDE.Vec d) (ν : ComplexMeasure (PDE.Vec d))
    (hν : IsFourierProjection K q ξ ν)

include hν in
/-- Variation is dominated by the source velocity marginal. -/
theorem fourierProjection_variation_le :
    ν.variation ≤ K.firstMarginal q := by
  rw [fourierProjection_eq_densityMap K q ξ ν hν]
  calc
    _ ≤ (((K.master q).withDensityᵥ (fourierPhase ξ q.1.2.2.2)).variation).map Prod.fst :=
      VectorMeasure.variation_map_le
    _ = (K.master q).map Prod.fst := by
      rw [Measure.variation_withDensityᵥ (fourierPhase_integrable K q ξ _)]
      have hphase : (fun w => ‖fourierPhase ξ q.1.2.2.2 w‖ₑ) = 1 := by
        funext w
        rw [← ofReal_norm, norm_fourierPhase]
        norm_num
      rw [hphase, withDensity_one]
    _ = K.firstMarginal q := by
      rw [MovingFiberKernel.firstMarginal, ProbabilityTheory.Kernel.fst_apply]

include ν in
/-- Total variation on the whole carrier, before any conversion to real. -/
abbrev totalVariationNorm : ℝ≥0∞ :=
  ν.variation Set.univ

include hν in
/-- The projected measure has total variation at most one. -/
theorem fourierProjection_totalVariation_le_one :
    totalVariationNorm ν ≤ 1 := by
  apply (Measure.le_iff.1 (fourierProjection_variation_le K q ξ ν hν) univ
    MeasurableSet.univ).trans
  rw [MovingFiberKernel.firstMarginal, ProbabilityTheory.Kernel.fst_apply,
    Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
  apply K.mass_le_one

/-- The zero frequency is the positive velocity marginal. -/
theorem fourierProjection_zero
    (hν : IsFourierProjection K q 0 ν) (E : Set (PDE.Vec d))
    (hE : MeasurableSet E) : ν E = ((K.firstMarginal q E).toReal : ℂ) := by
  have hz : fourierPhase 0 q.1.2.2.2 = fun _ => 1 := by
    funext w
    simp [fourierPhase, PDE.vecDot, Complex.ofReal_zero, Complex.exp_zero]
  rw [hν E hE, hz]
  change _ = (((Measure.map Prod.fst (K.master q)) E).toReal : ℂ)
  rw [Measure.map_apply measurable_fst hE]
  have hset : (Prod.fst : EvolutionAmbientState d → PDE.Vec d) ⁻¹' E = E ×ˢ univ := by
    ext w
    simp
  rw [hset]
  simp only [setIntegral_const, measureReal_def, Complex.real_smul, mul_one]

/-- A full zero-mode equality usable for vector-measure rewriting. -/
theorem fourierProjection_zero_measure (hν : IsFourierProjection K q 0 ν) :
    ν = (K.firstMarginal q).withDensityᵥ (fun _ => (1 : ℂ)) := by
  have hm : IsFiniteMeasure (K.firstMarginal q) := by
    change IsFiniteMeasure ((K.master q).map Prod.fst)
    infer_instance
  apply VectorMeasure.ext
  intro E hE
  rw [fourierProjection_zero K q ν hν E hE, withDensityᵥ_apply (integrable_const (1 : ℂ)) hE]
  simp only [setIntegral_const, measureReal_def, Complex.real_smul, mul_one]

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
