module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeakIntegrability
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Finite measures determined by the smooth Duhamel identity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/- Positive test weights vanish outside every set containing their closed support. -/
theorem sourcePositiveMeasure_compl_eq_zero
    (Ψ : ℝ × EvolutionAmbientState d → ℝ) {U }
    (hU : MeasurableSet U) (hs : tsupport Ψ ⊆ U) : sourcePositiveMeasure Ψ Uᶜ = 0 := by
  rw [sourcePositiveMeasure, withDensity_apply _ hU.compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem hU.compl] with q hq
  have hz := image_eq_zero_of_notMem_tsupport (fun h => hq (hs h))
  rw [hz, max_self, ENNReal.ofReal_zero]
  rfl

/- Negating a compact weight preserves its closed support. -/
theorem tsupport_neg_weight (Ψ : ℝ × EvolutionAmbientState d → ℝ) :
    tsupport (fun q => -Ψ q) = tsupport Ψ := by
  apply congrArg closure
  ext q
  change (-Ψ q ≠ 0) ↔ (Ψ q ≠ 0)
  exact neg_ne_zero

/- The two positive source measures in a signed weak identity. -/
def weakSourcePositiveMeasure (K : MovingFiberKernel Ω γ)
    (Λ Ψ : ℝ × EvolutionAmbientState d → ℝ) (a T : ℝ) :
    Measure (ℝ × EvolutionAmbientState d) :=
  boundedSourceActionMeasure K (sourcePositiveStartMeasure Λ) a T + sourcePositiveMeasure Ψ

/- The negative source measure uses the negative weights, without source-value cutoffs. -/
def weakSourceNegativeMeasure (K : MovingFiberKernel Ω γ)
    (Λ Ψ : ℝ × EvolutionAmbientState d → ℝ) (a T : ℝ) :
    Measure (ℝ × EvolutionAmbientState d) :=
  weakSourcePositiveMeasure K (fun q => -Λ q) (fun q => -Ψ q) a T

/- Smooth compact-source identities determine the corresponding finite source measures.
The consumer supplies this identity from the proved smooth Duhamel theorem. -/
end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
