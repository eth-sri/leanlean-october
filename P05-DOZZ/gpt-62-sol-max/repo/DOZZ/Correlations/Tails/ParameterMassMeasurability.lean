/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.SingularMassMeasurability

/-! Jointly measurable random weights against actual GMC versions. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

section
variable {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V] (P : Measure Ω) (X : Ω → Distr)
  (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
  (θ : Ω → V) (hθ : AEMeasurable θ P)
include Ω X hX γ hγ hγ2 hM hθ

/-- Random parameters may depend on the field. Extended-real integrals need no
integrability assumption, including at an insertion singularity. -/
theorem gmc_parameter_lintegral_aemeasurable
    (F : V × ℂ → ℝ≥0∞) (hF : Measurable F) :
    AEMeasurable (fun ω => ∫⁻ x, F (θ ω, x) ∂M ω) P :=
  (measurable_lintegral_finiteMeasure_parameter hF).comp_aemeasurable
    (hθ.prodMk (equatorGFF_finiteGMC_aemeasurable P X hX γ hγ hγ2 M hM))

/-- The signed integral of a random test is measurable on the
actual GMC version, even when its parameter is correlated with the field. -/
theorem gmc_parameter_integral_aemeasurable
    (F : V × ℂ → ℝ) (hF : Measurable F) :
    AEMeasurable (fun ω => ∫ x, F (θ ω,x) ∂M ω) P :=
  (measurable_integral_finiteMeasure_parameter hF).comp_aemeasurable
    (hθ.prodMk (equatorGFF_finiteGMC_aemeasurable P X hX γ hγ hγ2 M hM))

end

end DOZZ.Proofs
