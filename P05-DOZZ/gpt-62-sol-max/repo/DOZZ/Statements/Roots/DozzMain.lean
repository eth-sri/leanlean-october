/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
import DOZZ.ShiftEquations.Residual.Assembly
import DOZZ.Roots.FormulaGammaContinuity
import DOZZ.Roots.GammaDensity
import DOZZ.Roots.ParameterFamilies



public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

open Proofs

/-- **DOZZ formula** ([KRV, Theorem 2.4]). -/
theorem dozz_main (γ μ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (α₁ α₂ α₃ : ℝ) (hα : ExtendedSeiberg3 γ α₁ α₂ α₃)
    (hs : ∀ n : ℕ, sExp γ α₁ α₂ α₃ ≠ -(n : ℝ))
    (U : ℂ → ℂ) (hU : IsUpsilon γ U)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    (structureConstant P M γ μ α₁ α₂ α₃ : ℂ) = dozzFormula γ μ U α₁ α₂ α₃ := by
  obtain ⟨N, hNγ, hN⟩ := roots_GMC_family_through P X hX γ M hM
  obtain ⟨V, hVγ, hV⟩ := roots_Upsilon_family_through γ U hU
  have hC : ContinuousAt (fun g => (structureConstant P (N g) g μ α₁ α₂ α₃ : ℂ)) γ :=
    Complex.continuous_ofReal.continuousAt.comp
      (roots_structureConstant_gamma_continuousAt P X N hX hN γ μ α₁ α₂ α₃ hγ hγ2 hμ hα hs)
  have hD := roots_dozzFormula_gamma_continuousAt V hV γ μ α₁ α₂ α₃ hγ hγ2 hμ hα hs
  have heq : ∃ᶠ g : ℝ in nhds γ,
      (structureConstant P (N g) g μ α₁ α₂ α₃ : ℂ) = dozzFormula g μ (V g) α₁ α₂ α₃ := by
    have hfreq := (roots_frequently_irrational_sq γ hγ).and_eventually
      ((roots_extended_parameters_nhds hγ hγ2 hα).and (roots_poleFree_gamma_nhds γ α₁ α₂ α₃ hγ.ne' hs))
    apply hfreq.mono
    rintro g ⟨hgirr, ⟨hg, hg2, hgα⟩, hgs⟩
    exact dozz_main_irrational P X (N g) g μ hg hg2 hgirr hμ (V g) (hV g ⟨hg, hg2⟩)
      hX (hN g hg hg2) α₁ α₂ α₃ hgα hgs
  have he := tendsto_nhds_unique_of_frequently_eq hC.tendsto hD.tendsto heq
  simpa only [hNγ, hVγ] using he

end DOZZ
