/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergMoment
public import DOZZ.GMC.Moments.RhoCoulomb
import Mathlib.Tactic

/-! # Finiteness of the supplied limiting Coulomb mass

A small positive moment exists when every finite and infinite charge is below
`Q`. No total-charge condition is needed for almost-sure mass finiteness.
-/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The literal rho mass is almost surely finite whenever its three charges are below `Q`. -/
theorem reflected_rho_ae_finite {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    ∀ᵐ ω ∂P, rho γ (M ω) α₁ α₂ α₃ < ⊤ := by
  have hz : Function.Injective (![0, 1] : Fin 2 → ℂ) :=
    Matrix.injective_pair_iff_ne.mpr zero_ne_one
  have hcharges : ∀ k : Fin 2, (![α₁, α₂] : Fin 2 → ℝ) k < Q γ := by
    intro k
    fin_cases k
    · exact hα₁
    · exact hα₂
  filter_upwards [coulombMass_ae_lt_top P X hX γ hγ hγ₂ M hM
    ![0, 1] hz ![α₁, α₂] α₃ hcharges hα₃,
    gmc_rho_eq_coulombMass_ae P X hX γ hγ hγ₂ M hM α₁ α₂ α₃] with ω hf he
  rw [he]
  exact hf

end DOZZ.Proofs
