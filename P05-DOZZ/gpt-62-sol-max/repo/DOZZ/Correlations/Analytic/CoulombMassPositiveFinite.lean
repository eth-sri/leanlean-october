/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergMoment

/-! Almost sure positivity and finiteness needed for varying real exponents. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Subcritical individual charges give a positive finite Coulomb mass almost surely, independently
of the sign of the Seiberg exponent. -/
theorem coulomb_mass_pos_finite_ae
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : Fin N → ℂ) (hz : Function.Injective z) (α : Fin N → ℝ) (αinf : ℝ)
    (ha : ∀ k, α k < Q γ) (hi : αinf < Q γ) :
    ∀ᵐ ω ∂P, coulombMass γ (M ω) α z αinf ≠ 0 ∧
      coulombMass γ (M ω) α z αinf ≠ ⊤ := by
  filter_upwards [coulombMass_ae_pos P X hX γ hγ hγ2 M hM α z αinf,
    coulombMass_ae_lt_top P X hX γ hγ hγ2 M hM z hz α αinf ha hi] with ω hp hf
  exact ⟨hp.ne', hf.ne⟩

end DOZZ.Proofs
