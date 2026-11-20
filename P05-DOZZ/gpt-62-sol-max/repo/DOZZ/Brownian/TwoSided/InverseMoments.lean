/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Reflection.Moments

/-! Initial-block inverse bounds with a common radial constant for all subcritical charges. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The initial positive unit block is retained in the full two-sided mass, including its
endpoint convention. -/
theorem twosided_initial_block_le_mass {Ω : Type*} (γ : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (ω : Ω) :
    initialUnitBlockMass γ (B ω).1 (Z ω) ≤ twoSidedReflectionMass γ B Z ω := by
  unfold initialUnitBlockMass twoSidedReflectionMass
  apply lintegral_mono
  intro t
  by_cases ht : 0 ≤ t ∧ t ≤ 1
  · simp only [ht, dite_true, twoSidedConditionedValue]
    rfl
  · simp only [ht, dite_false, ENNReal.ofReal_zero]
    exact zero_le

/-- A bounded drift range and one uniform lateral inverse moment give a uniform inverse
moment of the full mass. Its radial factor uses only the first half-path. -/
theorem twosided_inverse_moment_uniform_from_lateral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Kγ Kν : Set ℝ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : ℝ → Ω → Measure ℝ)
    (hData : ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      IsTwoSidedConditionedBrownianProcess P (B ν) ν ∧
        IsLateralGMCOf P γ (Z γ) ∧ IndepFun (B ν) (Z γ) P)
    (p N : ℝ) (hp : p < 0) (hνN : ∀ ν ∈ Kν, ν ≤ N)
    (L : ℝ≥0∞) (hL : L < ⊤)
    (hUnit : ∀ γ ∈ Kγ, (∫⁻ ω, (Z γ ω (Ioc 0 1)) ^ p ∂P) ≤ L) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) (Z γ) ω) p ∂P) ≤ C := by
  obtain ⟨C, hC, hInv⟩ := initialUnitBlockMass_inverse_moment_le P 2 N (-p) (by norm_num) (neg_pos.mpr hp)
  refine ⟨C * L, ENNReal.mul_lt_top hC hL, ?_⟩
  intro γ hγ ν hν
  obtain ⟨hB, hZ, hi⟩ := hData γ hγ ν hν
  have h := hInv γ hZ.1.le hZ.2.1.le (Z γ) hZ.2.2.2.1
    (hZ.2.2.2.2.1.mono fun _ h => h 0 1) ν (hνN ν hν) _ hB.1 (hi.comp measurable_fst measurable_id)
  rw [neg_neg, lateralGMC_Icc_moment_eq_Ioc P γ (Z γ) hZ 0 1 p (by norm_num)] at h
  exact (lintegral_mono fun ω => ennreal_rpow_antitone_nonpos _ _ p
    (twosided_initial_block_le_mass γ (B ν) (Z γ) ω) hp.le).trans
      (h.trans (mul_le_mul' le_rfl (hUnit γ hγ)))

end DOZZ.Proofs
