/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.RetainedZeroDeletedWeight
public import DOZZ.FourPoint.Dual.OuterMassLimit
public import DOZZ.FourPoint.ReflectedOuter.InverseDifference
import Mathlib.Tactic
/-! # The actual deleted-disk inverse-expectation error -/
public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The retained zero inverse expectation differs from the full zero inverse expectation
by at most the deleted-disk radial power. -/
theorem dual_retainedZero_deleted_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hp : 0 < p)
    (hα₁ : α₁ - 2 / γ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hβ : γ * α₁ < 4) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      |(∫⁻ ω, dualRetainedZeroMass γ α₁ α₂ α₃ r (M ω) ^ (-p) ∂P).toReal -
        (∫⁻ ω, coulombMass γ (M ω) ![-2 / γ, α₁, α₂] ![0, 0, 1] α₃ ^ (-p) ∂P).toReal| ≤
          C * r ^ (4 - γ * α₁) := by
  let e : ℝ := 4 - γ * α₁
  obtain ⟨Cd, hCd, hdb⟩ := dual_retainedZero_deleted_weight_bound
    P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ (p + 1) (by linarith only [hp]) hβ
  refine ⟨p * Cd, mul_pos hp hCd, ?_⟩
  intro r hr hr₀
  exact (retainedZero_deleted_moment_le P X hX γ hγ hγ₂ M hM (-2 / γ) α₁ α₂ α₃ r p
    (Cd * r ^ e) (by linarith) hp (by positivity)
    (by simpa [sub_eq_add_neg, neg_div] using hα₁) hα₂ hα₃ _
    (fun ν h0 h1 => (dual_kernel_integral_eq_coulombMass γ α₁ α₂ α₃ hγ.ne' 0 ν h0 h0 h1).symm)
    (hdb r hr hr₀)).trans_eq (mul_assoc p Cd (r ^ e)).symm

end DOZZ.Proofs
