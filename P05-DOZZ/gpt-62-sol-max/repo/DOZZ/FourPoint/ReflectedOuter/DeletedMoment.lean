/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedOuter.DeletedDisk
public import DOZZ.FourPoint.ReflectedOuter.InverseDifference
public import DOZZ.Statements.FourPoint.GammaHalfMoment
import Mathlib.Tactic

/-! # The deleted-disk bound for the literal inverse moment -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The inverse moment of the retained zero mass differs from the full zero moment by the
freezing power `κ+δ`, uniformly as the retained radius tends to zero. -/
theorem reflected_retainedZero_deleted_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hreflect : Q γ - α₁ < γ / 2) (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ r : ℝ, 0 < r → r < ε₀ →
      |(∫⁻ ω, (reflectedRetainedZeroMass γ α₁ α₂ α₃ r (M ω)) ^
          (-((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ)) ∂P).toReal -
        gammaHalfMoment P M γ α₁ α₂ α₃
          ((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ) 0| ≤
        C * r ^ (γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2) := by
  let p : ℝ := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ
  let e : ℝ := γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  obtain ⟨Cd, εd, hCd, hεd, hdb⟩ := reflected_deleted_disk_weight_bound
    P X M γ α₁ α₂ α₃ hγ hγ₂ hα₁ hreflect hs hX hM
  refine ⟨p * Cd, min εd 1, mul_pos hp hCd, lt_min hεd zero_lt_one, ?_⟩
  intro r hr hr₀
  obtain ⟨hrd, hr₁⟩ := lt_min_iff.mp hr₀
  exact (retainedZero_deleted_moment_le P X hX γ hγ hγ₂ M hM (-γ / 2) α₁ α₂ α₃ r p
    (Cd * r ^ e) hr₁.le hp (by positivity) (by linarith) hα₂ hα₃ _
    (fun ν h0 h1 => (gammaHalfMass_eq_coulombMass γ α₁ α₂ α₃ 0 ν h0 h0 h1).symm)
    (hdb r hr hrd)).trans_eq (mul_assoc p Cd (r ^ e)).symm

end DOZZ.Proofs
