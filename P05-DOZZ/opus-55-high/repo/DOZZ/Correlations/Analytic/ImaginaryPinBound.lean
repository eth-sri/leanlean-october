/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.VertexVarianceBound

/-! The imaginary equator pin is a bounded quadratic form. -/

@[expose] public section
namespace DOZZ.Proofs
section
variable {N : ℕ}

/-- The imaginary zero-mode power has the exact total-charge scaling. -/
theorem complexMomentPower_im_scaled (γ : ℝ) (hγ : γ ≠ 0)
    (β : Fin N → ℂ) :
    γ * (complexMomentPower γ β).im = -∑ i, (β i).im := by
  unfold complexMomentPower
  simp_all

/-- A bounded pin vector gives a quadratic bound in all imaginary charges, including the
outward vertex. -/
theorem imaginary_pin_le (b : Fin (N + 1) → ℝ) (A : Fin N → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hA : ∀ i, |A i| ≤ B) :
    -(∑ i, b i) * (∑ i, b i.castSucc * A i) ≤
      B * (N + 1 : ℕ) * ∑ i, b i ^ 2 := by
  classical
  let S := ∑ i, |b i|
  have hS : 0 ≤ S := by positivity
  have hsum : |∑ i, b i| ≤ S := Finset.abs_sum_le_sum_abs ..
  have hsub : ∑ i : Fin N, |b i.castSucc| ≤ S := by
    dsimp only [S]
    rw [Fin.sum_univ_castSucc]
    simp
  have hpin : |∑ i, b i.castSucc * A i| ≤ S * B := by
    calc
      _ ≤ ∑ i, |b i.castSucc * A i| := Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ i, |b i.castSucc| * B := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul]
        bound)
      _ = (∑ i : Fin N, |b i.castSucc|) * B := (Finset.sum_mul ..).symm
      _ ≤ S * B := mul_le_mul_of_nonneg_right hsub hB
  have hsq : S ^ 2 ≤ (N + 1 : ℕ) * ∑ i, b i ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |b i|))
  calc
    _ ≤ |-(∑ i, b i) * (∑ i, b i.castSucc * A i)| := le_abs_self _
    _ = |∑ i, b i| * |∑ i, b i.castSucc * A i| := by simp
    _ ≤ S * (S * B) := mul_le_mul hsum hpin (abs_nonneg _) hS
    _ = B * S ^ 2 := by ring
    _ ≤ B * ((N + 1 : ℕ) * ∑ i, b i ^ 2) := mul_le_mul_of_nonneg_left hsq hB
    _ = _ := by ring

end

end DOZZ.Proofs
