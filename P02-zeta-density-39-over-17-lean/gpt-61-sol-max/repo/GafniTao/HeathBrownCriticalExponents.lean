module
import Mathlib
public import GafniTao.HeathBrownLemmaOneCore

@[expose] public section

/-!
# Exact critical exponents in Heath-Brown's Lemma 1

The source critical moment is `s = k(k-1)/2`.  This file records, over the
reals, the identities that turn the normalized Lemma 1 bound into the three
monomials displayed in Heath-Brown's proof.  Keeping these as named lemmas
prevents any later exponent simplification from being hidden in `ring_nf`.
-/

namespace GafniTao

noncomputable section

/-- The reciprocal exponent `1/(k(k-1))` in Heath-Brown Theorem 1. -/
def heathBrownCriticalReciprocal (k : ℕ) : ℝ :=
  1 / ((k : ℝ) * ((k : ℝ) - 1))

theorem heathBrownCriticalMoment_cast
    {k : ℕ} (hk : 1 ≤ k) :
    (heathBrownCriticalMoment k : ℝ) =
      (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  unfold heathBrownCriticalMoment
  rw [Nat.cast_div
    (even_iff_two_dvd.mp (Nat.even_mul_pred_self k))
    (by norm_num : (2 : ℝ) ≠ 0)]
  simp_all

section
variable {k : ℕ} (hk : 2 ≤ k)
include k hk

theorem heathBrownCriticalMoment_pos
     :
    (0 : ℝ) < heathBrownCriticalMoment k := by
  rw [heathBrownCriticalMoment_cast (by omega : 1 ≤ k)]
  have hkReal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

theorem heathBrownCriticalReciprocal_pos
     :
    0 < heathBrownCriticalReciprocal k := by
  unfold heathBrownCriticalReciprocal
  have hkReal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkmOne : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  positivity

theorem heathBrownCriticalReciprocal_le_half
     :
    heathBrownCriticalReciprocal k ≤ 1 / 2 := by
  unfold heathBrownCriticalReciprocal
  have hkReal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : (2 : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) := by
    nlinarith
  exact one_div_le_one_div_of_le (by norm_num) hden

theorem heathBrown_two_mul_criticalMoment
     :
    2 * (heathBrownCriticalMoment k : ℝ) =
      (k : ℝ) * ((k : ℝ) - 1) := by
  rw [heathBrownCriticalMoment_cast (by omega : 1 ≤ k)]
  ring

theorem heathBrown_half_critical_eq_reciprocal
     :
    1 / (2 * (heathBrownCriticalMoment k : ℝ)) =
      heathBrownCriticalReciprocal k := by
  rw [heathBrown_two_mul_criticalMoment hk]
  rfl

theorem heathBrown_inverse_critical_eq_two_reciprocal
     :
    1 / (heathBrownCriticalMoment k : ℝ) =
      2 * heathBrownCriticalReciprocal k := by
  rw [heathBrownCriticalMoment_cast (by omega : 1 ≤ k)]
  unfold heathBrownCriticalReciprocal
  field_simp

theorem heathBrown_critical_core_exponent
     :
    1 - 1 / (heathBrownCriticalMoment k : ℝ) =
      1 - 2 * heathBrownCriticalReciprocal k := by
  rw [heathBrown_inverse_critical_eq_two_reciprocal hk]
end






