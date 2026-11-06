module

public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Basic.Complex.Basic

/-!
Exact scalar ingredients of the compact Glennie estimate. The native Albert
adapter is a separate obligation: these results make no spectral or pair
reduction assumption and do not state the universal Glennie endpoint.
-/

public section

namespace Glennie.ScalarEstimates

/-- The trace-zero cubic discriminant, with the actual unscaled trace metric. -/
theorem discriminant_identity (a b c : ℝ) (htrace : a + b + c = 0) :
    ((a - b) * (a - c) * (b - c)) ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2) ^ 3 / 2 - 27 * (a * b * c) ^ 2 := by grind

theorem amgm_min (a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hac : a ≤ c) :
    27 * (a * b * c) ≤ (a + b + c) ^ 3 := by
  have hu : 0 ≤ b - a := by linarith
  have hv : 0 ≤ c - a := by linarith
  have hq : 0 ≤ (b - a) ^ 2 - (b - a) * (c - a) + (c - a) ^ 2 := by nlinarith
  have hm := mul_nonneg ha hq
  have hp := pow_nonneg (add_nonneg hu hv) 3
  have hid : (a + b + c) ^ 3 - 27 * (a * b * c) =
      ((b - a) + (c - a)) ^ 3 +
        9 * a * ((b - a) ^ 2 - (b - a) * (c - a) + (c - a) ^ 2) := by ring
  linarith

/-- AM–GM in a polynomial form, including zero arguments. -/
theorem amgm_three (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27 * (a * b * c) ≤ (a + b + c) ^ 3 := by
  rcases le_total a b with hab | hba
  · rcases le_total a c with hac | hca
    · exact amgm_min a b c ha hab hac
    · have h := amgm_min c a b hc hca (hca.trans hab)
      nlinarith
  · rcases le_total b c with hbc | hcb
    · have h := amgm_min b a c hb hba hbc
      nlinarith
    · have h := amgm_min c a b hc (hcb.trans hba) hcb
      nlinarith

theorem amgm_min_eq (a b c : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hac : a ≤ c)
    (heq : 27 * (a * b * c) = (a + b + c) ^ 3) : a = b ∧ b = c := by
  have hu : 0 ≤ b - a := by linarith
  have hv : 0 ≤ c - a := by linarith
  have hq : 0 ≤ (b - a) ^ 2 - (b - a) * (c - a) + (c - a) ^ 2 := by nlinarith
  have hm := mul_nonneg ha hq
  have hid : (a + b + c) ^ 3 - 27 * (a * b * c) =
      ((b - a) + (c - a)) ^ 3 +
        9 * a * ((b - a) ^ 2 - (b - a) * (c - a) + (c - a) ^ 2) := by ring
  have hle : ((b - a) + (c - a)) ^ 3 ≤ 0 := by linarith
  have hs : (b - a) + (c - a) ≤ 0 := by
    by_contra h
    have hp := pow_pos (lt_of_not_ge h) 3
    linarith
  constructor <;> linarith

theorem amgm_three_eq_iff (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27 * (a * b * c) = (a + b + c) ^ 3 ↔ a = b ∧ b = c := by
  constructor
  · intro heq
    rcases le_total a b with hab | hba
    · rcases le_total a c with hac | hca
      · exact amgm_min_eq a b c ha hab hac heq
      · have h' : 27 * (c * a * b) = (c + a + b) ^ 3 := by nlinarith
        obtain ⟨h1, h2⟩ := amgm_min_eq c a b hc hca (hca.trans hab) h'
        constructor <;> linarith
    · rcases le_total b c with hbc | hcb
      · have h' : 27 * (b * a * c) = (b + a + c) ^ 3 := by nlinarith
        obtain ⟨h1, h2⟩ := amgm_min_eq b a c hb hba hbc h'
        constructor <;> linarith
      · have h' : 27 * (c * a * b) = (c + a + b) ^ 3 := by nlinarith
        obtain ⟨h1, h2⟩ := amgm_min_eq c a b hc (hcb.trans hba) hcb h'
        constructor <;> linarith
  · grind

end Glennie.ScalarEstimates
