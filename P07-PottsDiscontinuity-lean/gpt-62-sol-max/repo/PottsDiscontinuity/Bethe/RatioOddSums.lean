module

public import PottsDiscontinuity.Bethe.AsymptoticSumSplit
public import PottsDiscontinuity.Bethe.RatioProducts
public import PottsDiscontinuity.Bethe.RatioProfile

/-! # Finite reflection and telescoping identities for the odd quotient -/

@[expose] public section

open Finset
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem ratio_ell_neg (c x : ℝ) : ratioEll c (-x) = ratioEll c x := by
  unfold ratioEll
  simp [ratio_M_neg]

theorem ratio_ell_zero (c : ℝ) : ratioEll c 0 = 0 := by
  simp [ratioEll, BetheAnsatz.M]

theorem ratio_sum_reflection {m h d : ℕ} (hcount : h + d + h = m)
    (f : Fin m → ℝ) (hsym : ∀ j, f (Fin.rev j) = f j)
    (hc : (∑ j : Fin d, f ⟨h + j.val, by omega⟩) = 0) :
    (∑ j, f j) = 2 * ∑ j : Fin h, f ⟨h + d + j.val, by omega⟩ := by
  have he := sum_fin_reflect_block (a := 0) (k := h) (b := h + d) (by omega) f hsym
  simp only [zero_add] at he
  rw [sum_fin_split_block hcount, hc, he, add_zero, two_mul]

theorem odd_middle_root_zero {n t : ℕ} (hn : n = 2 * t + 1)
    (q : Fin n → ℝ) (hq : ∀ j, q (Fin.rev j) = -q j) : q ⟨t, by omega⟩ = 0 := by
  grind

/-- The edge logarithms telescope, leaving the first root, the last retained
root, and the s discarded positive boundary roots. -/
theorem ratio_midpoint_sum_telescoping {m t s : ℕ} (hcount : t + 1 + s = m)
    (f : Fin m → ℝ) (g : Fin t → ℝ) :
    2 * (∑ j, g j) - 2 * (∑ j, f j) =
      (∑ j : Fin t, (2 * g j - f ⟨j.val, by omega⟩ - f ⟨j.val + 1, by omega⟩)) -
        f ⟨0, by omega⟩ - f ⟨t, by omega⟩ -
          2 * ∑ j : Fin s, f ⟨t + 1 + j.val, by omega⟩ := by
  let F : Fin (t + 1) → ℝ := fun j => f ⟨j.val, by omega⟩
  have h₀ := Fin.sum_univ_succ F
  have h₁ := Fin.sum_univ_castSucc F
  have hs := sum_fin_split_block (m := m) (a := t + 1) (n := s) (b := 0) (by omega) f
  simp only [Fin.sum_univ_zero, add_zero] at hs
  change (∑ j, f j) = (∑ j : Fin (t + 1), F j) + ∑ j : Fin s, f ⟨t + 1 + j.val, by omega⟩ at hs
  change (∑ j : Fin (t + 1), F j) = f ⟨0, by omega⟩ + ∑ j : Fin t, f ⟨j.val + 1, by omega⟩ at h₀
  change (∑ j : Fin (t + 1), F j) = (∑ j : Fin t, f ⟨j.val, by omega⟩) + f ⟨t, by omega⟩ at h₁
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum]
  linarith only [h₀, h₁, hs]

end PottsDiscontinuity.Bethe
