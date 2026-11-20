/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Summing finite weighted sets in geometric shells. -/

@[expose] public section
namespace CCDN
open Finset

/-- A geometric partition with successive shells of at most half the preceding budget. -/
theorem sum_le_of_geometric_shells {α : Type*} (S : Finset α) (h w : α → ℝ)
    {L q C D : ℝ} (hL : 0 < L) (hq : 1 < q) (hC : 0 ≤ C)
    (hbase : ∑ i ∈ S.filter (fun i => h i ≤ L), w i ≤ D)
    (hshell : ∀ n : ℕ,
      ∑ i ∈ S.filter (fun i => L * q ^ n < h i ∧ h i ≤ L * q ^ (n + 1)), w i ≤
        C * (1 / 2 : ℝ) ^ n) :
    ∑ i ∈ S, w i ≤ D + 2 * C := by
  classical
  let T (n : ℕ) := S.filter (fun i => h i ≤ L * q ^ n)
  have hsum (n : ℕ) : ∑ i ∈ T n, w i ≤ D + 2 * C - 2 * C * (1 / 2 : ℝ) ^ n := by
    induction n with
    | zero => simpa [T] using hbase
    | succ n ih =>
      have hsub : T n ⊆ T (n + 1) := fun i hi =>
        mem_filter.mpr ⟨(mem_filter.mp hi).1, (mem_filter.mp hi).2.trans (by gcongr <;> first | exact hq.le | omega)⟩
      have he : T (n + 1) \ T n = S.filter (fun i => L * q ^ n < h i ∧ h i ≤ L * q ^ (n + 1)) := by
        ext i
        by_cases hi : i ∈ S <;> simp [T, hi, and_comm]
      have ht := sum_sdiff hsub (f := w)
      rw [he] at ht
      rw [pow_succ]
      linarith [hshell n]
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((∑ i ∈ S, |h i|) / L) hq
  have hT : T n = S := filter_eq_self.mpr fun i hi =>
    (le_abs_self _).trans ((single_le_sum (fun _ _ => abs_nonneg _) hi).trans
      (by simpa [mul_comm] using ((div_lt_iff₀ hL).mp hn).le))
  rw [← hT]
  exact (hsum n).trans (sub_le_self _ (by positivity))

end CCDN
