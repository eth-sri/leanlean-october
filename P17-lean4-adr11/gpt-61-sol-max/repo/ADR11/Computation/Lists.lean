module
public import ADR11.Computation.Codes
@[expose] public section
namespace ADR11.Computation.Lists
open Finset
instance {α : Type*} [DecidableEq α] (F : Family α) : Decidable (IsForest F) := by
  unfold IsForest; infer_instance
variable {L : Type*} [Fintype L] [DecidableEq L]
def jumpL : ℕ → Family L → Multiset (ℚ × Family L)
  | 0, F => {(1, F)}
  | j + 1, F => if #(roots F) ≤ 1 then {(1, F)} else
      (merges F).val.bind fun H => (jumpL j H).map fun q =>
        (((#(roots F)).choose 2 : ℚ)⁻¹ * q.1, q.2)
theorem jump_spec : ∀ (j : ℕ) (F : Family L), IsForest F → ∀ G,
    (jumpMatrix ^ j) F G =
      ((jumpL j F).map fun q => if q.2 = G then (q.1 : ℝ) else 0).sum
  | 0, F, _, G => by simp [jumpL, Matrix.one_apply, eq_comm]
  | j + 1, F, hF, G => by
    by_cases hk : #(roots F) ≤ 1
    · rw [jumpMatrix_pow_of_card_roots_le_one hk]
      simp [jumpL, hk, eq_comm]
    · rw [jumpMatrix_pow_succ_apply (by omega)]
      rw [jumpL, ite_eq_right hk, Multiset.map_bind, Multiset.sum_bind]
      change _ = ∑ H ∈ merges F, _
      rw [mul_sum]
      apply sum_congr rfl
      intro H hH
      rw [jump_spec j H (hF.of_mem_merges hH).1 G, Multiset.map_map]
      simp_rw [← Multiset.sum_map_mul_left]
      congr! 2
      simp only [Function.comp_apply]
      split_ifs <;> push_cast <;> ring
end ADR11.Computation.Lists
