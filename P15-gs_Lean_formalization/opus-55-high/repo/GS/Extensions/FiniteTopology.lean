module

public import GS.OriginalLocalModel

@[expose] public section


/-!
# Finite-dimensional topology used by the original fibre proof

The argument uses coordinatewise compact intervals, not an identification of
mathlib's default matrix norm with the Frobenius norm.
-/

noncomputable section
namespace GS.Extensions

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem continuous_frobSq : Continuous (@frobSq ι κ _ _) := by
  unfold frobSq frobInner
  fun_prop

theorem abs_entry_le_of_frobSq_le {A : Matrix ι κ ℝ} {η : ℝ}
    (h : frobSq A ≤ η^2) (i : ι) (j : κ) : |A i j| ≤ |η| := by
  refine sq_le_sq.1 (le_trans ?_ h)
  exact pow_two (A i j) ▸ (Finset.single_le_sum (f := fun l => A i l * A i l) (fun l _ => mul_self_nonneg _)
    (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun r => ∑ l, A r l * A r l)
    (fun r _ => Finset.sum_nonneg fun l _ => mul_self_nonneg _) (Finset.mem_univ i))

theorem isClosed_supported (n : ℕ) (block : Fin n → ℕ) :
    IsClosed {A : Mat n | Supported block A} := by
  simp only [Supported, Set.setOf_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (by fun_prop) continuous_const

section
variable (q : ℕ) (η : ℝ)
theorem isCompact_originalK : IsCompact (originalK q η) := by
  let ρ := |η| + 1
  refine (isCompact_Icc (a :=
    (fun _ => -ρ, fun _ => -ρ, fun _ _ => -ρ, fun _ _ => -ρ, fun _ => -ρ)) (b :=
    (fun _ => ρ, fun _ => ρ, fun _ _ => ρ, fun _ _ => ρ, fun _ => ρ))).of_isClosed_subset ?_ ?_
  · simp only [originalK, IsSkew, OnCircle, frobSq, frobInner, Set.setOf_and, Set.setOf_forall]
    repeat' first | apply IsClosed.inter | apply isClosed_iInter; intro
    all_goals first | exact isClosed_le (by fun_prop) (by fun_prop) | exact isClosed_eq (by fun_prop) (by fun_prop)
  rintro ⟨ell, r, c, z, u⟩ ⟨hell, hr, -, -, -, hcn, hzn, hu⟩
  have hu' : u 0 ^ 2 + u 1 ^ 2 = 1 := hu
  simp
  have h4 i j := abs_le.1 (abs_entry_le_of_frobSq_le hcn i j)
  have h5 i j := abs_le.1 (abs_entry_le_of_frobSq_le hzn i j)
  and_intros <;> intro i <;> try intro j
  all_goals first | grind | fin_cases i <;> simp <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), abs_nonneg η]

end

end GS.Extensions
