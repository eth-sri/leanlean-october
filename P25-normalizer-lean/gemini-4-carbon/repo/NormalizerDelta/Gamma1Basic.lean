module

public import NormalizerDelta.GammaIso

@[expose] public section

/-!
# §K, easy part: Γ₀(N) and the w_Q normalize ±Γ₁(N); the case Q = 1; the exception N = 4

* ι_Q fixes ±1, so every w_Q normalizes Γ_{±1}(N) (`al_mem_normG_iff`).
* (ℤ/4)ˣ = {±1}, so ±Γ₁(4) = Γ₀(4), whose normalizer contains S₂ (h(4) = 2); S₂ is not an
  Atkin–Lehner element (its (0,0) entry would be √Q·x = 1, forcing Q = 1, and then y = 1/2).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

theorem isAtkinLehner_one_iff' (N : ℕ) (g : SL(2, ℝ)) : IsAtkinLehner N 1 g ↔ g ∈ Gamma0R N := by
  constructor
  · rintro ⟨x, y, z, w, hdet, hgm⟩
    refine mem_Gamma0R_of_entries x y (N * z) w ?_ (dvd_mul_right _ _)
    rw [hgm]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  · intro hg
    obtain ⟨a, b, c, d, hdet, ⟨z, rfl⟩, hgm⟩ := exists_entries_of_mem_Gamma0R hg
    refine ⟨a, b, z, d, by push_cast; linear_combination hdet, ?_⟩
    rw [hgm]
    ext i j; fin_cases i <;> fin_cases j <;> simp

/-! ### N = 4 -/

end

end NormalizerLean
