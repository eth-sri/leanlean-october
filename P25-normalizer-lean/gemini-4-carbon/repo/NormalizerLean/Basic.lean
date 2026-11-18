module

public import NormalizerLean.Defs

@[expose] public section

/-!
# Basic API for Γ₀(N) ≤ SL₂(ℝ), its normalizer, B(N), S_k and h(N)
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ### Membership in Γ₀(N) -/

/-- The real matrix of an integer matrix. -/
abbrev castM (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℝ := M.map (Int.cast)

theorem mem_Gamma0R_iff {N : ℕ} {g : SL(2, ℝ)} :
    g ∈ Gamma0R N ↔ ∃ M : Matrix (Fin 2) (Fin 2) ℤ,
      (N : ℤ) ∣ M 1 0 ∧ (g : Matrix (Fin 2) (Fin 2) ℝ) = castM M := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨A, ?_, ?_⟩
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (CongruenceSubgroup.Gamma0_mem.1 hA)
    · ext i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  · rintro ⟨M, hM, hg⟩
    have hdet : M.det = 1 := by
      have h1 := g.2
      rw [hg, det_fin_two] at h1
      rw [det_fin_two]
      simp only [castM, map_apply] at h1
      exact_mod_cast h1
    let A : SL(2, ℤ) := ⟨M, hdet⟩
    refine ⟨A, CongruenceSubgroup.Gamma0_mem.2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hM), ?_⟩
    refine Matrix.SpecialLinearGroup.ext _ _ (fun i j => ?_)
    rw [Matrix.SpecialLinearGroup.map_apply_coe, hg]
    rfl

/-- Membership in Γ₀(N) from explicit integer entries. -/
theorem mem_Gamma0R_of_entries {N : ℕ} {g : SL(2, ℝ)} (a b c d : ℤ)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; c, d]) (hc : (N : ℤ) ∣ c) :
    g ∈ Gamma0R N := by
  refine mem_Gamma0R_iff.2 ⟨!![a, b; c, d], by simpa using hc, ?_⟩
  rw [hg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Elements of Γ₀(N) have integer entries, lower-left divisible by N, determinant 1. -/
theorem exists_entries_of_mem_Gamma0R {N : ℕ} {g : SL(2, ℝ)} (hg : g ∈ Gamma0R N) :
    ∃ a b c d : ℤ, a * d - b * c = 1 ∧ (N : ℤ) ∣ c ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) = !![(a : ℝ), b; c, d] := by
  obtain ⟨M, hM, hgM⟩ := mem_Gamma0R_iff.1 hg
  refine ⟨M 0 0, M 0 1, M 1 0, M 1 1, ?_, hM, ?_⟩
  · have h1 := g.2
    rw [hgM, det_fin_two] at h1
    simp only [castM, map_apply] at h1
    exact_mod_cast h1
  · rw [hgM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-! ### The normalizer -/

/-! ### B(N) -/

/-! ### Translations S_k -/

theorem coe_S (k : ℕ) : ((S k : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, (k : ℝ)⁻¹; 0, 1] :=
  rfl

/-! ### h(N) -/

theorem hPart_pos (N : ℕ) : 0 < hPart N := by
  unfold hPart
  positivity

/-! ### Units modulo divisors of 24 square to 1 -/

theorem modEq_of_mul_modEq_one {k : ℕ} (hk : k ∣ 24) {a d : ℤ} (h : a * d ≡ 1 [ZMOD k]) :
    a ≡ d [ZMOD k] := by
  have hk24 : k ≤ 24 := Nat.le_of_dvd (by norm_num) hk
  rw [← ZMod.intCast_eq_intCast_iff] at h ⊢
  push_cast at h
  generalize (a : ZMod k) = x at h ⊢
  generalize (d : ZMod k) = y at h ⊢
  revert x y
  interval_cases k <;> norm_num at hk <;> decide

end

end NormalizerLean
