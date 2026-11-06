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
abbrev castM (M : Matℤ) : Matℝ := M.map (Int.cast)

theorem mem_Gamma0R_iff {N : ℕ} {g : SLℝ} :
    g ∈ Gamma0R N ↔ ∃ M : Matℤ,
      (N : ℤ) ∣ M 1 0 ∧ (g : Matℝ) = castM M := by
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
    let A : SLℤ := ⟨M, hdet⟩
    refine ⟨A, CongruenceSubgroup.Gamma0_mem.2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hM), ?_⟩
    refine Matrix.SpecialLinearGroup.ext _ _ (fun i j => ?_)
    rw [Matrix.SpecialLinearGroup.map_apply_coe, hg]
    rfl

/-- Elements of Γ₀(N) have integer entries, lower-left divisible by N, determinant 1. -/
theorem exists_entries_of_mem_Gamma0R {N : ℕ} {g : SLℝ} (hg : g ∈ Gamma0R N) :
    ∃ a b c d : ℤ, a * d - b * c = 1 ∧ (N : ℤ) ∣ c ∧
      (g : Matℝ) = !![(a : ℝ), b; c, d] := by
  obtain ⟨M, hM, hgM⟩ := mem_Gamma0R_iff.1 hg
  refine ⟨M 0 0, M 0 1, M 1 0, M 1 1, ?_, hM, ?_⟩
  · have h1 := g.2
    rw [hgM, det_fin_two] at h1
    simp only [castM, map_apply] at h1
    exact_mod_cast h1
  · rw [hgM]
    mat_smp

/-! ### h(N) -/

theorem hPart_pos (N : ℕ) : 0 < hPart N := by unfold hPart; positivity

/-! ### Units modulo divisors of 24 square to 1 -/

end

end NormalizerLean
