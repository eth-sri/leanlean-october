module
public import PottsDiscontinuity.BetheAnsatz.SpectralLimit

/-! # The coordinate Bethe eigenvector in all particle sectors -/
@[expose] public section
open Matrix
namespace PottsDiscontinuity.BetheAnsatz

/-- Theorem 3.1 in all particle sectors. The empty and one-particle cases are
handled directly; sectors of size at least two use the general regular and
zero-root branches above. The hypotheses imply the requested statement without
needing the half-filling bound. -/
theorem betheAnsatz_all {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin n → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hinj : Function.Injective p) (hBE : BetheEquations N (anisotropy c) p) :
    ((∀ j, p j ≠ 0) ∧
      (SixVertex.transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ
        betheVector (anisotropy c) p =
        eigenvalueRegular c p • betheVector (anisotropy c) p) ∨
    (∃ l, p l = 0 ∧
      (SixVertex.transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ
        betheVector (anisotropy c) p =
        eigenvalueZero N c p l • betheVector (anisotropy c) p) := by
  classical
  cases n with
  | zero =>
      have hnonzero : ∀ j : Fin 0, p j ≠ 0 := by
        grind
      exact Or.inl ⟨hnonzero, betheAnsatz_zero N c p⟩
  | succ n =>
      cases n with
      | zero =>
          by_cases hzero : p 0 = 0
          · exact Or.inr ⟨0, hzero, betheAnsatz_one_zero N c p 0 hzero⟩
          · have hnonzero : ∀ j : Fin 1, p j ≠ 0 := by
              grind
            exact Or.inl ⟨hnonzero, betheAnsatz_one_regular N c p hp hBE hnonzero⟩
      | succ m =>
          by_cases h : ∀ j, p j ≠ 0
          · exact .inl ⟨h, eigen_of_row_limit hc p hBE (regular_row_limit p fun j => z_ne_one (hp j) (h j))⟩
          push Not at h
          obtain ⟨a, ha⟩ := h
          exact .inr ⟨a, ha, eigen_of_row_limit hc p hBE (singular_row_limit hc p a ha
            (fun j hj => z_ne_one (hp j) fun he => hj (hinj (he.trans ha.symm))) hBE)⟩

end PottsDiscontinuity.BetheAnsatz
