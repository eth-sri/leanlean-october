module

public import PottsDiscontinuity.BetheAnsatz.SpectralLimit
public import PottsDiscontinuity.BetheAnsatz.OneParticle

/-!
# The degenerate zero-momentum Bethe Ansatz branch

The two eigenvalue branches obtained from the common spectral deformation,
with the empty and one-particle sectors handled directly.
-/

@[expose] public section

open Finset Complex Matrix Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- Theorem 3.1 for every sector with at least two particles, stated as the two
mutually exclusive momentum branches. Injectivity makes the zero-root index unique. -/
theorem betheAnsatz_twoOrMore {N m : ℕ} {c : ℝ} (hc : 2 < c)
    (p : Fin (m + 2) → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
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
  by_cases hnonzero : ∀ j, p j ≠ 0
  · exact Or.inl ⟨hnonzero, betheAnsatz_regular hc p hp hnonzero hBE⟩
  · push Not at hnonzero
    rcases hnonzero with ⟨l, hl⟩
    have hpl : p l = 0 := by simpa using hl
    exact Or.inr ⟨l, hpl, betheAnsatz_zeroRoot hc p hp hinj l hpl hBE⟩

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
        simp
      exact Or.inl ⟨hnonzero, betheAnsatz_zero N c p⟩
  | succ n =>
      cases n with
      | zero =>
          by_cases hzero : p 0 = 0
          · exact Or.inr ⟨0, hzero, betheAnsatz_one_zero N c p 0 hzero⟩
          · have hnonzero : ∀ j : Fin 1, p j ≠ 0 := by
              simp_all
            exact Or.inl ⟨hnonzero, betheAnsatz_one_regular N c p hp hBE hnonzero⟩
      | succ m =>
          exact betheAnsatz_twoOrMore hc p hp hinj hBE

end PottsDiscontinuity.BetheAnsatz
