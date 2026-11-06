module
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonPrefixVectors

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonPrefixGramMax (m N : ℕ) (t u : ℝ) : ℝ :=
  (Finset.range (N+1)).sup' (by simp) (fun j => ‖atkinsonPrefixGram m j t u‖)

theorem norm_atkinsonPrefixGram_le_max (m N j : ℕ) (hj : j ≤ N) (t u : ℝ) :
    ‖atkinsonPrefixGram m j t u‖ ≤ atkinsonPrefixGramMax m N t u := by
  unfold atkinsonPrefixGramMax
  aesop

section
variable (m N : ℕ)
include m N
theorem atkinsonPrefixGramMax_nonneg (t u : ℝ) :
    0 ≤ atkinsonPrefixGramMax m N t u := by
  have h := norm_atkinsonPrefixGram_le_max m N 0 (Nat.zero_le N) t u
  simpa [atkinsonPrefixGram] using h

theorem atkinsonPrefixGramMax_self (t : ℝ) :
    atkinsonPrefixGramMax m N t t = (N:ℝ) := by
  apply le_antisymm
  · unfold atkinsonPrefixGramMax
    apply Finset.sup'_le
    intro j hj
    rw [norm_atkinsonPrefixGram_self]
    simp_all
  · simpa only [norm_atkinsonPrefixGram_self] using
      norm_atkinsonPrefixGram_le_max m N N le_rfl t t

theorem atkinsonPrefixGramMax_swap (t u : ℝ) :
    atkinsonPrefixGramMax m N u t = atkinsonPrefixGramMax m N t u := by
  unfold atkinsonPrefixGramMax
  simp_rw [atkinsonPrefixGram_swap m _ u t,Complex.norm_conj]
end


end MathCollab.Density.Stronger.Atkinson
