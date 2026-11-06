module

public import ADR11.Identifiability.FiveTaxa.Common
public import ADR11.Identifiability.FiveTaxa.Classes
public import ADR11.Rootings.Proofs
public meta import ADR11.Rootings.Proofs

/-!
# The balanced 5-taxon species tree `(((a,b):x,c):y,(d,e):z)`

Appendix B.1 (equation (11)), Table 1, the equivalence classes, the inequalities (4), their
exhaustiveness, and the extreme classes (Section 4.2.1). Throughout, `X = e^{-x}`, `Y = e^{-y}`,
`Z = e^{-z}` with `x, y, z` the lengths of the edges above `{a,b}`, `{a,b,c}` and `{d,e}`.

As in the paper, each invariant of Table 1 is proved by its explanation (`ex_balanced_rows`):
the symmetries `(ab)`, `(de)`, `(ab)(de)` of the species tree, or the above-the-root argument with
Lemma 4 (`ADR11.FiveTaxa.Explanations`); the "if" direction of the equivalence classes follows
from these invariants. That the invariants form a basis, and that there are no others
(`table1`), rests on the explicit formulas (11), like the inequalities (4), as in the paper.
-/

@[expose] public section

namespace ADR11

open Finset Real

/-- **Equation (11)** (Appendix B.1): the unrooted gene tree distribution of the balanced species
tree `(((a,b):x,c):y,(d,e):z)`. -/
theorem equation11 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = balanced5) :
    let X := exp (-σ.length {0, 1})
    let Y := exp (-σ.length {0, 1, 2})
    let Z := exp (-σ.length {3, 4})
    u σ 1 = 1 - 2 / 3 * X - 2 / 3 * Y * Z + 1 / 3 * X * Y * Z + 1 / 15 * X * Y ^ 3 * Z ∧
    u σ 2 = 1 / 3 * Y * Z - 1 / 6 * X * Y * Z - 1 / 10 * X * Y ^ 3 * Z ∧ u σ 3 = u σ 2 ∧
    u σ 4 = 1 / 3 * X - 1 / 3 * X * Y * Z + 1 / 15 * X * Y ^ 3 * Z ∧ u σ 13 = u σ 4 ∧
    u σ 5 = 1 / 6 * X * Y * Z - 1 / 10 * X * Y ^ 3 * Z ∧ u σ 6 = u σ 5 ∧ u σ 9 = u σ 5 ∧
      u σ 12 = u σ 5 ∧
    u σ 7 = 1 / 15 * X * Y ^ 3 * Z ∧ u σ 8 = u σ 7 ∧ u σ 10 = u σ 7 ∧ u σ 11 = u σ 7 ∧
      u σ 14 = u σ 7 ∧ u σ 15 = u σ 7 := by
  msc hσ

/-! ### The invariants of Table 1, by their explanations (Section 4.2.1) -/

/-- **Inequalities (4)**: for all branch lengths, `u₁ > u₂ > u₅`, `u₁ > u₄ > u₅` and `u₅ > u₇`. -/
theorem equation4 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = balanced5) :
    u σ 1 > u σ 2 ∧ u σ 1 > u σ 4 ∧ u σ 2 > u σ 5 ∧ u σ 4 > u σ 5 ∧ u σ 5 > u σ 7 := by
  obtain ⟨h1, h2, -, h4, -, h5, -, -, -, h7, -⟩ := equation11 σ hσ
  obtain ⟨hX, hX1⟩ := five_exp_bounds hσ {0, 1}
  obtain ⟨hY, hY1⟩ := five_exp_bounds hσ {0, 1, 2}
  obtain ⟨hZ, hZ1⟩ := five_exp_bounds hσ {3, 4}
  rw [h1, h2, h4, h5, h7]
  generalize exp (-σ.length {0, 1}) = X at *
  generalize exp (-σ.length {0, 1, 2}) = Y at *
  generalize exp (-σ.length {3, 4}) = Z at *
  have hX' : 0 < 1 - X := by linarith
  have hZ' : 0 < 1 - Z := by linarith
  have hYZ : Y * Z < 1 := by nlinarith
  have hY3 : Y ^ 3 < 1 := pow_lt_one₀ hY.le hY1 (by norm_num)
  have hY3Z : Y ^ 3 * Z < 1 := by nlinarith [pow_pos hY 3]
  have hY2 : 0 < 1 - Y ^ 2 := by nlinarith
  -- `u₁ - u₂ = k₁/6 + (1 - Z)/3 + k₂/6`
  have k1 : 0 < (1 - X) * (4 - 3 * (Y * Z) - Y ^ 3 * Z) := mul_pos hX' (by linarith)
  have k2 : 0 ≤ Z * ((1 - Y) ^ 2 * (2 + Y)) := by positivity
  -- `u₁ - u₄ = k₃`
  have k3 : 0 < (1 - X) * (1 - 2 / 3 * (Y * Z)) := mul_pos hX' (by linarith)
  -- `u₂ - u₅ = k₄/3`
  have k4 : 0 < Y * Z * (1 - X) := by positivity
  -- `u₄ - u₅ = k₅/6`
  have k5 : 0 < X * (2 * (1 - Z) + Z * ((1 - Y) ^ 2 * (2 + Y))) := by positivity
  -- `u₅ - u₇ = k₆/6`
  have k6 : 0 < X * Y * Z * (1 - Y ^ 2) := by positivity
  grind

/-- Section 4.2.1: the 6-element class always has the strictly smallest probability, and the
4-element class the next smallest. -/
theorem balanced_extremeClasses {σ : SpeciesTree (Fin 5)} (hσ : σ.clusters = balanced5) :
    cls_leastClass σ = {7, 8, 10, 11, 14, 15} ∧ cls_secondClass σ = {5, 6, 9, 12} := by
  obtain ⟨h12, h14, h25, h45, h57⟩ := equation4 σ hσ
  obtain ⟨-, -, e3, -, e13, -, e6, e9, e12, -, e8, e10, e11, e14, e15⟩ := equation11 σ hσ
  ac1_cases ac1_least_second (u σ 7) (u σ 5) using h12, h14, h25, h45, h57

end ADR11
