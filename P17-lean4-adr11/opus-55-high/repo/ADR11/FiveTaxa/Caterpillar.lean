module

public import ADR11.Identifiability.FiveTaxa.Common
public import ADR11.Identifiability.FiveTaxa.Classes
public import ADR11.Rootings.Proofs
public meta import ADR11.Rootings.Proofs

/-!
# The rooted caterpillar 5-taxon species tree `((((a,b):x,c):y,d):z,e)`

Appendix B.2 (equation (12)), Table 2, the marginalization invariant, the equivalence classes,
the inequalities (5) and their exhaustiveness (Section 4.2.2). Throughout, `X = e^{-x}`,
`Y = e^{-y}`, `Z = e^{-z}` with `x, y, z` the lengths of the edges above `{a,b}`, `{a,b,c}` and
`{a,b,c,d}`.

As in the paper, each invariant of Table 2 is proved by its explanation: the near-the-root
argument and the symmetry `(ab)` (`ex_caterpillar_rows`, from `ADR11.FiveTaxa.Explanations`), and
for the last one the marginalization argument (`caterpillar_marginalization`: Lemma 5 on
`{b,c,d,e}` and the four-taxon distribution); the "if" direction of the equivalence classes
follows from these invariants. That the invariants form a basis, and that there are no others
(`table2`), rests on the explicit formulas (12), like the inequalities (5), as in the paper.
-/

@[expose] public section

namespace ADR11

open Finset Real

/-- **Equation (12)** (Appendix B.2): the unrooted gene tree distribution of the rooted caterpillar
species tree `((((a,b):x,c):y,d):z,e)`. -/
theorem equation12 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    let X := exp (-σ.length {0, 1})
    let Y := exp (-σ.length {0, 1, 2})
    let Z := exp (-σ.length {0, 1, 2, 3})
    u σ 1 = 1 - 2 / 3 * X - 2 / 3 * Y + 1 / 3 * X * Y + 1 / 18 * X * Y ^ 3 +
        1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
    u σ 2 = 1 / 3 * Y - 1 / 6 * X * Y - 1 / 9 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
    u σ 3 = 1 / 3 * Y - 1 / 6 * X * Y - 1 / 18 * X * Y ^ 3 - 2 / 45 * X * Y ^ 3 * Z ^ 6 ∧
    u σ 4 = 1 / 3 * X - 1 / 3 * X * Y + 1 / 18 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 13 = u σ 4 ∧
    u σ 5 = 1 / 6 * X * Y - 1 / 9 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 ∧ u σ 12 = u σ 5 ∧
    u σ 6 = 1 / 6 * X * Y - 1 / 18 * X * Y ^ 3 - 2 / 45 * X * Y ^ 3 * Z ^ 6 ∧ u σ 9 = u σ 6 ∧
    u σ 7 = 1 / 18 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 ∧ u σ 8 = u σ 7 ∧
      u σ 10 = u σ 7 ∧ u σ 11 = u σ 7 ∧ u σ 14 = u σ 7 ∧ u σ 15 = u σ 7 := by
  msc hσ

/-! ### The invariants of Table 2, by their explanations (Section 4.2.2) -/

/-- **Inequalities (5)**: for all branch lengths, `u₁ > u₂ > u₅`, `u₁ > u₄ > u₅`, `u₃ > u₂`,
`u₃ > u₆ > u₅` and `u₅ > u₇`. -/
theorem equation5 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    u σ 1 > u σ 2 ∧ u σ 1 > u σ 4 ∧ u σ 2 > u σ 5 ∧ u σ 4 > u σ 5 ∧ u σ 5 > u σ 7 ∧
      u σ 3 > u σ 2 ∧ u σ 3 > u σ 6 ∧ u σ 6 > u σ 5 := by
  obtain ⟨h1, h2, h3, h4, -, h5, -, h6, -, h7, -⟩ := equation12 σ hσ
  obtain ⟨hX, hX1⟩ := five_exp_bounds hσ {0, 1}
  obtain ⟨hY, hY1⟩ := five_exp_bounds hσ {0, 1, 2}
  obtain ⟨hZ, hZ1⟩ := five_exp_bounds hσ {0, 1, 2, 3}
  rw [h1, h2, h3, h4, h5, h6, h7]
  generalize exp (-σ.length {0, 1}) = X at *
  generalize exp (-σ.length {0, 1, 2}) = Y at *
  generalize exp (-σ.length {0, 1, 2, 3}) = Z at *
  have hX' : 0 < 1 - X := by linarith
  have hY' : 0 < 1 - Y := by linarith
  have hY3 : Y ^ 3 < 1 := pow_lt_one₀ hY.le hY1 (by norm_num)
  have hZ6 : Z ^ 6 < 1 := pow_lt_one₀ hZ.le hZ1 (by norm_num)
  have hY2 : 0 < 1 - Y ^ 2 := by nlinarith
  -- `u₁ - u₂ = k₁/6 + k₂/6`
  have k1 : 0 < (1 - X) * (4 - 3 * Y - Y ^ 3) := mul_pos hX' (by linarith)
  have k2 : 0 < (1 - Y) ^ 2 * (2 + Y) := by positivity
  -- `u₁ - u₄ = k₃`
  have k3 : 0 < (1 - X) * (1 - 2 / 3 * Y) := mul_pos hX' (by linarith)
  -- `u₂ - u₅ = u₃ - u₆ = k₄/3`
  have k4 : 0 < Y * (1 - X) := by positivity
  -- `u₄ - u₅ = k₅/6`
  have k5 : 0 < X * ((1 - Y) ^ 2 * (2 + Y)) := by positivity
  -- `u₅ - u₇ = k₆/6`
  have k6 : 0 < X * Y * (1 - Y ^ 2) := by positivity
  -- `u₃ - u₂ = u₆ - u₅ = k₇/18`
  have k7 : 0 < X * Y ^ 3 * (1 - Z ^ 6) := by positivity
  grind

/-- From the inequalities (5): the 6-element class always has the strictly smallest probability
and the class `{T₅, T₁₂}` the next smallest (used in the proof of Proposition 7). -/
theorem caterpillar_extremeClasses {σ : SpeciesTree (Fin 5)} (hσ : σ.clusters = caterpillar5) :
    cls_leastClass σ = {7, 8, 10, 11, 14, 15} ∧ cls_secondClass σ = {5, 12} := by
  obtain ⟨h12, h14, h25, h45, h57, h32, h36, h65⟩ := equation5 σ hσ
  obtain ⟨-, -, -, -, e13, -, e12, -, e9, -, e8, e10, e11, e14, e15⟩ := equation12 σ hσ
  ac1_cases ac1_least_second (u σ 7) (u σ 5) using h12, h14, h25, h45, h57, h32, h36, h65

end ADR11
