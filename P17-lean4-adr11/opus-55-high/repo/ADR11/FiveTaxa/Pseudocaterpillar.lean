module

public import ADR11.Identifiability.FiveTaxa.Common
public import ADR11.Identifiability.FiveTaxa.Classes
public import ADR11.Rootings.Proofs
public meta import ADR11.Rootings.Proofs

/-!
# The pseudocaterpillar 5-taxon species tree `(((a,b):x,(d,e):y):z,c)`

Appendix B.3 (equation (13)), Table 3, the equivalence classes, the inequalities (6) and their
exhaustiveness (Section 4.2.3). Throughout, `X = e^{-x}`, `Y = e^{-y}`, `Z = e^{-z}` with
`x, y, z` the lengths of the edges above `{a,b}`, `{d,e}` and `{a,b,d,e}`.

As in the paper, each invariant of Table 3 is proved by its explanation
(`ex_pseudocaterpillar_rows`): the symmetries `(ab)`, `(de)`, `(ab)(de)` of the species tree, or
the near-the-root argument (`ADR11.FiveTaxa.Explanations`); the "if" direction of the equivalence
classes follows from these invariants. That the invariants form a basis, and that there are no
others (`table3`), rests on the explicit formulas (13), like the inequalities (6), as in the
paper.
-/

@[expose] public section

namespace ADR11

open Finset Real

/-- **Equation (13)** (Appendix B.3): the unrooted gene tree distribution of the pseudocaterpillar
species tree `(((a,b):x,(d,e):y):z,c)`. -/
theorem equation13 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = pseudocaterpillar5) :
    let X := exp (-σ.length {0, 1})
    let Y := exp (-σ.length {3, 4})
    let Z := exp (-σ.length {0, 1, 3, 4})
    u σ 1 = 1 - 2 / 3 * X - 2 / 3 * Y + 4 / 9 * X * Y - 2 / 45 * X * Y * Z ^ 6 ∧
    u σ 2 = 1 / 3 * Y - 5 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6 ∧ u σ 3 = u σ 2 ∧
    u σ 4 = 1 / 3 * X - 5 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6 ∧ u σ 13 = u σ 4 ∧
    u σ 5 = 1 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6 ∧ u σ 6 = u σ 5 ∧ u σ 7 = u σ 5 ∧
      u σ 9 = u σ 5 ∧ u σ 10 = u σ 5 ∧ u σ 12 = u σ 5 ∧ u σ 14 = u σ 5 ∧ u σ 15 = u σ 5 ∧
    u σ 8 = 1 / 9 * X * Y - 2 / 45 * X * Y * Z ^ 6 ∧ u σ 11 = u σ 8 := by
  msc hσ

/-! ### The invariants of Table 3, by their explanations (Section 4.2.3) -/

/-- **Inequalities (6)**: for all branch lengths, `u₁ > u₂ > u₅`, `u₁ > u₄ > u₅` and
`u₁ > u₈ > u₅`. -/
theorem equation6 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = pseudocaterpillar5) :
    u σ 1 > u σ 2 ∧ u σ 1 > u σ 4 ∧ u σ 1 > u σ 8 ∧ u σ 2 > u σ 5 ∧ u σ 4 > u σ 5 ∧
      u σ 8 > u σ 5 := by
  obtain ⟨h1, h2, -, h4, -, h5, -, -, -, -, -, -, -, h8, -⟩ := equation13 σ hσ
  obtain ⟨hX, hX1⟩ := five_exp_bounds hσ {0, 1}
  obtain ⟨hY, hY1⟩ := five_exp_bounds hσ {3, 4}
  obtain ⟨hZ, hZ1⟩ := five_exp_bounds hσ {0, 1, 3, 4}
  rw [h1, h2, h4, h5, h8]
  generalize exp (-σ.length {0, 1}) = X at *
  generalize exp (-σ.length {3, 4}) = Y at *
  generalize exp (-σ.length {0, 1, 3, 4}) = Z at *
  have hX' : 0 < 1 - X := by linarith
  have hY' : 0 < 1 - Y := by linarith
  have hZ6 : Z ^ 6 < 1 := pow_lt_one₀ hZ.le hZ1 (by norm_num)
  -- `u₁ - u₂ = k₁ + k₈/18`, `u₁ - u₄ = k₂ + k₈/18`, `u₁ - u₈ = k₃ + (k₄ + k₅)/3`,
  -- `u₂ - u₅ = k₄/3`, `u₄ - u₅ = k₅/3`, `u₈ - u₅ = k₈/18`
  have k1 : 0 < (1 - Y) * (1 - 2 / 3 * X) := mul_pos hY' (by linarith)
  have k2 : 0 < (1 - X) * (1 - 2 / 3 * Y) := mul_pos hX' (by linarith)
  have k3 : 0 < (1 - X) * (1 - Y) := by positivity
  have k4 : 0 < Y * (1 - X) := by positivity
  have k5 : 0 < X * (1 - Y) := by positivity
  have k8 : 0 < X * Y * (1 - Z ^ 6) := by positivity
  grind

/-- Section 4.2.3: the 8-element class always has the strictly smallest probability. -/
theorem pseudocaterpillar_minClass {σ : SpeciesTree (Fin 5)}
    (hσ : σ.clusters = pseudocaterpillar5) : cls_leastClass σ = {5, 6, 7, 9, 10, 12, 14, 15} := by
  obtain ⟨h12, h14, h18, h25, h45, h85⟩ := equation6 σ hσ
  obtain ⟨-, -, e3, -, e13, -, e6, e7, e9, e10, e12, e14, e15, -, e11⟩ := equation13 σ hσ
  ac1_cases ac1_least (u σ 5) using h12, h14, h18, h25, h45, h85

end ADR11
