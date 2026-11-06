module

public import ADR11.FiveTaxa.Basic
public import ADR11.Computation.FiveTaxa
public import ADR11.FiveTaxa.Explanations
public import ADR11.Identifiability.FiveTaxa.Classes

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
  have h (i : ℕ) (hi : i ∈ Icc 1 15) :
      u σ i = Computation.evalPoly σ.length (Computation.bal5Poly i) :=
    Computation.u_bal5 σ hσ hi
  dsimp only
  rw [h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide),
    h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide),
    h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide)]
  simp only [Computation.bal5Poly, Computation.evalPoly_cons, Computation.evalPoly_nil,
    Computation.monoVal_cons, Computation.monoVal_nil, Computation.decC_5_3,
    Computation.decC_5_7, Computation.decC_5_24]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | ring

/-! ### Helpers: the formulas (11) on the classes, and balanced trees with given `X, Y, Z` -/

/-- For a balanced species tree, `X, Y, Z ∈ (0, 1)`. -/
theorem tables_bal_bounds (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = balanced5) :
    0 < exp (-σ.length {0, 1}) ∧ exp (-σ.length {0, 1}) < 1 ∧
    0 < exp (-σ.length {0, 1, 2}) ∧ exp (-σ.length {0, 1, 2}) < 1 ∧
    0 < exp (-σ.length {3, 4}) ∧ exp (-σ.length {3, 4}) < 1 := by
  have h : ∀ A ∈ balanced5, A ≠ univ → exp (-σ.length A) < 1 := fun A hA hne =>
    Real.exp_lt_one_iff.2 (neg_lt_zero.2 (σ.length_pos A (hσ ▸ hA) hne))
  exact ⟨exp_pos _, h _ (by decide) (by decide), exp_pos _, h _ (by decide) (by decide),
    exp_pos _, h _ (by decide) (by decide)⟩

/-- Equation (11) on the names of the classes, with `X, Y, Z ∈ (0, 1)`. -/
private theorem tables_bal_formulas (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = balanced5) :
    ∃ X Y Z : ℝ, 0 < X ∧ X < 1 ∧ 0 < Y ∧ Y < 1 ∧ 0 < Z ∧ Z < 1 ∧
      u σ 1 = 1 - 2 / 3 * X - 2 / 3 * Y * Z + 1 / 3 * X * Y * Z + 1 / 15 * X * Y ^ 3 * Z ∧
      u σ 2 = 1 / 3 * Y * Z - 1 / 6 * X * Y * Z - 1 / 10 * X * Y ^ 3 * Z ∧
      u σ 4 = 1 / 3 * X - 1 / 3 * X * Y * Z + 1 / 15 * X * Y ^ 3 * Z ∧
      u σ 5 = 1 / 6 * X * Y * Z - 1 / 10 * X * Y ^ 3 * Z ∧
      u σ 7 = 1 / 15 * X * Y ^ 3 * Z := by
  obtain ⟨h1, h2, -, h4, -, h5, -, -, -, h7, -⟩ := equation11 σ hσ
  obtain ⟨a, b, c, d, e, f⟩ := tables_bal_bounds σ hσ
  exact ⟨_, _, _, a, b, c, d, e, f, h1, h2, h4, h5, h7⟩

/-! ### The invariants of Table 1, by their explanations (Section 4.2.1) -/

/-- The class of `T_i` in the partition of Section 4.2.1, named by its smallest index:
`{T₁}, {T₂,T₃}, {T₄,T₁₃}, {T₅,T₆,T₉,T₁₂}, {T₇,T₈,T₁₀,T₁₁,T₁₄,T₁₅}`. -/
def balancedClass : ℕ → ℕ
  | 3 => 2 | 13 => 4 | 6 => 5 | 9 => 5 | 12 => 5
  | 8 => 7 | 10 => 7 | 11 => 7 | 14 => 7 | 15 => 7 | i => i

/-- **Inequalities (4)**: for all branch lengths, `u₁ > u₂ > u₅`, `u₁ > u₄ > u₅` and `u₅ > u₇`. -/
theorem equation4 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = balanced5) :
    u σ 1 > u σ 2 ∧ u σ 1 > u σ 4 ∧ u σ 2 > u σ 5 ∧ u σ 4 > u σ 5 ∧ u σ 5 > u σ 7 := by
  obtain ⟨X, Y, Z, hX, hX1, hY, hY1, hZ, hZ1, h1, h2, h4, h5, h7⟩ := tables_bal_formulas σ hσ
  rw [h1, h2, h4, h5, h7]
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
  have k5 : 0 < X * (2 * (1 - Z) + Z * ((1 - Y) ^ 2 * (2 + Y))) := mul_pos hX (by positivity)
  -- `u₅ - u₇ = k₆/6`
  have k6 : 0 < X * Y * Z * (1 - Y ^ 2) := by positivity
  exact ⟨by linarith only [k1, k2, hZ'], by linarith only [k3], by linarith only [k4],
    by linarith only [k5], by linarith only [k6]⟩

open scoped Classical in
/-- Section 4.2.1: the 6-element class always has the strictly smallest probability, the
4-element class the next smallest, and the class of the largest probability is the singleton
`{T₁}`. -/
theorem balanced_extremeClasses (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = balanced5) :
    {i ∈ Icc 1 15 | ∀ j ∈ Icc 1 15, u σ i ≤ u σ j} = {7, 8, 10, 11, 14, 15} ∧
    {i ∈ Icc 1 15 | u σ 7 < u σ i ∧ ∀ j ∈ Icc 1 15, u σ 7 < u σ j → u σ i ≤ u σ j} =
      {5, 6, 9, 12} ∧
    {i ∈ Icc 1 15 | ∀ j ∈ Icc 1 15, u σ j ≤ u σ i} = {1} := by
  obtain ⟨h12, h14, h25, h45, h57⟩ := equation4 σ hσ
  obtain ⟨-, -, e3, -, e13, -, e6, e9, e12, -, e8, e10, e11, e14, e15⟩ := equation11 σ hσ
  have hL := five_leastClass_eq (τ := σ) {7, 8, 10, 11, 14, 15} (u σ 7)
    (by decide) (by decide) (by
      intro i hi
      obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
      interval_cases i <;> simp_all <;> linarith)
  have hS := five_secondClass_eq hL {5, 6, 9, 12} (u σ 5) (by decide) (by decide) (by decide) (by
      intro i hi
      obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
      interval_cases i <;> simp_all <;> linarith)
  have hM := five_mostProbable_eq (τ := σ) {1} (u σ 1) (by decide) (by decide) (by
      intro i hi
      obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
      interval_cases i <;> simp_all <;> linarith)
  refine ⟨hL, ?_, hM⟩
  rw [← cls_secondClass_eq_filter (m := 7) (by rw [hL]; decide)]
  exact hS

end ADR11
