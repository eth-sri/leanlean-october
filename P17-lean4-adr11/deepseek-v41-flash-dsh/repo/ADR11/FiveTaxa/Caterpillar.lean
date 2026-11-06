module

public import ADR11.FiveTaxa.Basic
public import ADR11.Computation.FiveTaxa
public import ADR11.FiveTaxa.Explanations

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
theorem equation12 (σ : ST5) (hσ : σ.clusters = caterpillar5) :
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
  have h (i : ℕ) (hi : i ∈ F15) :
      u σ i = Computation.evalPoly σ.length (Computation.cat5Poly i) :=
    Computation.u_cat5 σ hσ hi
  dsimp only
  rw [h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide),
    h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide),
    h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide)]
  simp only [Computation.cat5Poly, Computation.evalPoly_cons, Computation.evalPoly_nil,
    Computation.monoVal_cons, Computation.monoVal_nil, Computation.decC_5_3,
    Computation.decC_5_7, Computation.decC_5_15]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | ring

/-! ### Helpers: the formulas (12) on the classes, and caterpillars with given `X, Y, Z` -/

/-- For a caterpillar species tree, `X, Y, Z ∈ (0, 1)`. -/
theorem tables_cat_bounds (σ : ST5) (hσ : σ.clusters = caterpillar5) :
    0 < exp (-σ.length {0, 1}) ∧ exp (-σ.length {0, 1}) < 1 ∧
    0 < exp (-σ.length {0, 1, 2}) ∧ exp (-σ.length {0, 1, 2}) < 1 ∧
    0 < exp (-σ.length {0, 1, 2, 3}) ∧ exp (-σ.length {0, 1, 2, 3}) < 1 := by
  have h : ∀ A ∈ caterpillar5, A ≠ univ → exp (-σ.length A) < 1 := fun A hA hne =>
    Real.exp_lt_one_iff.2 (neg_lt_zero.2 (σ.length_pos A (hσ ▸ hA) hne))
  exact ⟨exp_pos _, h _ (by decide) (by decide), exp_pos _, h _ (by decide) (by decide),
    exp_pos _, h _ (by decide) (by decide)⟩

/-- Equation (12) on the names of the classes, with `X, Y, Z ∈ (0, 1)`. -/
private theorem tables_cat_formulas (σ : ST5) (hσ : σ.clusters = caterpillar5) :
    ∃ X Y Z : ℝ, 0 < X ∧ X < 1 ∧ 0 < Y ∧ Y < 1 ∧ 0 < Z ∧ Z < 1 ∧
      u σ 1 = 1 - 2 / 3 * X - 2 / 3 * Y + 1 / 3 * X * Y + 1 / 18 * X * Y ^ 3 +
        1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 2 = 1 / 3 * Y - 1 / 6 * X * Y - 1 / 9 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 3 = 1 / 3 * Y - 1 / 6 * X * Y - 1 / 18 * X * Y ^ 3 - 2 / 45 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 4 = 1 / 3 * X - 1 / 3 * X * Y + 1 / 18 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 5 = 1 / 6 * X * Y - 1 / 9 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 6 = 1 / 6 * X * Y - 1 / 18 * X * Y ^ 3 - 2 / 45 * X * Y ^ 3 * Z ^ 6 ∧
      u σ 7 = 1 / 18 * X * Y ^ 3 + 1 / 90 * X * Y ^ 3 * Z ^ 6 := by
  obtain ⟨h1, h2, h3, h4, -, h5, -, h6, -, h7, -⟩ := equation12 σ hσ
  obtain ⟨a, b, c, d, e, f⟩ := tables_cat_bounds σ hσ
  exact ⟨_, _, _, a, b, c, d, e, f, h1, h2, h3, h4, h5, h6, h7⟩

/-! ### The invariants of Table 2, by their explanations (Section 4.2.2) -/

/-- The class of `T_i` in the partition of Section 4.2.2, named by its smallest index:
`{T₁}, {T₂}, {T₃}, {T₄,T₁₃}, {T₅,T₁₂}, {T₆,T₉}, {T₇,T₈,T₁₀,T₁₁,T₁₄,T₁₅}`. -/
def caterpillarClass : ℕ → ℕ
  | 13 => 4 | 12 => 5 | 9 => 6
  | 8 => 7 | 10 => 7 | 11 => 7 | 14 => 7 | 15 => 7 | i => i

/-- **Inequalities (5)**: for all branch lengths, `u₁ > u₂ > u₅`, `u₁ > u₄ > u₅`, `u₃ > u₂`,
`u₃ > u₆ > u₅` and `u₅ > u₇`. -/
theorem equation5 (σ : ST5) (hσ : σ.clusters = caterpillar5) :
    u σ 1 > u σ 2 ∧ u σ 1 > u σ 4 ∧ u σ 2 > u σ 5 ∧ u σ 4 > u σ 5 ∧ u σ 5 > u σ 7 ∧
      u σ 3 > u σ 2 ∧ u σ 3 > u σ 6 ∧ u σ 6 > u σ 5 := by
  obtain ⟨X, Y, Z, hX, hX1, hY, hY1, hZ, hZ1, h1, h2, h3, h4, h5, h6, h7⟩ :=
    tables_cat_formulas σ hσ
  rw [h1, h2, h3, h4, h5, h6, h7]
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
  have k7 : 0 < X * Y ^ 3 * (1 - Z ^ 6) := mul_pos (by positivity) (by linarith)
  exact ⟨by linarith only [k1, k2], by linarith only [k3], by linarith only [k4],
    by linarith only [k5], by linarith only [k6], by linarith only [k7], by linarith only [k4],
    by linarith only [k7]⟩

open scoped Classical in
/-- From the inequalities (5): the 6-element class always has the strictly smallest probability
and the class `{T₅, T₁₂}` the next smallest (used in the proof of Proposition 7). -/
theorem caterpillar_extremeClasses (σ : ST5) (hσ : σ.clusters = caterpillar5) :
    {i ∈ F15 | ∀ j ∈ F15, u σ i ≤ u σ j} = {7, 8, 10, 11, 14, 15} ∧
    {i ∈ F15 | u σ 7 < u σ i ∧ ∀ j ∈ F15, u σ 7 < u σ j → u σ i ≤ u σ j} =
      {5, 12} := by
  obtain ⟨h12, h14, h25, h45, h57, h32, h36, h65⟩ := equation5 σ hσ
  obtain ⟨-, -, -, -, e13, -, e12, -, e9, -, e8, e10, e11, e14, e15⟩ := equation12 σ hσ
  have K1 : ∀ j ∈ F15, u σ 7 ≤ u σ j := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := mem_Icc.1 hj
    interval_cases j <;> linarith
  have K2 : ∀ j ∈ F15, u σ 7 < u σ j → u σ 5 ≤ u σ j := by
    intro j hj hj7
    obtain ⟨hj1, hj2⟩ := mem_Icc.1 hj
    interval_cases j <;> linarith
  refine ⟨?_, ?_⟩
  · ext i
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hi, h⟩
      have h7 := h 7 (by simp)
      obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
      interval_cases i <;> first | (exfalso; linarith) | simp
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;>
        exact ⟨by simp, fun j hj => by linarith [K1 j hj]⟩
  · ext i
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hi, hlt, h⟩
      have h5 := h 5 (by simp) h57
      obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
      interval_cases i <;> first | (exfalso; linarith) | simp
    · rintro (rfl | rfl) <;>
        exact ⟨by simp, by linarith, fun j hj hj7 => by linarith [K2 j hj hj7]⟩

end ADR11
