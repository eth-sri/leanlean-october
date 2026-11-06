module

public import ADR11.FiveTaxa.Basic
public import ADR11.Computation.FiveTaxa
public import ADR11.FiveTaxa.Explanations

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
  have h (i : ℕ) (hi : i ∈ Icc 1 15) :
      u σ i = Computation.evalPoly σ.length (Computation.pseudo5Poly i) :=
    Computation.u_pseudo5 σ hσ hi
  dsimp only
  rw [h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide),
    h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide),
    h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide)]
  simp only [Computation.pseudo5Poly, Computation.evalPoly_cons, Computation.evalPoly_nil,
    Computation.monoVal_cons, Computation.monoVal_nil, Computation.decC_5_3,
    Computation.decC_5_24, Computation.decC_5_27]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | ring

/-! ### Helpers: the formulas (13) on the classes, and pseudocaterpillars with given `X, Y, Z` -/

/-- For a pseudocaterpillar species tree, `X, Y, Z ∈ (0, 1)`. -/
theorem tables_pse_bounds (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = pseudocaterpillar5) :
    0 < exp (-σ.length {0, 1}) ∧ exp (-σ.length {0, 1}) < 1 ∧
    0 < exp (-σ.length {3, 4}) ∧ exp (-σ.length {3, 4}) < 1 ∧
    0 < exp (-σ.length {0, 1, 3, 4}) ∧ exp (-σ.length {0, 1, 3, 4}) < 1 := by
  have h : ∀ A ∈ pseudocaterpillar5, A ≠ univ → exp (-σ.length A) < 1 := fun A hA hne =>
    Real.exp_lt_one_iff.2 (neg_lt_zero.2 (σ.length_pos A (hσ ▸ hA) hne))
  exact ⟨exp_pos _, h _ (by decide) (by decide), exp_pos _, h _ (by decide) (by decide),
    exp_pos _, h _ (by decide) (by decide)⟩

/-- Equation (13) on the names of the classes, with `X, Y, Z ∈ (0, 1)`. -/
private theorem tables_pse_formulas (σ : SpeciesTree (Fin 5))
    (hσ : σ.clusters = pseudocaterpillar5) :
    ∃ X Y Z : ℝ, 0 < X ∧ X < 1 ∧ 0 < Y ∧ Y < 1 ∧ 0 < Z ∧ Z < 1 ∧
      u σ 1 = 1 - 2 / 3 * X - 2 / 3 * Y + 4 / 9 * X * Y - 2 / 45 * X * Y * Z ^ 6 ∧
      u σ 2 = 1 / 3 * Y - 5 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6 ∧
      u σ 4 = 1 / 3 * X - 5 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6 ∧
      u σ 5 = 1 / 18 * X * Y + 1 / 90 * X * Y * Z ^ 6 ∧
      u σ 8 = 1 / 9 * X * Y - 2 / 45 * X * Y * Z ^ 6 := by
  obtain ⟨h1, h2, -, h4, -, h5, -, -, -, -, -, -, -, h8, -⟩ := equation13 σ hσ
  obtain ⟨a, b, c, d, e, f⟩ := tables_pse_bounds σ hσ
  exact ⟨_, _, _, a, b, c, d, e, f, h1, h2, h4, h5, h8⟩

/-! ### The invariants of Table 3, by their explanations (Section 4.2.3) -/

/-- The class of `T_i` in the partition of Section 4.2.3, named by its smallest index:
`{T₁}, {T₂,T₃}, {T₄,T₁₃}, {T₈,T₁₁}, {T₅,T₆,T₇,T₉,T₁₀,T₁₂,T₁₄,T₁₅}`. -/
def pseudocaterpillarClass : ℕ → ℕ
  | 3 => 2 | 13 => 4 | 11 => 8
  | 6 => 5 | 7 => 5 | 9 => 5 | 10 => 5 | 12 => 5 | 14 => 5 | 15 => 5 | i => i

/-- **Inequalities (6)**: for all branch lengths, `u₁ > u₂ > u₅`, `u₁ > u₄ > u₅` and
`u₁ > u₈ > u₅`. -/
theorem equation6 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = pseudocaterpillar5) :
    u σ 1 > u σ 2 ∧ u σ 1 > u σ 4 ∧ u σ 1 > u σ 8 ∧ u σ 2 > u σ 5 ∧ u σ 4 > u σ 5 ∧
      u σ 8 > u σ 5 := by
  obtain ⟨X, Y, Z, hX, hX1, hY, hY1, hZ, hZ1, h1, h2, h4, h5, h8⟩ := tables_pse_formulas σ hσ
  rw [h1, h2, h4, h5, h8]
  have hX' : 0 < 1 - X := by linarith
  have hY' : 0 < 1 - Y := by linarith
  have hZ6 : Z ^ 6 < 1 := pow_lt_one₀ hZ.le hZ1 (by norm_num)
  -- `u₁ - u₂ = k₁ + k₈/18`, `u₁ - u₄ = k₂ + k₈/18`, `u₁ - u₈ = k₃ + (k₄ + k₅)/3`,
  -- `u₂ - u₅ = k₄/3`, `u₄ - u₅ = k₅/3`, `u₈ - u₅ = k₈/18`
  have k1 : 0 < (1 - Y) * (1 - 2 / 3 * X) := mul_pos hY' (by linarith)
  have k2 : 0 < (1 - X) * (1 - 2 / 3 * Y) := mul_pos hX' (by linarith)
  have k3 : 0 < (1 - X) * (1 - Y) := mul_pos hX' hY'
  have k4 : 0 < Y * (1 - X) := mul_pos hY hX'
  have k5 : 0 < X * (1 - Y) := mul_pos hX hY'
  have k8 : 0 < X * Y * (1 - Z ^ 6) := mul_pos (mul_pos hX hY) (by linarith)
  exact ⟨by linarith only [k1, k8], by linarith only [k2, k8], by linarith only [k3, k4, k5],
    by linarith only [k4], by linarith only [k5], by linarith only [k8]⟩

open scoped Classical in
/-- Section 4.2.3: the 8-element class always has the strictly smallest probability. -/
theorem pseudocaterpillar_minClass (σ : SpeciesTree (Fin 5))
    (hσ : σ.clusters = pseudocaterpillar5) :
    {i ∈ Icc 1 15 | ∀ j ∈ Icc 1 15, u σ i ≤ u σ j} = {5, 6, 7, 9, 10, 12, 14, 15} := by
  obtain ⟨h12, h14, h18, h25, h45, h85⟩ := equation6 σ hσ
  obtain ⟨-, -, e3, -, e13, -, e6, e7, e9, e10, e12, e14, e15, -, e11⟩ := equation13 σ hσ
  have K : ∀ j ∈ Icc 1 15, u σ 5 ≤ u σ j := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := mem_Icc.1 hj
    interval_cases j <;> linarith
  ext i
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hi, h⟩
    have h5 := h 5 (by simp)
    obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
    interval_cases i <;> first | (exfalso; linarith) | simp
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact ⟨by simp, fun j hj => by linarith [K j hj]⟩

end ADR11
