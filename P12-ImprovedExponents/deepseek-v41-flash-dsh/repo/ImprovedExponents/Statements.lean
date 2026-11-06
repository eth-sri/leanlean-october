module

public import ThreeSumApsp.Statements.Exponents
public import ImprovedExponents.Pipeline.General
public import ImprovedExponents.Pipeline.PrunedClaim
public import ImprovedExponents.Optimum.NumValues
public import ImprovedExponents.Optimum.NumWitness
public import ImprovedExponents.Optimum.Global
public import ImprovedExponents.Optimum.GlobalFull
public import ImprovedExponents.AllEdges.Pairs.TimeBound
public import ImprovedExponents.AllEdges.Host.ClaimAE
public import ThreeSumApsp.TacticsShort

@[expose] public section

/-!
# The improved bounds for 3SUM, Exact Triangle, the (min,+)-product and APSP

The statements of this file are about programs of the word RAM of upstream's `EndStatement.lean`:
`Q.SolvedInTime r` says that for every exponent `κ` there are a program, a slope `b` and a time
bound `T(n) = O(n^r)` such that the program solves every instance of `Q` whose numbers have
absolute value at most `n^κ`, at every word size of at least `b (⌊log₂ n⌋ + 1)` bits, within `T(n)`
steps. Upstream proves the paper's Theorem 22 in this form: 3SUM with `r = 1.9992`, the
(min,+)-product and APSP with `r = 2.99942`, Exact Triangle with `r = 3 - 0.0017`.

Four sets of bounds follow, in the order of the ingredients they use. `δ` is the saving for Exact
Triangle; 3SUM keeps half of it and the (min,+)-product and APSP a third, or all of it through
all-edges Exact Triangle (`…_allEdges`). None of them has a hypothesis.

| | ingredients | `δ >` | 3SUM | Exact Triangle | (min,+), APSP | all-edges route |
|---|---|---|---|---|---|---|
| `…_paper` | the paper's algorithm and analysis, better parameters | 0.00184 | 1.99908 | 2.99816 |
2.99939 | |
| `…_exact` | + exact count of the leaves | 0.00196 | 1.99902 | 2.99804 | 2.99935 | |
| `…_full` | + reduction charged at the true middle size | 0.002059 | 1.99898 | 2.99795 | 2.99932 |
2.99795 |
| `…_pruned` | + pruned encodings | 0.002095 | 1.99896 | 2.99791 | 2.99931 | 2.99791 |

The numerals of the first two rows are taken at the ratio `c = 108/5`, which the regime test
`D^18 ≤ N` of the existing program admits; those of the third at `c = 107/5`, near the optimum of
the method, with the solver whose test is `D^r ≤ N^s` (`ImprovedExponents.Pipeline.RegimeRS`); those
of the last at `c = 22`, with the solver whose encoder is pruned
(`ImprovedExponents.PrunedProgram`, `ImprovedExponents.Pipeline.PrunedClaim`). The general theorems
behind them are `allSolved_paper`, `allSolved_exact`, `allSolved_full`
(`ImprovedExponents.Pipeline.General`) and `allSolved_pruned`
(`ImprovedExponents.Pipeline.PrunedClaim`), and the optima over the ratio are
`optimum_global_full` (paper's encodings) and `optimum_global` (pruned encodings);
`allSolved_full_sup` and `allSolved_pruned_sup` give every saving below them.
-/

namespace ImprovedExponents

open ThreeSumApsp.WordRam

/-! ## From a saving to the end statements -/

/-- The four end statements at rational exponents above the bounds of a saving `δ`. -/
theorem AllSolved.endStatements {δ : ℝ} (h : AllSolved δ) {r₃ rE rM : ℚ}
    (h₃ : 2 - δ / 2 < (r₃ : ℝ)) (hE : 3 - δ < (rE : ℝ)) (hM : 3 - δ / 3 < (rM : ℝ))
    (h₃0 : 0 ≤ r₃) (hE0 : 0 ≤ rE) (hM0 : 0 ≤ rM) :
    EndStatement.ThreeSum.SolvedInTime r₃ ∧ EndStatement.ExactTriangle.SolvedInTime rE ∧
      EndStatement.MinPlusProduct.SolvedInTime rM ∧ EndStatement.APSP.SolvedInTime rM :=
  ⟨SolvedInTime.endStatement (h.threeSum _ h₃) rfl h₃0,
    SolvedInTime.endStatement (h.exactTriangle _ hE) rfl hE0,
    SolvedInTime.endStatement (h.minPlus _ hM) rfl hM0,
    SolvedInTime.endStatement (h.apsp _ hM) rfl hM0⟩

/-! ## The savings -/

/-- **With pruned encodings** (`c = 22`): a saving of more than `0.002095` for Exact Triangle;
every saving below `R'_c(Γ) Γ/2 = 0.0020952…`. -/
theorem allSolved_pruned_num :
    ∃ δ : ℝ, (0.002095 : ℝ) < δ ∧ AllSolved δ :=
  ⟨(0.002095 + savingF (basePruned 22) (Gam 22)) / 2, by linarith [savingF_pruned_gt],
    allSolved_pruned (c := 22) tac_norm_num (by linarith [savingF_pruned_gt])
      (by linarith [savingF_pruned_gt])⟩

/-! ## The paper's algorithm and analysis at better parameters -/

/-! ## With the exact count of the leaves -/

/-! ## With the reduction charged at the true size of the middle part -/

/-! ## With pruned encodings -/

/-- With pruned encodings: 3SUM in `O(n^1.99896)`, Exact Triangle in `O(n^2.99791)`, the
(min,+)-product and APSP in `O(n^2.99931)`. -/
theorem endStatements_pruned :
    EndStatement.ThreeSum.SolvedInTime 1.99896 ∧
      EndStatement.ExactTriangle.SolvedInTime 2.99791 ∧
      EndStatement.MinPlusProduct.SolvedInTime 2.99931 ∧
      EndStatement.APSP.SolvedInTime 2.99931 := by
  obtain ⟨δ, hδ, h⟩ := allSolved_pruned_num
  exact h.endStatements (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
    tac_norm_num tac_norm_num tac_norm_num

/-- **3SUM in `O(n^1.99896)` steps on the word RAM**: the exact count, the true middle size and
pruned encodings. No hypothesis. -/
theorem threeSum_pruned : EndStatement.ThreeSum.SolvedInTime 1.99896 :=
  endStatements_pruned.1

/-- **Exact Triangle in `O(n^2.99791)` steps on the word RAM**, with pruned encodings. No
hypothesis. -/
theorem exactTriangle_pruned : EndStatement.ExactTriangle.SolvedInTime 2.99791 :=
  endStatements_pruned.2.1

/-! ## The optimum of the method -/

/-! ## APSP through all-edges Exact Triangle

Footnote 10 of the paper: the all-edges version of Exact Triangle is solved by the host of
Theorem 17 within the same bound (`ImprovedExponents.AllEdges.Host`), and the (min,+)-product
reduces to it on the same `n` vertices (`ImprovedExponents.AllEdges.Pairs`, upstream's bit search
and repeated squaring). So the (min,+)-product and APSP keep all of the saving `δ` of Exact
Triangle:
the exponent is `3 - δ` instead of `3 - δ/3`. -/

/-- The two end statements at a rational exponent above `3 - δ`. -/
theorem AllEdges.MinPlusSolved.endStatements {δ : ℝ} (h : AllEdges.MinPlusSolved δ) {rM : ℚ}
    (hM : 3 - δ < (rM : ℝ)) (hM0 : 0 ≤ rM) :
    EndStatement.MinPlusProduct.SolvedInTime rM ∧ EndStatement.APSP.SolvedInTime rM :=
  ⟨SolvedInTime.endStatement (h.minPlus _ hM) rfl hM0,
    SolvedInTime.endStatement (h.apsp _ hM) rfl hM0⟩

/-- **The (min,+)-product and APSP with pruned encodings**: every saving below
`R'_c(Γ(c)) Γ(c)/2`, for every `c ≥ 21`, with the whole saving. No hypothesis. -/
theorem minPlusSolved_pruned {c δ : ℝ} (hc : 21 ≤ c) (hδ0 : 0 ≤ δ)
    (hδ : δ < savingF (basePruned c) (Gam c)) : AllEdges.MinPlusSolved δ := by
  have hhalf : savingF (basePruned c) (Gam c) ≤ 1 / 2 :=
    savingF_le_half (basePruned_pos tac_linarith).le (Gam_pos tac_linarith).le
  exact AllEdges.minPlusSolved_of_explicitFrom AllEdges.CA_nonneg AllEdges.pairsFromAllEdges
    tac_linarith
    (explicitFrom_pruned hc hδ0 hδ AllEdges.lightModelAE rfl AllEdges.midHostRat_ae)

/-- The (min,+)-product and APSP in `O(n^2.99791)`, with pruned encodings and the all-edges host,
at `c = 22`. -/
theorem endStatements_allEdges_pruned :
    EndStatement.MinPlusProduct.SolvedInTime 2.99791 ∧ EndStatement.APSP.SolvedInTime 2.99791 :=
  (minPlusSolved_pruned (c := 22) tac_norm_num tac_norm_num
    savingF_pruned_gt).endStatements tac_norm_num tac_norm_num

/-- **The (min,+)-product in `O(n^2.99791)` steps on the word RAM.** No hypothesis. -/
theorem minPlus_allEdges_pruned :
    EndStatement.MinPlusProduct.SolvedInTime 2.99791 :=
  endStatements_allEdges_pruned.1

/-- **APSP in `O(n^2.99791)` steps on the word RAM.** No hypothesis. -/
theorem apsp_allEdges_pruned :
    EndStatement.APSP.SolvedInTime 2.99791 :=
  endStatements_allEdges_pruned.2

end ImprovedExponents