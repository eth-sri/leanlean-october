
import GradedNear.Defs
import GradedNear.Tactics

/-!
# Soundness of the row relaxations

On a box interval `[a, b]` (ticks) containing `τ·TS`, a near row at the actual threshold `τ`
implies the first-order linear relaxation (case 2), and one of the two tangent relaxations
(cases 0, 1): the row's left side plus `τ²/(d/S)` is convex in `τ`, so its tangent line at the
midpoint is below it, and an affine function that is `≤ 1` somewhere on `[a, b]` is `≤ 1` at an
endpoint. Integer costs are floored and budgets ceiled, in the safe direction.

Both relaxations need the family counts `n ≥ 0` (part of `wellFormed`): the first-order budget
evaluates the family terms at the upper threshold `b`, and the tangent budget replaces each family
term by its tangent line. Without `n ≥ 0` both statements are false. The hypothesis
`k < L.rows.length` is not used: out-of-range rows default to `⟨1, []⟩`. Helpers are in
`GradedNear.Cert.RelaxAux`.
-/

namespace GradedNear.Cert

variable (L : Leaf) (hwf : wellFormed L = true) (x : Fin L.cols.length → ℝ)
  (hx : ∀ j, 0 ≤ x j)

/-- The relaxed linear constraint of row `k` for case `c` on the box interval `[a, b]`. -/
def RelaxHolds (k : ℕ) (a b : ℤ) (c : ℕ) : Prop :=
  ∑ j, ↑ (colCost (L.feature j k) (L.diagonal j k) a b c) *
      x j ≤ ↑ (rowBudget (L.row k) a b c)

namespace RelaxAux

/-! ### Constants and rounding -/

lemma S_pos_int : (0 : ℤ) < S := by decide

lemma S_pos : (0 : ℝ) < S := by exact_mod_cast S_pos_int

/-- Floor division by a positive integer is at most real division. -/
lemma cast_ediv_le (a b : ℤ) (hb : 0 < b) : ((a / b : ℤ) : ℝ) ≤ ↑a / b := by
  rw [le_div_iff₀ (by simp_all)]
  exact_mod_cast Int.ediv_mul_le a (ne_of_gt hb)

/-! ### Well-formedness -/

section
variable {L}
include hwf

lemma wf_colD (j : Fin L.cols.length) (k : ℕ) :
    0 < L.diagonal j k := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true] at hwf

  grind [List.getElem_mem]

lemma wf_row (k : ℕ) :
    0 < (L.row k).d ∧ ∀ t ∈ (L.row k).fam, 0 ≤ t.1 ∧ 0 < t.2.2 := by
  unfold wellFormed at hwf
  grind

end

/-! ### Sums -/

/-! ### First order -/

/-- The first-order bound for one term: with `Sτ ≤ sh` and `n ≥ 0`,
`⌊n (v - sh)₊² / D⌋ ≤ S · n (v/S - τ)₊² / (D/S)`. -/
lemma first_le (n v D sh : ℤ) (hn : 0 ≤ n) (hD : 0 < D) {τ : ℝ} (hsh : ↑S * τ ≤ sh) :
    ((n * max (v - sh) 0 ^ 2 / D : ℤ) : ℝ) ≤
      S * (↑n * rowSlack v τ ^ 2 / unscale D ) := by
  have hS := S_pos

  refine (cast_ediv_le _ _ hD).trans ?_
  push_cast
  have hM : max ((v : ℝ) - sh) 0 ≤ S * rowSlack v τ := by
    rw [mul_max_of_nonneg _ _ hS.le, mul_zero, max_comm]
    gcongr
    field_simp
    nlinarith
  grw [hM]
  apply le_of_eq
  field_simp

/-! ### The tangent line -/

/-- The tangent line at `m` of `t ↦ (w - t)₊²`, evaluated at `t = m + s`. -/
def tgt (w m s : ℝ) : ℝ := max 0 (w - m) ^ 2 - 2 * max 0 (w - m) * s

/-- `t ↦ (w - t)₊²` is convex: it lies above its tangent line at `m`. -/
lemma tangent_ineq (w m t : ℝ) : tgt w m (t - m) ≤ max 0 (w - t) ^ 2 := by
  unfold tgt
  simp only [max_def]
  split_ifs <;> nlinarith [sq_nonneg (t - m)]

/-- The exact family term of `rowBudget`, cast to `ℝ`. -/
lemma tangentExact_cast (w m h : ℚ) (c : ℕ) (hc : c = 0 ∨ c = 1) :
    ↑ (tangentExact w m h c) =
      tgt ↑w ↑m ((2 * ↑c - 1) * ↑h) := by
  rcases hc with rfl | rfl <;>
    norm_num [tangentExact, tgt] <;> (try split_ifs) <;> first | (push_cast; grind) | simp_all

end RelaxAux

include hwf hx
theorem relax_first {k : ℕ} {a b : ℤ} (ha : 0 ≤ a) {τ : ℝ}
    (hτa : ↑a ≤ τ * TS) (hτb : τ * TS ≤ b)
    (hrow : rowLHS L x k τ ≤ 1 - τ ^ 2 / unscale (L.row k).d ) :
    RelaxHolds L x k a b 2 := by
  obtain ⟨hd, hfam⟩ := RelaxAux.wf_row hwf k


  -- the first-order shift `sh = b·(S/TS)` dominates `Sτ`
  have hsh : ↑S * τ ≤ ((b * (S / TS) : ℤ) : ℝ) := by
    norm_num [S, TS] at hτb ⊢
    linarith
  have hcols : ∑ j, ↑ (colCost (L.feature j k) (L.diagonal j k) a b 2) * x j ≤ S * ∑ j, x j * rowSlack (L.feature j k) τ ^ 2 /
         unscale (L.diagonal j k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have h := RelaxAux.first_le 1 (L.feature j k) _ _ zero_le_one
      (RelaxAux.wf_colD hwf j k) hsh
    simp only [Int.cast_one, one_mul] at h

    calc _ ≤ S * (rowSlack (L.feature j k) τ ^ 2 /
           unscale (L.diagonal j k) ) * x j :=  by bound
      _ = _ := by ring
  have hfamb :=
    List.sum_le_sum (l := (L.row k).fam) fun t ht =>
      RelaxAux.first_le t.1 t.2.1 t.2.2 _ (hfam t ht).1 (hfam t ht).2 hsh
  rw [List.sum_map_mul_left] at hfamb
  have hquad : ((S * S * a * a / (TS * TS * (L.row k).d) : ℤ) : ℝ) ≤
      S * (τ ^ 2 / unscale (L.row k).d ) := by

    refine (RelaxAux.cast_ediv_le _ _ (by norm_num [TS]; positivity)).trans ?_

    have h1 := mul_self_le_mul_self (by positivity) hτa
    norm_num only [S, TS, Int.cast_mul, Int.cast_ofNat] at h1 ⊢
    field_simp; nlinarith

  have key := mul_le_mul_of_nonneg_left hrow RelaxAux.S_pos.le
  unfold rowLHS at key

  unfold RelaxHolds
  rw [rowBudget, ite_eq_left rfl, Int.cast_sub, Int.cast_sub]
  push_cast
  grind [Function.comp_def]

open RelaxAux

theorem relax_tangent {k : ℕ} {a b : ℤ} {τ : ℝ}
    (hτa : ↑a ≤ τ * TS) (hτb : τ * TS ≤ b)
    (hrow : rowLHS L x k τ ≤ 1 - τ ^ 2 / unscale (L.row k).d ) :
    RelaxHolds L x k a b 0 ∨ RelaxHolds L x k a b 1 := by
  let mid : ℝ := (↑a + b) / (2 * TS)
  let hw : ℝ := (↑b - a) / (2 * TS)
  let sgn (c : ℕ) : ℝ := (2 * ↑c - 1) * hw
  have tangentCost_le (v : ℤ) (c : ℕ) (hc : c = 0 ∨ c = 1) :
      ↑ (tangentCost v (a + b) (b - a) c) ≤ S * tgt unscale v mid (sgn c) := by
    clear * - hc
    rcases hc with rfl | rfl <;> dsimp [tangentCost, tgt] <;> split_ifs
    all_goals
      try refine (cast_ediv_le _ _ S_pos_int).trans ?_
      rify at * <;> norm_num [S, HS, TS, mid, sgn, hw, max_def] at * <;> split_ifs <;>
        first
        | nlinarith
        | have hz : (v:ℝ) / 10000000000000000 - ((a:ℝ)+b) / 2000000 = 0 := by linarith
          simp_all

  let colT s :=
    ∑ j, x j * RelaxAux.tgt unscale (L.feature j k) mid s / unscale (L.diagonal j k)
  let famT s :=
    ((L.row k).fam.map fun t => (t.1 : ℝ) * RelaxAux.tgt unscale t.2.1 mid s / unscale t.2.2 ).sum
  let quadT s :=
    (mid ^ 2 + 2 * mid * s) / unscale (L.row k).d
  let tline s := colT s + famT s + quadT s
  have hB : tline (τ - mid) ≤
      rowLHS L x k τ + τ ^ 2 / unscale (L.row k).d := by
    obtain ⟨hd, hfam⟩ := RelaxAux.wf_row hwf k
    have hS := RelaxAux.S_pos
    dsimp only [tline, colT, famT, quadT]
    unfold rowLHS
    gcongr
    · exact div_nonneg (by exact_mod_cast (RelaxAux.wf_colD hwf _ _).le) hS.le
    · exact hx _
    · grind [GradedNear.Cert.RelaxAux.tangent_ineq]
    · refine List.sum_le_sum fun t ht => ?_
      gcongr
      · exact div_nonneg (by exact_mod_cast (hfam t ht).2.le) hS.le
      · exact_mod_cast (hfam t ht).1
      grind [GradedNear.Cert.RelaxAux.tangent_ineq]
    · nlinarith [sq_nonneg (τ - mid)]
  have rowBudget_tangent_ge (c : ℕ) (hc : c = 0 ∨ c = 1) :
      S * (1 - famT (sgn c) - quadT (sgn c)) ≤
        ↑(rowBudget (L.row k) a b c) := by
    rw [rowBudget, ite_eq_right (by omega)]
    dsimp only
    refine le_trans (le_of_eq ?_) (by rewrite [← Rat.ceil_cast (α := ℝ)]; exact Int.le_ceil _)
    push_cast
    simp only [List.map_map, Function.comp_def]
    push_cast
    simp_rw [RelaxAux.tangentExact_cast _ _ _ c hc]
    push_cast
    dsimp only [famT, quadT]
    dsimp only [sgn, mid, hw]
    rcases hc with rfl | rfl <;> norm_num <;> sum_ring
  have relax_case (c : ℕ) (hc : c = 0 ∨ c = 1)
      (hG : tline (sgn c) ≤ 1) : RelaxHolds L x k a b c := by
    have hS := RelaxAux.S_pos
    have hcols : ∑ j, ↑ (colCost (L.feature j k) (L.diagonal j k) a b c) * x j ≤ S * colT (sgn c) := by
      dsimp only [colT]
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have hD := RelaxAux.wf_colD hwf j k

      have hxj := hx j
      rw [colCost, ite_eq_right (by omega)]
      grw [RelaxAux.cast_ediv_le _ _ hD]
      rw [Int.cast_mul]
      grw [tangentCost_le (L.feature j k) c hc]
      apply le_of_eq
      field_simp
    have hbud := rowBudget_tangent_ge c hc
    dsimp only [tline] at hG
    unfold RelaxHolds
    nlinarith
  have hT : (0 : ℝ) < TS := by norm_num [TS]
  have hG : tline (τ - mid) ≤ 1 := by linarith
  obtain ⟨h1, h2⟩ : -hw ≤ τ - mid ∧ τ - mid ≤ hw := by
    dsimp [hw, mid]
    constructor <;> field_simp <;> nlinarith
  have he s : tline s = tline 0 + s * (tline 1 - tline 0) := by
    dsimp only [tline, colT, famT, quadT]
    unfold RelaxAux.tgt
    sum_ring
  rw [he (τ - mid)] at hG
  rcases le_total 0 (tline 1 - tline 0) with hQ | hQ
  · left
    apply relax_case 0 (Or.inl rfl)
    rw [he (sgn 0)]
    norm_num [sgn]
    nlinarith
  · right
    apply relax_case 1 (Or.inr rfl)
    rw [he (sgn 1)]
    norm_num [sgn]
    nlinarith

end GradedNear.Cert
