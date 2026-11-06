module

public import GradedNear.Defs

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

@[expose] public section

namespace GradedNear.Cert

/-- The relaxed linear constraint of row `k` for case `c` on the box interval `[a, b]`. -/
def RelaxHolds (L : Leaf) (x : Fin L.cols.length → ℝ) (k : ℕ) (a b : ℤ) (c : ℕ) : Prop :=
  ∑ j, ((colCost ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1) a b c : ℤ) : ℝ) *
      x j ≤ ((rowBudget (L.rows.getD k ⟨1, []⟩) a b c : ℤ) : ℝ)

lemma S_pos : (0 : ℝ) < S := by norm_num [S]

/-- Floor division by a positive integer is at most real division. -/
lemma cast_ediv_le (a b : ℤ) (hb : 0 < b) : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  rw [le_div_iff₀ (mod_cast hb)]
  exact_mod_cast Int.ediv_mul_le a hb.ne'

lemma wf {L : Leaf} (hwf : wellFormed L = true) (k : ℕ) :
    (∀ j : Fin L.cols.length, 0 < (L.cols.get j).D.getD k 1) ∧ 0 < (L.rows.getD k ⟨1, []⟩).d ∧
      ∀ t ∈ (L.rows.getD k ⟨1, []⟩).fam, 0 ≤ t.1 ∧ 0 < t.2.2 := by
  simp [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  refine ⟨fun j => ?_, ?_⟩ <;> rw [List.getD_eq_getElem?_getD]
  · cases h : (L.cols.get j).D[k]?
    exacts [Int.one_pos, (hwf.1 _ (List.get_mem _ j)).2 _ (List.mem_of_getElem? h)]
  · grind

/-- Column costs at most `S` times exact terms `f j`, an exact row inequality, and a budget at
least `S` times the exact budget give the relaxed row. -/
lemma relax_of {L : Leaf} {x : Fin L.cols.length → ℝ} {k : ℕ} {a b : ℤ} {c : ℕ}
    {f : Fin L.cols.length → ℝ} {F Q : ℝ} (h : ∑ j, f j + F + Q ≤ 1)
    (hf : ∀ j, ((colCost ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1) a b c : ℤ) : ℝ) *
      x j ≤ S * f j)
    (hB : S * (1 - Q - F) ≤ rowBudget (L.rows.getD k ⟨1, []⟩) a b c) : RelaxHolds L x k a b c :=
  (Finset.sum_le_sum fun j _ => hf j).trans (by
    rw [← Finset.mul_sum]; linarith [mul_le_mul_of_nonneg_left h S_pos.le])

/-! ### First order -/

/-- The first-order bound for one term: with `Sτ ≤ sh` and `n ≥ 0`,
`⌊n (v - sh)₊² / D⌋ ≤ S · n (v/S - τ)₊² / (D/S)`. -/
lemma first_le (n v D sh : ℤ) (hn : 0 ≤ n) (hD : 0 < D) {τ : ℝ} (hsh : (S : ℝ) * τ ≤ sh) :
    (((n * (max (v - sh) 0) ^ 2) / D : ℤ) : ℝ) ≤
      S * ((n : ℝ) * (max 0 ((v : ℝ) / S - τ)) ^ 2 / ((D : ℝ) / S)) := by
  have hS := S_pos
  grw [cast_ediv_le _ _ hD]
  push_cast
  grw [← hsh]
  rw [div_sub' hS.ne', ← zero_div (S : ℝ), max_div_div_right hS.le, max_comm]
  field_simp
  simp

theorem relax_first (L : Leaf) (hwf : wellFormed L = true) (x : Fin L.cols.length → ℝ)
    (hx : ∀ j, 0 ≤ x j) {k : ℕ} {a b : ℤ} (ha : 0 ≤ a) {τ : ℝ}
    (hτa : (a : ℝ) ≤ τ * TS) (hτb : τ * TS ≤ b)
    (hrow : rowLHS L x k τ ≤ 1 - τ ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S)) :
    RelaxHolds L x k a b 2 := by
  obtain ⟨hD, hd, hfam⟩ := wf hwf k
  have hsh : (S : ℝ) * τ ≤ ((b * (S / TS) : ℤ) : ℝ) := by norm_num [S, TS] at *; linarith
  refine relax_of (le_sub_iff_add_le.1 hrow) (fun j => ?_) ?_
  · rw [colCost, if_pos rfl, ← one_mul (max _ _ ^ 2)]
    exact (mul_le_mul_of_nonneg_right (first_le 1 _ _ _ zero_le_one (hD j) hsh) (hx j)).trans_eq
      (by grind)
  rw [rowBudget, if_pos rfl, Int.cast_sub, Int.cast_sub, mul_sub, mul_sub, mul_one]
  gcongr _ - ?_ - ?_
  · grw [cast_ediv_le _ _ (mul_pos (by norm_num [TS]) hd)]
    push_cast
    rw [div_le_iff₀ (by norm_num [TS]; positivity)]
    field_simp
    nlinarith [mul_self_le_mul_self (mod_cast ha) hτa]
  · rw [Int.cast_list_sum, List.map_map, ← List.sum_map_mul_left]
    grind [List.sum_le_sum, first_le]

/-! ### The tangent line -/

/-- The tangent line at `m` of `t ↦ (w - t)₊²`, evaluated at `t = m + s`. -/
noncomputable def tgt (w m s : ℝ) : ℝ := (max 0 (w - m)) ^ 2 - 2 * max 0 (w - m) * s

/-- `t ↦ (w - t)₊²` is convex: it lies above its tangent line at `m`. -/
lemma tangent_ineq (w m t : ℝ) : tgt w m (t - m) ≤ (max 0 (w - t)) ^ 2 := by
  unfold tgt
  rcases le_total (w - m) 0 with h1 | h1
  · simp_all
  · rw [max_eq_right h1]
    nlinarith [sq_nonneg (max 0 (w - t) - (w - m)), mul_nonneg h1 (sub_nonneg.2 (le_max_right 0 (w - t)))]

/-- Midpoint `(a + b)/(2 TS)` of the box interval, in threshold units. -/
noncomputable def mid (a b : ℤ) : ℝ := ((a : ℝ) + b) / (2 * TS)

/-- Half-width `(b - a)/(2 TS)` of the box interval, in threshold units. -/
noncomputable def hw (a b : ℤ) : ℝ := ((b : ℝ) - a) / (2 * TS)

/-- The endpoint offset of case `c`: `-h` for `c = 0`, `+h` for `c = 1`. -/
noncomputable def sgn (a b : ℤ) (c : ℕ) : ℝ := (2 * (c : ℝ) - 1) * hw a b

/-- Family part of the tangent line. -/
noncomputable def famT (r : RowHead) (m s : ℝ) : ℝ :=
  (r.fam.map fun t => (t.1 : ℝ) * tgt ((t.2.1 : ℝ) / S) m s / ((t.2.2 : ℝ) / S)).sum

/-- Tangent line of `τ ↦ τ²/(d/S)` at `m`, evaluated at `m + s`. -/
noncomputable def quadT (r : RowHead) (m s : ℝ) : ℝ := (m ^ 2 + 2 * m * s) / ((r.d : ℝ) / S)

/-- The tangent line at `m` of `τ ↦ rowLHS + τ²/(d/S)`, evaluated at `m + s`. -/
noncomputable def tline (L : Leaf) (x : Fin L.cols.length → ℝ) (k : ℕ) (m s : ℝ) : ℝ :=
  ∑ j, x j * tgt (((L.cols.get j).v.getD k 0 : ℝ) / S) m s / (((L.cols.get j).D.getD k 1 : ℝ) / S) +
    famT (L.rows.getD k ⟨1, []⟩) m s + quadT (L.rows.getD k ⟨1, []⟩) m s

lemma tline_affine (L : Leaf) (x : Fin L.cols.length → ℝ) (k : ℕ) (m s : ℝ) :
    tline L x k m s = (1 - s) * tline L x k m 0 + s * tline L x k m 1 := by
  have (w : ℝ) : tgt w m s = (1 - s) * tgt w m 0 + s * tgt w m 1 := by grind [tgt]
  simp [tline, famT, quadT, this, mul_add, add_div, mul_left_comm _ (1 - s), mul_left_comm _ s,
    mul_div_assoc, Finset.sum_add_distrib, List.sum_map_add, ← Finset.mul_sum, List.sum_map_mul_left]
  ring

/-- The tangent line lies below the convex row function (needs `x ≥ 0` and `n ≥ 0`). -/
lemma tline_le (L : Leaf) (hwf : wellFormed L = true) (x : Fin L.cols.length → ℝ)
    (hx : ∀ j, 0 ≤ x j) (k : ℕ) (m τ : ℝ) :
    tline L x k m (τ - m) ≤ rowLHS L x k τ + τ ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S) := by
  obtain ⟨hD, hd, hfam⟩ := wf hwf k
  have hS := S_pos
  unfold tline famT quadT rowLHS
  gcongr with j
  · exact div_nonneg (mod_cast (hD j).le) hS.le
  · grind
  · exact tangent_ineq ..
  · refine List.sum_le_sum fun t ht => ?_
    gcongr
    · exact div_nonneg (mod_cast (hfam t ht).2.le) hS.le
    · exact_mod_cast (hfam t ht).1
    · exact tangent_ineq ..
  · nlinarith [sq_nonneg (τ - m)]

/-! ### Tangent costs and budgets -/

/-- The tangent-case column cost is at most `S²` times the exact tangent term over `D`. -/
lemma colCost_tangent_le (v D a b : ℤ) (hD : 0 < D) (c : ℕ) (hc : c = 0 ∨ c = 1) :
    ((colCost v D a b c : ℤ) : ℝ) ≤ S * tgt ((v : ℝ) / S) (mid a b) (sgn a b c) * S / D := by
  have hS := S_pos
  rw [colCost, if_neg (by omega)]
  refine (cast_ediv_le _ _ hD).trans (div_le_div_of_nonneg_right ?_ (mod_cast hD.le))
  unfold tangentCost tgt sgn
  rw [show (v : ℝ) / S - mid a b = ((v - (a + b) * HS : ℤ) : ℝ) / S by simp [mid, S, TS, HS]; ring, show hw a b = (((b - a) * HS : ℤ) : ℝ) / S by simp [hw, S, TS, HS]; ring]
  dsimp only
  split_ifs with hx
  · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (mod_cast hx) hS.le)]; simp
  all_goals
    rw [max_eq_right (div_nonneg (mod_cast (not_le.1 hx).le) hS.le), Int.cast_mul]
    refine mul_le_mul_of_nonneg_right ((cast_ediv_le _ _ (by simp_all)).trans_eq ?_) hS.le
    rcases hc with rfl | rfl <;> norm_num at * <;> field_simp <;> ring

lemma tangentExact_eq (w m h : ℚ) (c : ℕ) (hc : c = 0 ∨ c = 1) :
    (tangentExact w m h c : ℝ) = tgt w m ((2 * c - 1) * h) := by
  unfold tangentExact tgt
  rcases hc with rfl | rfl <;> simp only [max_comm (0 : ℝ)] <;> split_ifs <;> push_cast <;> simp_all <;> ring

/-- The tangent-case budget is at least `S` times the exact budget. -/
lemma rowBudget_tangent_ge (r : RowHead) (a b : ℤ) (c : ℕ) (hc : c = 0 ∨ c = 1) :
    S * (1 - quadT r (mid a b) (sgn a b c) - famT r (mid a b) (sgn a b c)) ≤
      ((rowBudget r a b c : ℤ) : ℝ) := by
  rw [rowBudget, if_neg (by omega)]
  refine (le_of_eq ?_).trans ((Rat.cast_le.2 (Int.le_ceil _)).trans_eq (Rat.cast_intCast _))
  unfold famT quadT sgn mid hw
  push_cast [tangentExact_eq _ _ _ c hc, List.map_map, Function.comp_def]
  rcases hc with rfl | rfl <;> simp <;> ring

theorem relax_tangent (L : Leaf) (hwf : wellFormed L = true) (x : Fin L.cols.length → ℝ)
    (hx : ∀ j, 0 ≤ x j) {k : ℕ} {a b : ℤ} {τ : ℝ}
    (hτa : (a : ℝ) ≤ τ * TS) (hτb : τ * TS ≤ b)
    (hrow : rowLHS L x k τ ≤ 1 - τ ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S)) :
    RelaxHolds L x k a b 0 ∨ RelaxHolds L x k a b 1 := by
  have h1 : -hw a b ≤ τ - mid a b ∧ τ - mid a b ≤ hw a b := by
    norm_num [mid, hw, TS] at *; constructor <;> linarith
  have hB := tline_le L hwf x hx k (mid a b) τ
  rw [tline_affine] at hB
  have key : ∀ c, c = 0 ∨ c = 1 → tline L x k (mid a b) (sgn a b c) ≤ 1 → RelaxHolds L x k a b c :=
    fun c hc h => relax_of h (fun j => (colCost_tangent_le _ _ a b ((wf hwf k).1 j) c hc |>
      mul_le_mul_of_nonneg_right <| hx j).trans_eq (by field_simp)) (rowBudget_tangent_ge _ a b c hc)
  rcases le_total (tline L x k (mid a b) 0) (tline L x k (mid a b) 1) with h | h
  exacts [.inl (key 0 (.inl rfl) (by rw [tline_affine]; norm_num [sgn]; nlinarith)),
    .inr (key 1 (.inr rfl) (by rw [tline_affine]; norm_num [sgn]; nlinarith))]

end GradedNear.Cert
