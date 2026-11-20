module

public import GradedNear.Cert.Rows

/-!
# Soundness of the row relaxations

Normalize costs and budgets by `S` to compare directly with the feasible row. The first-order
case evaluates the hinge and the threshold square at opposite endpoints. For the tangent cases, the affine lower bound at the midpoint has
value at most `S` at one endpoint. Costs round down and budgets round up.
-/

@[expose] public section

namespace GradedNear.Cert

/-- The relaxed constraint on row `k`, box interval `[a,b]`, and case `c`. -/
def RelaxHolds (L : Leaf) (x : Fin L.cols.length → ℝ) (k : ℕ) (a b : ℤ) (c : ℕ) : Prop :=
  ∑ j, (colCost (featureAt (L.cols.get j) k) (diagAt (L.cols.get j) k) a b c : ℝ) * x j ≤
    (rowBudget (rowAt L k) a b c : ℝ)

lemma int_div_le (a b : ℤ) (hb : 0 < b) : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Int.ediv_mul_le a hb.ne'

lemma wf_col {L : Leaf} (h : wellFormed L = true) {c : Col} (hc : c ∈ L.cols) :
    (c.v.length = L.rows.length ∧ c.D.length = L.rows.length) ∧ ∀ D ∈ c.D, 0 < D := by
  grind [wellFormed]

private noncomputable def cols (L : Leaf) (x : Fin L.cols.length → ℝ) (k : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ j, x j * f (unscaled (featureAt (L.cols.get j) k)) / (unscaled (diagAt (L.cols.get j) k))

private noncomputable def fam (r : RowHead) (f : ℝ → ℝ) : ℝ :=
  (r.fam.map fun t => (t.1 : ℝ) * f (unscaled (t.2.1)) / (unscaled (t.2.2))).sum

private noncomputable def hinge (t v : ℝ) : ℝ := max 0 (v - t)

private noncomputable def sq (t v : ℝ) : ℝ := hinge t v ^ 2

private lemma hinge_scale (v t : ℝ) : S * hinge t (v / S) = hinge (S * t) v := by
  rw [hinge, hinge, mul_max_of_nonneg _ _ S_pos.le, mul_zero, mul_sub, mul_div_cancel₀ _ S_pos.ne']

variable {L : Leaf} {x : Fin L.cols.length → ℝ} {k : ℕ} {a b : ℤ}

-- Combine termwise rounded costs with a bound for the exact row and rounded budget.
private lemma relax_of (hx : ∀ j, 0 ≤ x j) {c : ℕ} {f : ℝ → ℝ} {q : ℝ}
    (hc : ∀ j : Fin L.cols.length,
      unscaled (colCost (featureAt (L.cols.get j) k) (diagAt (L.cols.get j) k) a b c) ≤
        f (unscaled (featureAt (L.cols.get j) k)) / (unscaled (diagAt (L.cols.get j) k)))
    (hb : 1 - q - fam (rowAt L k) f ≤ unscaled (rowBudget (rowAt L k) a b c))
    (h : cols L x k f + fam (rowAt L k) f + q ≤ 1) : RelaxHolds L x k a b c := by
  unfold RelaxHolds
  apply (div_le_div_iff_of_pos_right S_pos).mp
  rw [Finset.sum_div]
  refine le_trans (b := cols L x k f) ?_ (by linarith)
  exact Finset.sum_le_sum fun j _ => by
    simpa only [mul_div_assoc, mul_comm _ (x j)] using mul_le_mul_of_nonneg_left (hc j) (hx j)

private lemma first_cost (n v D sh : ℤ) (hn : 0 ≤ n) (hD : 0 < D) {u : ℝ} (hh : S * u ≤ sh) :
    unscaled (n * max (v - sh) 0 ^ 2 / D) ≤ n * sq u (v / S) / (unscaled D) := by
  rw [div_le_iff₀ S_pos]
  refine (int_div_le _ _ hD).trans ?_
  simp only [sq, div_div_eq_mul_div]
  calc
    _ ≤ (n : ℝ) * hinge (S * u) v ^ 2 / D := by push_cast; rw [hinge, max_comm 0]; gcongr
    _ = _ := by rw [← hinge_scale]; ring

private noncomputable def tangent (m s v : ℝ) : ℝ := sq m v + s * (-2 * hinge m v)
section Endpoints
variable (a b : ℤ)

private noncomputable def mid : ℝ := ((a : ℝ) + b) / (2 * TS)
private noncomputable def half : ℝ := ((b : ℝ) - a) / (2 * TS)
private noncomputable def shift (c : ℕ) (h : ℝ) : ℝ := if c = 0 then -h else h

private lemma tangent_le (m u v : ℝ) : tangent m (u - m) v ≤ sq u v := by
  simp only [tangent, sq, hinge, max_def]
  split_ifs <;> nlinarith [sq_nonneg (u - m)]

-- The midpoint hinge can be evaluated either in threshold units or in input units.
private lemma tangentCost_eq (v m h : ℤ) (c : ℕ) :
    tangentCost v m h c = max 0 (v - m * HS) * (max 0 (v - m * HS) -
      2 * (if c = 0 then -(h * HS) else h * HS)) / S := by
  rw [max_comm 0]
  simp only [tangentCost, max_def]
  split_ifs <;> simp [sub_eq_add_neg]

private lemma tangent_cost (v D : ℤ) (c : ℕ) (hc : c ≠ 2) (hD : 0 < D) :
    unscaled (colCost v D a b c) ≤
      tangent (mid a b) (shift c (half a b)) (v / (S : ℝ)) / (unscaled D) := by
  rw [div_le_iff₀ S_pos, colCost, ite_eq_right hc]
  refine (int_div_le _ _ hD).trans ?_
  push_cast
  rw [div_div_eq_mul_div, div_mul_eq_mul_div]
  have := S_pos.le
  gcongr
  rw [tangentCost_eq]
  refine (int_div_le _ _ (by norm_num [S])).trans_eq ?_
  have hv : (S : ℝ) * hinge (mid a b) (v / S) = max 0 ((v : ℝ) - (a + b) * HS) := by
    rw [hinge_scale, hinge]
    congr 2
    norm_num [S, TS, HS, mid]
    ring
  push_cast
  rw [← hv]
  unfold tangent sq shift half
  split_ifs <;> norm_num [S, TS, HS] <;> ring

private lemma tangent_cast (v m h : ℚ) (c : ℕ) :
    (tangentExact v m h c : ℝ) = tangent m (shift c h) v := by
  unfold tangentExact tangent shift sq hinge
  dsimp only
  split_ifs <;> push_cast <;> rw [max_comm 0] <;> ring_nf
  simp_all

private lemma ceil_ge (q : ℚ) : (q : ℝ) ≤ (⌈q⌉ : ℝ) := by
  exact_mod_cast Int.le_ceil q

private lemma tangent_budget (r : RowHead) (c : ℕ) (hc : c ≠ 2) :
    1 - (mid a b ^ 2 + 2 * mid a b * shift c (half a b)) / (unscaled (r.d)) -
      fam r (tangent (mid a b) (shift c (half a b))) ≤ unscaled (rowBudget r a b c) := by
  rw [rowBudget, ite_eq_right hc, le_div_iff₀ S_pos]
  dsimp only
  refine (le_of_eq ?_).trans (ceil_ge _)
  push_cast [Rat.cast_list_sum, List.map_map, Function.comp_def, tangent_cast, mid, half, fam, shift]
  split_ifs <;> push_cast <;> ring_nf

end Endpoints

/-- A feasible row satisfies the first-order constraint or one of the two tangent constraints,
according to the prescribed order. -/
lemma relax_row (hwf : wellFormed L = true) (hx : ∀ j, 0 ≤ x j) (ha : 0 ≤ a) {τ : ℝ}
    (hτa : (a : ℝ) ≤ τ * TS) (hτb : τ * TS ≤ b)
    (hrow : rowLHS L x k τ ≤ 1 - τ ^ 2 / (unscaled ((rowAt L k).d))) (o : ℕ) :
    if o = 1 then RelaxHolds L x k a b 0 ∨ RelaxHolds L x k a b 1
    else RelaxHolds L x k a b 2 := by
  let r := rowAt L k
  let d := (r.d : ℝ) / S
  obtain ⟨hd, hf⟩ : 0 < r.d ∧ ∀ t ∈ r.fam, 0 ≤ t.1 ∧ 0 < t.2.2 := by
    dsimp only [r]
    grind [wellFormed]
  have hd' : 0 ≤ d := unscaled_nonneg hd.le
  have hDj (j : Fin L.cols.length) : 0 < diagAt (L.cols.get j) k := by
    have hD := (wf_col hwf (List.get_mem _ j)).2
    grind [List.getElem_mem]
  change cols L x k (sq τ) + fam r (sq τ) ≤ 1 - τ ^ 2 / d at hrow
  replace hrow := le_sub_iff_add_le.mp hrow
  split_ifs
  · let m := mid a b
    let G (s : ℝ) := cols L x k (tangent m s) + fam r (tangent m s) + (m ^ 2 + 2 * m * s) / d
    have hG : G (τ - m) ≤ 1 := by
      refine le_trans ?_ hrow
      dsimp only [G, cols, fam]
      gcongr with j
      · exact unscaled_nonneg (hDj j).le
      · exact hx j
      · exact tangent_le _ _ _
      · refine List.sum_le_sum fun t ht => ?_
        have hn : (0 : ℝ) ≤ t.1 := mod_cast (hf t ht).1
        gcongr
        · exact unscaled_nonneg (hf t ht).2.le
        · exact tangent_le _ _ _
      · nlinarith [sq_nonneg (τ - m)]
    have hAff s : G s = G 0 + s * (G 1 - G 0) := by
      simp only [G, cols, fam, tangent, zero_mul, one_mul, add_zero]
      simp_rw [mul_add, add_div, mul_left_comm _ s, mul_div_assoc s, Finset.sum_add_distrib,
        ← Finset.mul_sum, List.sum_map_add, List.sum_map_mul_left]
      ring
    have hb : τ - m ∈ Set.Icc (-half a b) (half a b) := by
      norm_num [m, half, mid, TS, Set.mem_Icc] at hτa hτb ⊢
      grind
    have get c (hc : c ≠ 2) (h : G (shift c (half a b)) ≤ 1) : RelaxHolds L x k a b c :=
      relax_of hx (fun j => tangent_cost a b _ _ c hc (hDj j)) (tangent_budget _ _ _ _ hc) h
    have hEnds : G (-half a b) ≤ 1 ∨ G (half a b) ≤ 1 := by
      rw [hAff (τ - m)] at hG
      rw [hAff (-half a b), hAff (half a b)]
      rcases le_total 0 (G 1 - G 0) with h | h
      · left; linarith only [hG, mul_le_mul_of_nonneg_right hb.1 h]
      · right; linarith only [hG, mul_le_mul_of_nonpos_right hb.2 h]
    exact hEnds.imp (get 0 (by decide)) (get 1 (by decide))
  · have hs : (S : ℝ) * τ ≤ (b * (S / TS) : ℤ) := by
      norm_num [S, TS] at hτb ⊢
      linarith
    refine relax_of (f := sq τ) (q := τ ^ 2 / d) hx (fun j => ?_) ?_ hrow
    · simpa [colCost] using first_cost 1 _ _ _ zero_le_one (hDj j) hs
    · let costs := r.fam.map fun t => t.1 * max (t.2.1 - b * (S / TS)) 0 ^ 2 / t.2.2
      have hf' : (costs.sum : ℝ) / S ≤ fam r (sq τ) := by
        dsimp [costs]
        rw [Int.cast_list_sum, List.map_map, div_eq_mul_inv, ← List.sum_map_mul_right, fam]
        exact List.sum_le_sum fun t ht => first_cost _ _ _ _ (hf t ht).1 (hf t ht).2 hs
      have hq : unscaled (S * S * a * a / (TS * TS * r.d)) ≤ τ ^ 2 / d := by
        rw [div_le_iff₀ S_pos]
        refine (int_div_le _ _ (mul_pos (by norm_num [TS]) hd)).trans ?_
        have h0 : (0 : ℝ) ≤ a := mod_cast ha
        have hD : (0 : ℝ) < r.d := mod_cast hd
        norm_num [d, S, TS, div_mul_eq_mul_div] at hτa ⊢
        have hsq := pow_le_pow_left₀ h0 hτa 2
        field_simp [hD]
        nlinarith only [hsq, mul_le_mul_of_nonneg_right hsq hD.le]
      rw [rowBudget, ite_eq_left rfl, Int.cast_sub, Int.cast_sub, sub_div, sub_div, div_self S_pos.ne']
      linarith only [hf', hq]

end GradedNear.Cert
