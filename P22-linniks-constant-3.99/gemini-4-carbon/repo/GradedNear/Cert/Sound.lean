module

public import GradedNear.Defs

@[expose] public section

namespace GradedNear.Cert

open Finset

noncomputable section

local notation "cv" L:arg j:arg k:arg => List.getD (Col.v (List.get (Leaf.cols L) j)) k 0
local notation "cD" L:arg j:arg k:arg => List.getD (Col.D (List.get (Leaf.cols L) j)) k 1
local notation "rh" L:arg k:arg => List.getD (Leaf.rows L) k ⟨1, []⟩

lemma term_le {v v' D D' τ : ℝ} (hv : v ≤ v' ∨ v ≤ 0) (hτ : 0 ≤ τ) (hD' : 0 < D')
    (hDD : D' ≤ D) : max 0 (v - τ) ^ 2 / D ≤ max 0 (v' - τ) ^ 2 / D' := by
  rcases hv with hv | hv
  · gcongr
  · rw [max_eq_left (by linarith)]; simp; positivity

theorem near_row_of_bins (L : Leaf) k {ι : Type*} [Fintype ι] (v Dg : ι → ℝ) d τ
    (hDg : ∀ j, 0 < Dg j) (hd : 0 < d) (hτ0 : 0 ≤ τ) (hτd : τ ≤ Real.sqrt d)
    (hT : ∑ j, max 0 (v j - τ) ^ 2 / Dg j ≤ 1 - τ ^ 2 / d)
    (bin : _ → Option (_ ⊕ _))
    (hcol : ∀ j c, bin j = some (.inl c) →
      (cv L c k / S ≤ v j ∨ cv L c k ≤ 0) ∧ Dg j ≤ cD L c k / S)
    (hfam : ∀ j i, bin j = some (.inr i) →
      (((rh L k).fam.get i).2.1 / S ≤ v j ∨ ((rh L k).fam.get i).2.1 ≤ 0) ∧
        Dg j ≤ ((rh L k).fam.get i).2.2 / S)
    (hfamD : ∀ i, 0 < ((rh L k).fam.get i).2.2)
    (hn : ∀ i, ((rh L k).fam.get i).1 ≤ (#(univ.filter fun j => bin j = some (.inr i)) : ℝ))
    (hdrow : d ≤ (rh L k).d / S)
    (x : _ → ℝ) (hx0 : ∀ c, 0 ≤ x c)
    (hx : ∀ c, 0 < cv L c k → x c ≤ #(univ.filter fun j => bin j = some (.inl c))) :
    0 ≤ τ ∧ τ ^ 2 ≤ (rh L k).d / S ∧ rowLHS L x k τ ≤ 1 - τ ^ 2 / ((rh L k).d / S) := by
  have hS : (0 : ℝ) < S := by norm_num [S]
  refine ⟨hτ0, by grw [hτd, Real.sq_sqrt hd.le, hdrow], ?_⟩
  have hbnd (s : Finset ι) (z : ℝ) (vi Di : ℤ) (h1 : 0 < Di ∨ 0 ≤ z) (h2 : 0 < vi → z ≤ #s)
      (h3 : ∀ j ∈ s, (vi / S ≤ v j ∨ vi ≤ 0) ∧ Dg j ≤ Di / S) :
      z * max 0 (vi / S - τ) ^ 2 / (Di / S) ≤ ∑ j ∈ s, max 0 (v j - τ) ^ 2 / Dg j := by
    have hs0 : 0 ≤ ∑ j ∈ s, max 0 (v j - τ) ^ 2 / Dg j :=
      sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hDg j).le
    by_cases hvi : vi ≤ 0
    · rw [max_eq_left (by grw [Int.cast_nonpos.2 hvi]; simp [hτ0])]
      simpa using hs0
    rcases eq_or_ne z 0 with rfl | hz
    · simpa using hs0
    have hzp := h2 (not_le.1 hvi)
    have hD0 : 0 ≤ (Di : ℝ) / S := h1.elim (fun h => by positivity) fun hz0 =>
      let ⟨j₀, hj₀⟩ := card_pos.1 (by exact_mod_cast (lt_of_le_of_ne hz0 hz.symm).trans_le hzp)
      (hDg j₀).le.trans (h3 j₀ hj₀).2
    grw [mul_div_assoc, hzp]
    simpa using sum_le_sum fun j hj => term_le ((h3 j hj).1.imp_right fun h =>
      by grw [Int.cast_nonpos.2 h]; simp) hτ0 (hDg j) (h3 j hj).2
  rw [← sum_fiberwise univ bin, Fintype.sum_option, Fintype.sum_sum_type] at hT
  rw [rowLHS, ← Fin.sum_univ_fun_getElem]
  have h0 : 0 ≤ ∑ j ∈ univ.filter (bin · = none), max 0 (v j - τ) ^ 2 / Dg j :=
    sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hDg j).le
  have h1 := sum_le_sum fun c (_ : c ∈ univ) =>
    hbnd _ _ _ _ (.inr (hx0 c)) (hx c) fun j hj => hcol j c (mem_filter.1 hj).2
  have h2 := sum_le_sum fun i (_ : i ∈ univ) =>
    hbnd _ _ _ _ (.inl (hfamD i)) (fun _ => hn i) fun j hj => hfam j i (mem_filter.1 hj).2
  simp only [List.get_eq_getElem] at h2
  grw [← hdrow]; linarith

private abbrev bk (box : List (ℤ × ℤ)) k := box.getD k (0, 0)

private def RelaxHolds (L : Leaf) (x : Fin L.cols.length → ℝ) k a b c :=
  ∑ j, (colCost (cv L j k) (cD L j k) a b c : ℝ) * x j ≤ rowBudget (rh L k) a b c

private lemma cast_ediv_le {a b : ℤ} (hb : 0 < b) : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]; exact_mod_cast Int.ediv_mul_le a hb.ne'

private lemma wf_col {L} (hwf : wellFormed L = true) {c} (hc : c ∈ L.cols) :
    c.v.length = L.rows.length ∧ c.D.length = L.rows.length ∧ ∀ y ∈ c.D, 0 < y := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc] at hwf
  exact hwf.1 c hc

private lemma wf_colD {L} (hwf : wellFormed L = true) j k : 0 < cD L j k := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (L.cols.get j).D[k]? with
  | none => decide
  | some y => exact (wf_col hwf (List.get_mem _ j)).2.2 y (List.mem_of_getElem? h)

private lemma wf_row {L} (hwf : wellFormed L = true) k :
    0 < (rh L k).d ∧ ∀ t ∈ (rh L k).fam, 0 ≤ t.1 ∧ 0 < t.2.2 := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  rw [List.getD_eq_getElem?_getD]
  cases h : L.rows[k]? with
  | none => simp
  | some r => exact hwf.2 r (List.mem_of_getElem? h)

private lemma first_le {n v D sh : ℤ} (hn : 0 ≤ n) (hD : 0 < D) {τ : ℝ} (hsh : S * τ ≤ sh) :
    ((n * max (v - sh) 0 ^ 2 / D : ℤ) : ℝ) ≤ S * (n * max 0 (v / S - τ) ^ 2 / (D / S)) := by
  have hS : (0 : ℝ) < S := by norm_num [S]
  refine (cast_ediv_le hD).trans ?_; push_cast
  have hM : max ((v : ℝ) - sh) 0 ≤ S * max 0 (v / S - τ) :=
    max_le (by linarith [mul_le_mul_of_nonneg_left (le_max_right 0 ((v : ℝ) / S - τ)) hS.le,
        mul_sub (S : ℝ) (v / S) τ, mul_div_cancel₀ (v : ℝ) hS.ne']) (by positivity)
  have : (0 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) ≤ D := by exact_mod_cast hD.le
  grw [hM]; rw [div_div_eq_mul_div]; exact le_of_eq (by ring)

private abbrev tgt (w m s : ℝ) := max 0 (w - m) ^ 2 - 2 * max 0 (w - m) * s
private abbrev mid (a b : ℤ) : ℝ := (a + b) / (2 * TS)
private abbrev hw (a b : ℤ) : ℝ := (b - a) / (2 * TS)
private abbrev sgn (a b : ℤ) (c : ℕ) : ℝ := (2 * c - 1) * hw a b

private lemma colCost_tangent_le (v D a b : ℤ) (hD : 0 < D) {c} (hc : c = 0 ∨ c = 1) :
    (colCost v D a b c : ℝ) ≤ S * (tgt (v / S) (mid a b) (sgn a b c) / (D / S)) := by
  have hS : (0 : ℝ) < S := by norm_num [S]
  rw [colCost, ite_eq_right (by omega)]
  refine (cast_ediv_le hD).trans ?_
  have : (0 : ℝ) ≤ D := by exact_mod_cast hD.le
  grw [Int.cast_mul, show (tangentCost v (a + b) (b - a) c : ℝ) ≤ S * tgt (v / S) (mid a b) (sgn a b c) by
    unfold tangentCost; dsimp only
    set d := v - (a + b) * HS
    have hxr : (d : ℝ) = S * (v / S - mid a b) := by simp [d, mid, S, TS, HS]; ring
    by_cases hx : d ≤ 0
    · rw [ite_eq_left hx, tgt, max_eq_left (by nlinarith [show (d : ℝ) ≤ 0 by exact_mod_cast hx])]; simp
    · rw [ite_eq_right hx, tgt, max_eq_right (by nlinarith [show (0 : ℝ) < d by exact_mod_cast not_le.1 hx])]
      refine (cast_ediv_le (by decide)).trans_eq ?_
      rcases hc with rfl | rfl <;> (simp [d, mid, sgn, hw, S, TS, HS]; ring)]
  rw [div_div_eq_mul_div]; exact le_of_eq (by ring)

private lemma rowBudget_tangent_ge (r : RowHead) (a b : ℤ) {c} (hc : c = 0 ∨ c = 1) :
    S * (1 - (r.fam.map fun t => (t.1 : ℝ) * tgt (t.2.1 / S) (mid a b) (sgn a b c) / (t.2.2 / S)).sum -
      (mid a b ^ 2 + 2 * mid a b * sgn a b c) / (r.d / S)) ≤ rowBudget r a b c := by
  rw [rowBudget, ite_eq_right (by omega)]; dsimp only
  have hq (q : ℚ) : (q : ℝ) ≤ ⌈q⌉ := by exact_mod_cast Int.le_ceil q
  refine (le_of_eq ?_).trans (hq _)
  have hte (w m h : ℚ) : (tangentExact w m h c : ℝ) = tgt w m ((2 * c - 1) * h) := by
    unfold tangentExact tgt; dsimp only
    rcases hc with rfl | rfl
    · simp [max_comm]; ring
    · simp only [one_ne_zero, ↓reduceIte, Nat.cast_one]
      split_ifs with hp
      · push_cast; rw [max_comm]; ring
      · simp [max_eq_left (show (w : ℝ) - m ≤ 0 by exact_mod_cast le_of_not_gt fun h => hp (lt_max_of_lt_left h))]
  symm
  rw [Rat.cast_mul, Rat.cast_sub, Rat.cast_sub, Rat.cast_list_sum, List.map_map,
    List.map_congr_left fun t _ => show _ = (t.1 : ℝ) * tgt (t.2.1 / S) (mid a b) (sgn a b c) / (t.2.2 / S) by
      simp [hte, mid, sgn, hw]]
  rcases hc with rfl | rfl <;> (simp [sgn, mid, hw]; ring)

private lemma zip3_eq (f : α → β → γ → δ) (a b c) :
    List.zipWith3 f a b c = List.zipWith (fun x (y, z) => f x y z) a (b.zip c) := by
  rw [List.zip_eq_zipWith, List.zipWith_zipWith_right]

private lemma colCosts_spec {L} (hwf : wellFormed L = true) {c} (hc : c ∈ L.cols)
    {box} (hbox : box.length = L.rows.length) {cs} (hcs : cs.length = L.rows.length) :
    (colCosts c box cs).length = L.rows.length ∧ ∀ k < L.rows.length,
      (colCosts c box cs).getD k 0 = colCost (c.v.getD k 0) (c.D.getD k 1)
        (bk box k).1 (bk box k).2 (cs.getD k 0) := by
  obtain ⟨hv, hD, -⟩ := wf_col hwf hc
  exact ⟨by simp [colCosts, zip3_eq, hbox, hv, hD, hcs],
    fun k hk => by simp [colCosts, zip3_eq, hbox, hv, hD, hcs, hk, bk]⟩

private lemma budgets_spec {L box} (hbox : box.length = L.rows.length)
    {cs} (hcs : cs.length = L.rows.length) :
    (budgets L box cs).length = L.rows.length ∧ ∀ k < L.rows.length,
      (budgets L box cs).getD k 0 = rowBudget (rh L k) (bk box k).1 (bk box k).2 (cs.getD k 0) :=
  ⟨by simp [budgets, zip3_eq, hbox, hcs], fun k hk => by simp [budgets, zip3_eq, hbox, hcs, hk, bk]⟩

private lemma sum_zip : ∀ (a : List ℕ) (b : List ℤ),
    (List.zipWith (· * ·) (a.map Nat.cast) b).sum =
      ∑ k ∈ range (min a.length b.length), (a.getD k 0 : ℤ) * b.getD k 0
  | [], _ | _, [] => by simp
  | _ :: xs, _ :: ys => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, List.length_cons,
      Nat.succ_min_succ, sum_range_succ', List.getD_cons_succ, List.getD_cons_zero, sum_zip xs ys]
    ring

private lemma exists_caseVector : ∀ (P : ℕ → ℕ → Prop) (os : List ℕ),
    (∀ k < os.length, (os.getD k 0 = 1 → P k 0 ∨ P k 1) ∧ (os.getD k 0 ≠ 1 → P k 2)) →
    ∃ cs ∈ caseVectors os, cs.length = os.length ∧ ∀ k < os.length, P k (cs.getD k 0)
  | _, [], _ => ⟨[], by simp [caseVectors]⟩
  | P, o :: os, h => by
    obtain ⟨cs, hcs, hlen, hP⟩ := exists_caseVector (P <| · + 1) os fun k hk =>
      by simpa using h (k + 1) (Nat.succ_lt_succ hk)
    obtain ⟨c, hc1, hc0⟩ : ∃ c, c :: cs ∈ caseVectors (o :: os) ∧ P 0 c := by
      by_cases ho : o = 1
      · rcases (h 0 (by simp)).1 ho with hp | hp <;> exact ⟨_, by simp [caseVectors, ho, hcs], hp⟩
      · exact ⟨2, by simp [caseVectors, ho, hcs], (h 0 (by simp)).2 ho⟩
    exact ⟨c :: cs, hc1, by simp [hlen], fun | 0, _ => hc0 | k + 1, hk => hP k (Nat.lt_of_succ_lt_succ hk)⟩

private lemma caseValue_sound {L} (hwf : wellFormed L = true) {box}
    (hbox : box.length = L.rows.length) {cs} (hlen : cs.length = L.rows.length)
    {du val} (hval : caseValue L box cs du = some val)
    {x τ} (hfeas : Feasible L x τ)
    (hrel : ∀ k < L.rows.length, RelaxHolds L x k (bk box k).1 (bk box k).2 (cs.getD k 0)) :
    objective L x ≤ val := by
  obtain ⟨hx, hW, hC, hNH, hE, -⟩ := hfeas
  obtain ⟨hblen, hbget⟩ := budgets_spec hbox hlen
  simp only [caseValue, Option.ite_none_right_eq_some, Option.some.injEq, List.all_eq_true,
    decide_eq_true_eq, bind_pure_comp, List.map_eq_map] at hval
  obtain ⟨⟨hZ, hcols⟩, rfl⟩ := hval
  have hc' (j : Fin L.cols.length) := (hcols _ (List.get_mem L.cols j)).trans_eq <| by
    obtain ⟨hclen', hcget⟩ := colCosts_spec hwf (List.get_mem L.cols j) hbox hlen
    rw [sum_zip, hZ, hclen', min_self, sum_congr rfl fun k hk => show _ =
      (du.Z.getD k 0 : ℤ) * colCost (cv L j k) (cD L j k) (bk box k).1 (bk box k).2 (cs.getD k 0) by
      rw [hcget k (mem_range.1 hk)]]
  have h1 := sum_le_sum fun j (_ : j ∈ univ) =>
    mul_le_mul_of_nonneg_right ((Int.cast_le (R := ℝ)).2 (hc' j)) (hx j)
  simp only [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_sum,
    add_mul, sum_add_distrib, sum_mul, mul_assoc] at h1
  rw [sum_comm (t := range L.rows.length)] at h1
  simp only [← mul_sum, hE] at h1
  grw [hW, hC, hNH, sum_le_sum fun k hk =>
    mul_le_mul_of_nonneg_left (hrel k (mem_range.1 hk)) (Nat.cast_nonneg _)] at h1
  rw [sum_zip, hZ, hblen, min_self, sum_congr rfl fun k hk => by rw [hbget k (mem_range.1 hk)]]
  have hceil (t : ℤ) : (t : ℝ) ≤ DS * (ceilDiv t DS : ℝ) := by
    have := Int.ediv_mul_le (-t) (by decide : DS ≠ 0)
    unfold ceilDiv; exact_mod_cast (by linarith : t ≤ DS * -(-t / DS))
  unfold objective; rw [Int.cast_add, Int.cast_add]
  suffices (DS : ℝ) * ∑ j, (L.cols.get j).G * x j ≤ DS * (ceilDiv _ DS : ℝ) by
    linarith [le_of_mul_le_mul_left this (by norm_num [DS] : (0 : ℝ) < DS)]
  refine le_trans (by push_cast; linarith) (hceil _)

private lemma relax_both {L} (hwf : wellFormed L = true) {x : Fin L.cols.length → ℝ}
    (hx : ∀ j, 0 ≤ x j) {k} {a b : ℤ} (ha : 0 ≤ a) {τ}
    (hτa : (a : ℝ) ≤ τ * TS) (hτb : τ * TS ≤ b)
    (hrow : rowLHS L x k τ ≤ 1 - τ ^ 2 / ((rh L k).d / S)) :
    (RelaxHolds L x k a b 0 ∨ RelaxHolds L x k a b 1) ∧ RelaxHolds L x k a b 2 := by
  obtain ⟨hd, hfam⟩ := wf_row hwf k
  have hS : (0 : ℝ) < S := by norm_num [S]
  have hT : (0 : ℝ) < TS := by norm_num [TS]
  have hSrow := mul_le_mul_of_nonneg_left hrow hS.le
  unfold rowLHS at hSrow
  refine ⟨?_, ?_⟩
  · set mm := mid a b; set hh := hw a b; set s₀ := τ - mm
    have hs1 : -hh ≤ s₀ := by linarith [(div_le_iff₀ hT).2 hτa, show mm - hh = a / TS by dsimp [mm, hh]; ring]
    have hs2 : s₀ ≤ hh := by linarith [(le_div_iff₀ hT).2 hτb, show mm + hh = b / TS by dsimp [mm, hh]; ring]
    let α : ℝ := if hh = 0 then 1 else (hh - s₀) / (2 * hh)
    let β : ℝ := 1 - α
    obtain ⟨hα, hβ, hcomb⟩ : 0 ≤ α ∧ 0 ≤ β ∧ α * sgn a b 0 + β * sgn a b 1 = s₀ := by
      dsimp only [sgn, α, β]; rw [show hw a b = hh from rfl]; split_ifs with hh0
      · exact ⟨zero_le_one, by norm_num, by simp [hh0]; linarith⟩
      · have : 0 < hh := lt_of_le_of_ne (by linarith) (Ne.symm hh0)
        exact ⟨div_nonneg (by linarith) (by positivity),
          sub_nonneg.2 ((div_le_one (by positivity)).2 (by linarith)), by push_cast; field_simp; ring⟩
    have htgt w : tgt w mm s₀ ≤ max 0 (w - τ) ^ 2 := by
      rcases le_total (w - mm) 0 with hw0 | hw0
      · simp only [tgt, max_eq_left hw0]; nlinarith [sq_nonneg (max 0 (w - τ))]
      · simp only [tgt, max_eq_right hw0]; dsimp [s₀]
        nlinarith [sq_nonneg (max 0 (w - τ) - (w - mm)),
          mul_nonneg hw0 (sub_nonneg.2 (le_max_right 0 (w - τ)))]
    let G s := ∑ j, x j * tgt (cv L j k / S) mm s / (cD L j k / S) +
      ((rh L k).fam.map fun t => (t.1 : ℝ) * tgt (t.2.1 / S) mm s / (t.2.2 / S)).sum +
      (mm ^ 2 + 2 * mm * s) / ((rh L k).d / S)
    have hGs₀ : G s₀ ≤ 1 := by
      refine le_trans ?_ (show rowLHS L x k τ + τ ^ 2 / ((rh L k).d / S) ≤ 1 by linarith)
      dsimp only [G, rowLHS]
      refine add_le_add (add_le_add (sum_le_sum fun j _ => ?_) (List.sum_le_sum fun t ht => ?_)) ?_
      · have := hx j; have : (0 : ℝ) < cD L j k / S := div_pos (by exact_mod_cast wf_colD hwf j k) hS
        gcongr; exact htgt _
      · have : (0 : ℝ) ≤ t.1 := by exact_mod_cast (hfam t ht).1
        have : (0 : ℝ) < t.2.2 / S := div_pos (by exact_mod_cast (hfam t ht).2) hS
        gcongr; exact htgt _
      · have : (0 : ℝ) < (rh L k).d / S := div_pos (by exact_mod_cast hd) hS
        gcongr; dsimp [s₀]; nlinarith [sq_nonneg (τ - mm)]
    have haff : α * G (sgn a b 0) + β * G (sgn a b 1) = G s₀ := by
      dsimp only [G]
      rw [show ∀ a1 b1 c1 a2 b2 c2 : ℝ, α * (a1 + b1 + c1) + β * (a2 + b2 + c2) =
        (α * a1 + β * a2) + (α * b1 + β * b2) + (α * c1 + β * c2) by intros; ring]
      congr 1; · congr 1
                 · simp only [mul_sum, ← sum_add_distrib]
                   exact sum_congr rfl fun j _ => by rw [← hcomb]; dsimp [tgt, β]; ring
                 · rw [← List.sum_map_mul_left, ← List.sum_map_mul_left, ← List.sum_map_add]
                   exact congrArg List.sum (List.map_congr_left fun t _ => by rw [← hcomb]; dsimp [tgt, β]; ring)
      · rw [← hcomb]; dsimp [β]; ring
    have hc_le {c} (hc : c = 0 ∨ c = 1) :
        ∑ j, (colCost (cv L j k) (cD L j k) a b c : ℝ) * x j - rowBudget (rh L k) a b c ≤
          S * (G (sgn a b c) - 1) := by
      grw [sum_le_sum fun j _ => (by
          have := hx j; grw [colCost_tangent_le _ _ a b (wf_colD hwf j k) hc]
          exact le_of_eq (by dsimp [mm]; ring) :
            _ ≤ S * (x j * tgt (cv L j k / S) mm (sgn a b c) / (cD L j k / S))),
        ← rowBudget_tangent_ge (rh L k) a b hc]
      rw [← mul_sum]; exact le_of_eq (by dsimp [G, mm]; ring)
    unfold RelaxHolds; by_contra! H
    have h0 := hc_le (.inl rfl); have h1 := hc_le (.inr rfl)
    have hcombG : S * (G s₀ - 1) ≤ 0 := by nlinarith
    rw [← haff, show S * (α * G (sgn a b 0) + β * G (sgn a b 1) - 1) =
      α * (S * (G (sgn a b 0) - 1)) + β * (S * (G (sgn a b 1) - 1)) by dsimp [β]; ring] at hcombG
    rcases eq_or_lt_of_le hα with hα0 | hp <;> dsimp [β] at *
    · nlinarith
    · nlinarith [mul_lt_mul_of_pos_left H.1 hp, mul_le_mul_of_nonneg_left H.2.le hβ,
        mul_le_mul_of_nonneg_left h0 hα, mul_le_mul_of_nonneg_left h1 hβ]
  · have hsh : (S : ℝ) * τ ≤ (b * (S / TS) : ℤ) := by norm_num [S, TS] at hτb ⊢; linarith
    unfold RelaxHolds
    rw [rowBudget, ite_eq_left rfl, Int.cast_sub, Int.cast_sub, Int.cast_list_sum, List.map_map, Function.comp_def]
    grw [sum_le_sum fun j _ => (by
        rw [colCost, ite_eq_left rfl]
        exact (mul_le_mul_of_nonneg_right
          (by simpa only [one_mul, Int.cast_one] using first_le zero_le_one (wf_colD hwf j k) hsh (v := cv L j k))
          (hx j)).trans_eq (by ring) : _ ≤ S * (x j * max 0 (cv L j k / S - τ) ^ 2 / (cD L j k / S))),
      List.sum_le_sum fun t ht => first_le (hfam t ht).1 (hfam t ht).2 hsh,
      (cast_ediv_le (mul_pos (by decide) hd)).trans (show _ ≤ S * (τ ^ 2 / ((rh L k).d / S)) by
        push_cast
        have : (0 : ℝ) < (rh L k).d := by exact_mod_cast hd
        have : (TS : ℝ) ≠ 0 := by norm_num [TS]
        rw [mul_assoc (_ * _ : ℝ)]
        grw [mul_self_le_mul_self (by exact_mod_cast ha) hτa]
        rw [div_div_eq_mul_div]; exact le_of_eq (by field_simp))]
    rw [← mul_sum, List.sum_map_mul_left]; linarith

private lemma verifyTree_sound {L} (hwf : wellFormed L = true) {x τ}
    (hfeas : Feasible L x τ) {T} :
    ∀ {box m}, verifyTree L T box = some m →
      box.length = L.rows.length →
      (∀ k < L.rows.length, 0 ≤ (bk box k).1 ∧
        ((bk box k).1 : ℝ) ≤ τ k * TS ∧ τ k * TS ≤ (bk box k).2) →
      objective L x ≤ m := by
  induction T with
  | split k mid l r ihl ihr =>
    intro box m h hlen hbox
    simp only [verifyTree] at h; split at h <;> try simp at h
    rename_i a b hk
    obtain ⟨hab, m1, h1, m2, h3, rfl⟩ := by simpa [Option.bind_eq_some_iff] using h
    obtain ⟨hkl, hkv⟩ := List.getElem?_eq_some_iff.1 hk
    obtain ⟨ha0, hτa, hτb⟩ := (by simp [bk, hkl, hkv] : bk box k = (a, b)) ▸ hbox k (hlen ▸ hkl)
    have hinv p (hp : 0 ≤ p.1 ∧ (p.1 : ℝ) ≤ τ k * TS ∧ τ k * TS ≤ p.2) :
        ∀ i < L.rows.length, 0 ≤ (bk (box.set k p) i).1 ∧
          ((bk (box.set k p) i).1 : ℝ) ≤ τ i * TS ∧
            τ i * TS ≤ (bk (box.set k p) i).2 := fun i hi => by
      simp only [bk, List.getD_eq_getElem?_getD, List.getElem?_set]
      by_cases hik : k = i
      · subst hik; simpa [hkl] using hp
      · simpa [bk, List.getD_eq_getElem?_getD, hik] using hbox i hi
    by_cases hmid : τ k * TS ≤ mid
    · exact (ihl h1 (by simp [hlen]) (hinv (a, mid) ⟨ha0, hτa, hmid⟩)).trans
        (by exact_mod_cast le_max_left _ _)
    · exact (ihr h3 (by simp [hlen])
        (hinv (mid, b) ⟨ha0.trans hab.1.le, le_of_not_ge hmid, hτb⟩)).trans
        (by exact_mod_cast le_max_right _ _)
  | node orders certs =>
    intro box m h hbox hτ
    simp only [verifyTree, Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨v, hv, -, rfl⟩ := h
    unfold checkBox at hv; dsimp only at hv; split_ifs at hv with hc
    obtain ⟨hord, hclen, -⟩ := hc
    obtain ⟨cs, hcs, hlen, hrel⟩ := exists_caseVector
      (fun k c => RelaxHolds L x k (bk box k).1 (bk box k).2 c) orders
      fun k hk => by
        rw [hord] at hk
        obtain ⟨ha, hτa, hτb⟩ := hτ k hk
        obtain ⟨h1, h2⟩ := relax_both hwf hfeas.1 ha hτa hτb (hfeas.2.2.2.2.2 k hk).2.2
        exact ⟨fun _ => h1, fun _ => h2⟩
    rw [hord] at hlen hrel
    obtain ⟨-, hbget⟩ := budgets_spec hbox hlen
    obtain ⟨i, hi, hcsi⟩ := List.mem_iff_getElem.1 hcs
    have ⟨cc₀, hmem, hfst⟩ : ∃ cc ∈ (caseVectors orders).zip certs, cc.1 = cs :=
      ⟨_, List.getElem_mem (by simp [hclen, hi] : i < _), by simp [List.getElem_zip, hcsi]⟩
    generalize (caseVectors orders).zip certs = l, (some (-1) : Option ℤ) = init at hv hmem
    suffices (∃ a, init = some a ∧ a ≤ v) ∧ ∀ cc ∈ l, cc.1 = cs → objective L x ≤ v from
      this.2 _ hmem hfst
    clear hmem; induction l generalizing init with
    | nil => exact ⟨⟨v, hv, le_rfl⟩, by simp⟩
    | cons cc l ih =>
      obtain ⟨⟨a', ha', hm⟩, hl⟩ := ih _ hv
      obtain ⟨a, rfl, hb⟩ := Option.bind_eq_some_iff.1 ha'
      have ⟨hle, hobj⟩ : a ≤ a' ∧ (cc.1 = cs → objective L x ≤ a') := by
        rcases cc with ⟨cv', _ | du⟩
        · simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hb
          refine ⟨hb.2.le, fun hcs' => ?_⟩
          rw [show cv' = cs from hcs'] at hb
          simp only [excludable, List.any_eq_true, List.all_eq_true, Bool.and_eq_true,
            decide_eq_true_eq, List.mem_range] at hb
          obtain ⟨⟨k, hk, hneg, hcost⟩, -⟩ := hb
          rw [hbget k hk] at hneg
          have h0 := (sum_nonneg fun j _ => mul_nonneg (by
            have hm' := List.get_mem L.cols j
            exact_mod_cast (colCosts_spec hwf hm' hbox hlen).2 k hk ▸ hcost _ hm') (hfeas.1 j)).trans (hrel k hk)
          exact absurd hneg (not_lt.2 (by exact_mod_cast h0))
        · obtain ⟨val, hval, rfl⟩ := Option.map_eq_some_iff.1 hb
          exact ⟨le_max_left _ _, fun hcs' => (caseValue_sound hwf hbox hlen (hcs' ▸ hval) hfeas hrel).trans
            (by exact_mod_cast le_max_right _ _)⟩
      exact ⟨⟨a, rfl, hle.trans hm⟩,
        List.forall_mem_cons.2 ⟨fun h => (hobj h).trans (by exact_mod_cast hm), hl⟩⟩

section
variable {L T val} (h : checkLeaf L T = some val)
include h

theorem checkLeaf_lt : val < S := by
  unfold checkLeaf at h; split_ifs at h
  let rec go {T box m} (h : verifyTree L T box = some m) : m < S := match T with
    | .split _ _ _ _ => by
      simp only [verifyTree] at h; split at h <;> simp_all [Option.bind_eq_some_iff]
      obtain ⟨-, _, h1, _, h2, rfl⟩ := h; exact max_lt (go h1) (go h2)
    | .node _ _ => by
      simp only [verifyTree, Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq] at h
      obtain ⟨_, _, hv, rfl⟩ := h; exact hv
  exact go h

variable (x : _) (τ : _) (hfeas : Feasible L x τ)
include hfeas

theorem checkLeaf_sound : objective L x ≤ val := by
  unfold checkLeaf at h; split_ifs at h with hwf
  refine verifyTree_sound hwf hfeas h (by simp [rootBox]) fun k hk => ?_
  rw [show bk (rootBox L) k = (0, rootEnd (rh L k).d) by simp [bk, rootBox, hk]]
  obtain ⟨h0, hd, -⟩ := hfeas.2.2.2.2.2 k hk
  refine ⟨le_rfl, by simpa using mul_nonneg h0 (by norm_num [TS] : (0 : ℝ) ≤ TS), ?_⟩
  set d := (rh L k).d
  have h1 : (τ k * TS) ^ 2 * S < ((d * TS * TS / S + 1 : ℤ) : ℝ) * S := by
    nlinarith [(le_div_iff₀ (by norm_num [S])).1 hd, sq_nonneg (TS : ℝ),
      show (d : ℝ) * TS * TS < ((d * TS * TS / S + 1 : ℤ) : ℝ) * S by
        exact_mod_cast Int.lt_ediv_add_one_mul_self (d * TS * TS) (by decide)]
  have h2 : ((d * TS * TS / S + 1 : ℤ) : ℝ) ≤ (rootEnd d : ℝ) ^ 2 := by
    unfold rootEnd; norm_cast; rw [sq]
    refine (Int.add_le_add_right (Int.self_le_toNat _) 1).trans (Int.ofNat_le.2 ?_)
    unfold isqrtUp; split_ifs with hq; exacts [hq.ge, (Nat.lt_succ_sqrt _).le]
  nlinarith [lt_of_mul_lt_mul_right h1 (by norm_num [S] : (0 : ℝ) ≤ S),
    show (0 : ℝ) ≤ rootEnd d by unfold rootEnd; positivity]

theorem certified : objective L x < S :=
  (checkLeaf_sound h x τ hfeas).trans_lt (by exact_mod_cast checkLeaf_lt h)

end

end

end GradedNear.Cert
