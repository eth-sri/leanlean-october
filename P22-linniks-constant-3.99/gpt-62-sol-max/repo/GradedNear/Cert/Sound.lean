module

public import GradedNear.Cert.Relax

/-!
# Soundness of the certificate checker

The rounded row constraints are enough for weak duality (with a free multiplier for the
second-family equality) and rule out exclusion. In a bx containing the actual thresholds,
choose a valid relaxation for each row. The case fold checks that vector along with all the
others. A bisection preserves containment in at least one child, and the rounded square root
at the root bounds every admissible threshold.
-/

@[expose] public section

namespace GradedNear.Cert

open Finset

private abbrev Box := List (ℤ × ℤ)
private abbrev cell (bx : Box) (k : ℕ) := bx.getD k (0, 0)

private lemma zipWith3_eq {α β γ δ : Type*} (f : α → β → γ → δ)
    (xs : List α) (ys : List β) (zs : List γ) :
    List.zipWith3 f xs ys zs = List.zipWith (fun x (y, z) => f x y z) xs (ys.zip zs) :=
  (List.zipWith_zipWith_right (fun x (y, z) => f x y z) Prod.mk xs ys zs).symm

-- Beyond the available budgets or costs the default is zero, so no equality of lengths is needed.
private lemma dual_sum (Z : List ℕ) (w : List ℤ) :
    (List.zipWith (fun z v => (z : ℤ) * v) Z w).sum =
      ∑ k ∈ range Z.length, (Z.getD k 0 : ℤ) * w.getD k 0 := by
  induction Z generalizing w with
  | nil => simp
  | cons z Z ih =>
    cases w with
    | nil => simp
    | cons v w => simpa [sum_range_succ', add_comm] using ih w

variable {L : Leaf} {bx : List (ℤ × ℤ)} {cs : List ℕ} {x : Fin L.cols.length → ℝ} {τ : ℕ → ℝ} {v : ℤ}

private abbrev Rounded (x : Fin L.cols.length → ℝ) (bx : Box) (cs : List ℕ) : Prop :=
  ∀ k < L.rows.length, ∑ j, ((colCosts (L.cols.get j) bx cs).getD k 0 : ℝ) * x j ≤
    (budgets L bx cs).getD k 0

private lemma rounded_of (hwf : wellFormed L = true)
    (hb : bx.length = L.rows.length) (hs : cs.length = L.rows.length)
    (h : ∀ k < L.rows.length, RelaxHolds L x k (cell bx k).1 (cell bx k).2 (cs.getD k 0)) :
    Rounded x bx cs := by
  intro k hk
  have H := h k hk
  unfold RelaxHolds at H
  convert H using 1
  · refine sum_congr rfl fun j _ => ?_
    obtain ⟨hv, hD⟩ := (wf_col hwf (List.get_mem _ j)).1
    simp_all [List.get_eq_getElem, colCosts, zipWith3_eq, cell, List.getElem_zipWith, List.getElem_zip]
  · simp [budgets, zipWith3_eq, cell, List.getElem_zipWith, List.getElem_zip, *]

private lemma obj_le_of {T : ℤ}
    (h : (DS : ℝ) * ∑ j, (L.cols.get j).G * x j ≤ (T : ℝ)) :
    objective L x ≤ ((ceilDiv T DS + L.first + L.final : ℤ) : ℝ) := by
  have hT := neg_le_neg (int_div_le (-T) DS (by norm_num [DS]))
  norm_num [objective, ceilDiv, DS] at h hT ⊢
  linarith

-- Multiply the column inequalities by the primal variables and use the rows, including
-- the equality row with its free multiplier P - M.
private lemma caseValue_sound {du : Duals}
    (hv : caseValue L bx cs du = some v)
    (hf : Feasible L x τ) (hr : Rounded x bx cs) :
    objective L x ≤ v := by
  unfold caseValue at hv
  split_ifs at hv with hd
  cases hv
  obtain ⟨hx, hW, hC, hNH, hE, -⟩ := hf
  have hc (j : Fin L.cols.length) := by
    have h := List.all_eq_true.mp hd.2 _ (List.get_mem _ j)
    rw [decide_eq_true_eq, dual_sum, hd.1] at h
    have hh := (Int.cast_le (R := ℝ)).mpr h
    push_cast at hh
    exact hh
  have H := sum_le_sum fun j (_ : j ∈ univ) => mul_le_mul_of_nonneg_right (hc j) (hx j)
  simp only [add_mul, sum_add_distrib, sum_mul, mul_assoc, ← mul_sum, hE] at H
  rw [sum_comm] at H
  simp only [← mul_sum] at H
  apply obj_le_of
  rw [dual_sum, hd.1]
  push_cast
  exact H.trans (by gcongr with k hk; exact hr k (mem_range.mp hk))

private lemma not_excludable
    (hx : ∀ j, 0 ≤ x j) (hr : Rounded x bx cs) : excludable L bx cs ≠ true := by
  intro h
  simp only [excludable, List.any_eq_true, List.mem_range, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨k, hk, hb, hc⟩ := h
  refine (not_lt_of_ge ((sum_nonneg fun j _ => mul_nonneg ?_ (hx j)).trans (hr k hk))) ?_
  · exact_mod_cast hc _ (List.get_mem _ j)
  · exact_mod_cast hb

private lemma exists_caseVector (P : ℕ → ℕ → Prop) (os : List ℕ)
    (h : ∀ k < os.length, if os.getD k 0 = 1 then P k 0 ∨ P k 1 else P k 2) :
    ∃ cs ∈ caseVectors os, cs.length = os.length ∧ ∀ k < os.length, P k (cs.getD k 0) := by
  induction os generalizing P with
  | nil => simp [caseVectors]
  | cons o os ih =>
    obtain ⟨cs, hcs, hlen, hP⟩ := ih (fun k c => P (k + 1) c)
      (fun k hk => by simpa using h (k + 1) (by simpa using hk))
    have h0 := h 0 (by simp)
    obtain ⟨c, hc, hm⟩ : ∃ c, P 0 c ∧ c :: cs ∈ caseVectors (o :: os) := by
      split at h0 <;> aesop (add simp caseVectors)
    exact ⟨c :: cs, hm, by simp [hlen], fun k hk => by cases k <;> simp_all⟩

private def InBox (L : Leaf) (bx : Box) (τ : ℕ → ℝ) : Prop :=
  bx.length = L.rows.length ∧ ∀ k < L.rows.length,
    0 ≤ (cell bx k).1 ∧ ((cell bx k).1 : ℝ) ≤ τ k * TS ∧ τ k * TS ≤ (cell bx k).2

private lemma checkBox_sound (hwf : wellFormed L = true) {os : List ℕ}
    {certs : List CaseCert} (h : checkBox L bx os certs = some v) (hf : Feasible L x τ) (hb : InBox L bx τ) :
    objective L x ≤ v := by
  unfold checkBox at h
  dsimp only at h
  split_ifs at h with ho
  obtain ⟨cv, hc, hl, hr⟩ := exists_caseVector
    (fun k c => RelaxHolds L x k (cell bx k).1 (cell bx k).2 c) os (fun k hk => by
      rw [ho.1] at hk
      obtain ⟨h0, ha, hb⟩ := hb.2 k hk
      exact relax_row hwf hf.1 h0 ha hb (hf.2.2.2.2.2 k hk).2.2 _)
  rw [ho.1] at hl hr
  have H := rounded_of hwf hb.1 hl hr
  have hm : cv ∈ (List.zip (caseVectors os) certs).map Prod.fst := by rwa [List.map_fst_zip ho.2.1.ge]
  have hn := not_excludable hf.1 H
  generalize List.zip (caseVectors os) certs = l at h hm
  induction l using List.reverseRecOn generalizing v with
  | nil => simp at hm
  | append_singleton l cc ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, Option.bind_eq_some_iff] at h
    obtain ⟨u, hu, hv⟩ := h
    rcases cc with ⟨cv', _ | du⟩ <;>
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hm
    · split_ifs at hv with he
      grind
    · grind [Option.map_eq_some_iff, Int.cast_max, le_max_iff, caseValue_sound]

private lemma inBox_set (h : InBox L bx τ)
    {k : ℕ} (hk : k < bx.length) {a b : ℤ} (ha : 0 ≤ a) (hta : (a : ℝ) ≤ τ k * TS)
    (htb : τ k * TS ≤ b) : InBox L (bx.set k (a, b)) τ := by
  grind [InBox]

private lemma verifyTree_spec (T : Tree)
    (h : verifyTree L T bx = some v) : v < S ∧
      ∀ x τ, wellFormed L = true → Feasible L x τ → InBox L bx τ → objective L x ≤ v := by
  induction T generalizing bx v with
  | node os cs => grind [verifyTree, Option.bind_eq_some_iff, checkBox_sound]
  | split k mid l r ihl ihr =>
    simp only [verifyTree] at h
    split at h
    next a b he =>
      split_ifs at h with hmid
      obtain ⟨vl, hl, vr, hr, rfl⟩ := by simpa only [Option.bind_eq_some_iff, Option.map_eq_some_iff] using h
      obtain ⟨hvl, hL⟩ := ihl hl
      obtain ⟨hvr, hR⟩ := ihr hr
      refine ⟨max_lt hvl hvr, fun x τ hwf hf hb => ?_⟩
      rw [Int.cast_max, le_max_iff]
      have hk := (List.getElem?_eq_some_iff.mp he).1
      have H := hb.2 k (by rwa [← hb.1])
      simp only [cell, List.getD_eq_getElem?_getD, he, Option.getD_some] at H
      rcases le_total (τ k * TS) (mid : ℝ) <;> grind only [inBox_set]
    next => simp at h

private lemma le_rootEnd {d : ℤ} {t : ℝ} (hd : t ^ 2 ≤ (d : ℝ) / S) :
    t * TS ≤ rootEnd d := by
  let q := d * TS * TS / S
  let r := isqrtUp (q.toNat + 1)
  have hrr : q.toNat + 1 ≤ r * r := by
    unfold r isqrtUp
    split_ifs with h
    · omega
    · exact (Nat.lt_succ_sqrt _).le
  have hr : (d : ℝ) ≤ 10000 * ((r : ℝ) * r) := by
    exact_mod_cast (show d ≤ 10000 * ((r * r : ℕ) : ℤ) by
      norm_num [q, S, TS] at hrr
      omega)
  change t * TS ≤ (r : ℝ)
  refine le_of_sq_le_sq ?_ (Nat.cast_nonneg _)
  norm_num [TS, S] at hd ⊢
  nlinarith

section LeafVerification

variable {T : Tree} {val : ℤ} (h : checkLeaf L T = some val)

include h

/-- An accepted certificate bounds the objective at every feasible point. -/
theorem checkLeaf_sound
    (x : Fin L.cols.length → ℝ) (τ : ℕ → ℝ) (hfeas : Feasible L x τ) :
    objective L x ≤ val := by
  unfold checkLeaf at h
  split_ifs at h with hwf
  refine (verifyTree_spec T h).2 x τ hwf hfeas ⟨by simp [rootBox], fun k hk => ?_⟩
  obtain ⟨h0, hd, -⟩ := hfeas.2.2.2.2.2 k hk
  have h₀ : (0 : ℝ) ≤ τ k * TS := mul_nonneg h0 (by norm_num [TS])
  simpa [cell, rootBox, hk] using And.intro h₀ (le_rootEnd (d := (rowAt L k).d) hd)

/-- An accepted certificate has value below the objective cutoff `S`. -/
theorem checkLeaf_lt : val < S := by
  grind [checkLeaf, → verifyTree_spec]

/-- A certified leaf has objective strictly below `S` throughout the feasible set. -/
theorem certified
    (x : Fin L.cols.length → ℝ) (τ : ℕ → ℝ) (hfeas : Feasible L x τ) :
    objective L x < S :=
  lt_of_le_of_lt (checkLeaf_sound h x τ hfeas) (by exact_mod_cast checkLeaf_lt h)

end LeafVerification

end GradedNear.Cert
