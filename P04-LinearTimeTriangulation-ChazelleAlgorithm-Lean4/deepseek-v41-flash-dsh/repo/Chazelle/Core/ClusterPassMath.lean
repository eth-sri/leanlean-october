module

public import Chazelle.Core.ClusterPassRam

/-!
# WP-I, part 30: what a partition pass computes

For the pass `passMem m0 sel … lo e j` (`ClusterPassRam.lean`), with `cntS sel lo i` the number of
selected positions in `[lo, i)`:

* `passMem_ptr_eq`: the pointer is `e + cntS sel lo (lo + j)`;
* `passMem_act`: the selected position `i` lands at `ACT[e + cntS sel lo i]`;
* `passMem_pos`: and `POS` of its item is that position;
* `passMem_keep`: nothing else changes.
-/

namespace Chazelle.Core.Cluster

open Machine

@[expose] public section

open Classical in
/-- The number of selected positions in `[lo, i)`. -/
noncomputable def cntS (sel : ℕ → Prop) (lo i : ℕ) : ℕ := ((Finset.Ico lo i).filter sel).card

section

variable {sel : ℕ → Prop} {m0 : ℕ → ℕ} {bACT bPOS bTMP lo e : ℕ}

theorem cntS_self (lo : ℕ) : cntS sel lo lo = 0 := by simp [cntS]

open Classical in
theorem cntS_succ {i : ℕ} (h : lo ≤ i) :
    cntS sel lo (i + 1) = cntS sel lo i + (if sel i then 1 else 0) := by
  classical
  unfold cntS
  rw [Nat.Ico_succ_right_eq_insert_Ico h, Finset.filter_insert]
  split_ifs with hs
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

theorem cntS_mono {i i' : ℕ} (h : i ≤ i') : cntS sel lo i ≤ cntS sel lo i' := by
  classical
  unfold cntS
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Ico_subset_Ico le_rfl h))

theorem cntS_lt {i i' : ℕ} (hlo : lo ≤ i) (h : i < i') (hs : sel i) :
    cntS sel lo i < cntS sel lo i' := by
  have := cntS_succ (sel := sel) hlo
  rw [ite_eq_left hs] at this
  have := cntS_mono (sel := sel) (lo := lo) (show i + 1 ≤ i' by omega)
  omega

theorem cntS_le (i : ℕ) : cntS sel lo i ≤ i - lo := by
  classical
  unfold cntS
  exact (Finset.card_filter_le _ _).trans (by rw [Nat.card_Ico])

open Classical in
theorem passMem_succ (j : ℕ) :
    passMem m0 sel bACT bPOS bTMP lo e (j + 1) =
      if sel (lo + j) then
        (upd (upd (passMem m0 sel bACT bPOS bTMP lo e j).1
          (bACT + (passMem m0 sel bACT bPOS bTMP lo e j).2) (m0 (bTMP + (lo + j))))
          (bPOS + m0 (bTMP + (lo + j))) (passMem m0 sel bACT bPOS bTMP lo e j).2,
          (passMem m0 sel bACT bPOS bTMP lo e j).2 + 1)
      else passMem m0 sel bACT bPOS bTMP lo e j := by
  simp only [passMem]

/-- **The pointer counts the selected positions.** -/
theorem passMem_ptr_eq (j : ℕ) :
    (passMem m0 sel bACT bPOS bTMP lo e j).2 = e + cntS sel lo (lo + j) := by
  classical
  induction j with
  | zero => simp [passMem, cntS_self]
  | succ j ih =>
    rw [passMem_succ, show lo + (j + 1) = lo + j + 1 by omega, cntS_succ (by omega)]
    split_ifs with hs
    · simp only; rw [ih]; omega
    · rw [ih]; omega

/-- **Selected items land at their rank.** -/
theorem passMem_act (j : ℕ)
    (hdAP : ∀ i, lo ≤ i → i < lo + j → ∀ p, e ≤ p → p < e + cntS sel lo (lo + j) →
      bPOS + m0 (bTMP + i) ≠ bACT + p) :
    ∀ i, lo ≤ i → i < lo + j → sel i →
      (passMem m0 sel bACT bPOS bTMP lo e j).1 (bACT + (e + cntS sel lo i)) = m0 (bTMP + i) := by
  classical
  induction j with
  | zero => intro i h1 h2; omega
  | succ j ih =>
    intro i h1 h2 hs
    have hp := passMem_ptr_eq (m0 := m0) (sel := sel) (bACT := bACT) (bPOS := bPOS)
      (bTMP := bTMP) (lo := lo) (e := e) j
    have hc := cntS_le (sel := sel) (lo := lo) (lo + j)
    have hcm := cntS_succ (sel := sel) (lo := lo) (show lo ≤ lo + j by omega)
    rw [show lo + j + 1 = lo + (j + 1) by omega] at hcm
    have hci : lo ≤ i → i < lo + j → sel i → cntS sel lo i < cntS sel lo (lo + j) :=
      fun a b c => cntS_lt a b c
    rw [passMem_succ]
    by_cases hsj : sel (lo + j)
    · rw [ite_eq_left hsj]
      rw [ite_eq_left hsj] at hcm
      simp only
      rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < lo + j + 1 by omega) with hi | hi
      · have hlt := cntS_lt (sel := sel) h1 hi hs
        have hci := cntS_mono (sel := sel) (lo := lo) (show i ≤ lo + j by omega)
        rw [Machine.upd_other _ _ _ (hdAP _ (by omega) (by omega) _ (by omega) (by omega)).symm,
          Machine.upd_other _ _ _ (by omega)]
        exact ih (fun i' a b p c d => hdAP i' a (by omega) p c (by omega)) i h1 hi hs
      · subst hi
        rw [Machine.upd_other _ _ _ (hdAP _ (by omega) (by omega) _ (by omega) (by omega)).symm,
          hp, Machine.upd_same]
    · rw [ite_eq_right hsj]
      rw [ite_eq_right hsj] at hcm
      have hi : i < lo + j := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < lo + j + 1 by omega) with hi | hi
        · exact hi
        · subst hi; exact absurd hs hsj
      exact ih (fun i' a b p c d => hdAP i' a (by omega) p c (by omega)) i h1 hi hs

/-- **The positions of the selected items.** -/
theorem passMem_pos (j : ℕ)
    (hdAP : ∀ i, lo ≤ i → i < lo + j → ∀ p, e ≤ p → p < e + cntS sel lo (lo + j) →
      bPOS + m0 (bTMP + i) ≠ bACT + p)
    (hinj : ∀ i i', lo ≤ i → i < lo + j → lo ≤ i' → i' < lo + j →
      m0 (bTMP + i) = m0 (bTMP + i') → i = i') :
    ∀ i, lo ≤ i → i < lo + j → sel i →
      (passMem m0 sel bACT bPOS bTMP lo e j).1 (bPOS + m0 (bTMP + i)) = e + cntS sel lo i := by
  classical
  induction j with
  | zero => intro i h1 h2; omega
  | succ j ih =>
    intro i h1 h2 hs
    have hp := passMem_ptr_eq (m0 := m0) (sel := sel) (bACT := bACT) (bPOS := bPOS)
      (bTMP := bTMP) (lo := lo) (e := e) j
    have hc := cntS_le (sel := sel) (lo := lo) (lo + j)
    have hcm := cntS_succ (sel := sel) (lo := lo) (show lo ≤ lo + j by omega)
    rw [show lo + j + 1 = lo + (j + 1) by omega] at hcm
    have hci : lo ≤ i → i < lo + j → sel i → cntS sel lo i < cntS sel lo (lo + j) :=
      fun a b c => cntS_lt a b c
    rw [passMem_succ]
    by_cases hsj : sel (lo + j)
    · rw [ite_eq_left hsj]
      rw [ite_eq_left hsj] at hcm
      simp only
      rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < lo + j + 1 by omega) with hi | hi
      · have hne : m0 (bTMP + i) ≠ m0 (bTMP + (lo + j)) := fun h =>
          absurd (hinj i (lo + j) h1 (by omega) (by omega) (by omega) h) (by omega)
        rw [Machine.upd_other _ _ _ (by omega),
          Machine.upd_other _ _ _ (hdAP _ h1 (by omega) _ (by omega) (by omega))]
        exact ih (fun i' a b p c d => hdAP i' a (by omega) p c (by omega))
          (fun a b c d e' f => hinj a b c (by omega) e' (by omega)) i h1 hi hs
      · subst hi
        rw [Machine.upd_same, hp]
    · rw [ite_eq_right hsj]
      rw [ite_eq_right hsj] at hcm
      have hi : i < lo + j := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < lo + j + 1 by omega) with hi | hi
        · exact hi
        · subst hi; exact absurd hs hsj
      exact ih (fun i' a b p c d => hdAP i' a (by omega) p c (by omega))
        (fun a b c d e' f => hinj a b c (by omega) e' (by omega)) i h1 hi hs

/-- **Nothing else changes.** -/
theorem passMem_keep (j : ℕ) {x : ℕ}
    (hA : ¬ (bACT + e ≤ x ∧ x < bACT + (e + cntS sel lo (lo + j))))
    (hP : ∀ i, lo ≤ i → i < lo + j → sel i → x ≠ bPOS + m0 (bTMP + i)) :
    (passMem m0 sel bACT bPOS bTMP lo e j).1 x = m0 x := by
  classical
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp := passMem_ptr_eq (m0 := m0) (sel := sel) (bACT := bACT) (bPOS := bPOS)
      (bTMP := bTMP) (lo := lo) (e := e) j
    have hcs := cntS_succ (sel := sel) (lo := lo) (show lo ≤ lo + j by omega)
    rw [show lo + (j + 1) = lo + j + 1 by omega, hcs] at hA
    rw [passMem_succ]
    by_cases hsj : sel (lo + j)
    · rw [ite_eq_left hsj] at hA ⊢
      simp only
      rw [Machine.upd_other _ _ _ (hP _ (by omega) (by omega) hsj),
        Machine.upd_other _ _ _ (by rw [hp]; omega)]
      exact ih (by omega) (fun i a b c => hP i a (by omega) c)
    · rw [ite_eq_right hsj] at hA ⊢
      exact ih (by omega) (fun i a b c => hP i a (by omega) c)

/-- **Passes with the same selection on the segment agree.** -/
theorem passMem_congr_sel {sel sel' : ℕ → Prop} (j : ℕ)
    (h : ∀ i, lo ≤ i → i < lo + j → (sel i ↔ sel' i)) :
    passMem m0 sel bACT bPOS bTMP lo e j = passMem m0 sel' bACT bPOS bTMP lo e j := by
  classical
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [passMem_succ, passMem_succ, ih (fun i a b => h i a (by omega))]
    by_cases hs : sel (lo + j)
    · rw [ite_eq_left hs, ite_eq_left ((h _ (by omega) (by omega)).mp hs)]
    · rw [ite_eq_right hs, ite_eq_right (fun h' => hs ((h _ (by omega) (by omega)).mpr h'))]

theorem cntS_congr {sel sel' : ℕ → Prop} {i : ℕ}
    (h : ∀ i', lo ≤ i' → i' < i → (sel i' ↔ sel' i')) : cntS sel lo i = cntS sel' lo i := by
  classical
  unfold cntS
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨a, b⟩, c⟩; exact ⟨⟨a, b⟩, (h x a b).mp c⟩
  · rintro ⟨⟨a, b⟩, c⟩; exact ⟨⟨a, b⟩, (h x a b).mpr c⟩

/-- **Every rank below the count is attained.** -/
theorem cntS_surj {sel : ℕ → Prop} {hi : ℕ} (hlh : lo ≤ hi) :
    ∀ r, r < cntS sel lo hi → ∃ i, lo ≤ i ∧ i < hi ∧ sel i ∧ cntS sel lo i = r := by
  classical
  induction hi, hlh using Nat.le_induction with
  | base => intro r hr; rw [cntS_self] at hr; omega
  | succ n hn ih =>
    intro r hr
    rw [cntS_succ hn] at hr
    by_cases hr' : r < cntS sel lo n
    · obtain ⟨i, a, b, c, d⟩ := ih r hr'
      exact ⟨i, a, by omega, c, d⟩
    · by_cases hs : sel n
      · rw [ite_eq_left hs] at hr
        exact ⟨n, hn, by omega, hs, by omega⟩
      · rw [ite_eq_right hs] at hr; omega

end

end

end Chazelle.Core.Cluster
