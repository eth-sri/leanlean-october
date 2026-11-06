module

public meta import Chazelle.Arithmetic

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
  grind

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


open Classical in
theorem passMem_succ (j : ℕ) :
    passMem m0 sel bACT bPOS bTMP lo e (j + 1) =
      if sel (lo + j) then
        (upd (upd (passMem m0 sel bACT bPOS bTMP lo e j).1
          (bACT + (passMem m0 sel bACT bPOS bTMP lo e j).2) (m0 (bTMP + (lo + j))))
          (bPOS + m0 (bTMP + (lo + j))) (passMem m0 sel bACT bPOS bTMP lo e j).2,
          (passMem m0 sel bACT bPOS bTMP lo e j).2 + 1)
      else passMem m0 sel bACT bPOS bTMP lo e j := by
  core_grind

/-- **The pointer counts the selected positions.** -/
theorem passMem_ptr_eq (j : ℕ) :
    (passMem m0 sel bACT bPOS bTMP lo e j).2 = e + cntS sel lo (lo + j) := by
  classical
  induction j with
  | zero => simp [passMem, cntS_self]
  | succ j ih =>
    grind [Chazelle.Core.Cluster.cntS_succ, Chazelle.Core.Cluster.passMem_succ]

section
variable (j : ℕ) (hdAP : ∀ i, lo ≤ i → i < lo + j → ∀ p, e ≤ p → p < e + cntS sel lo (lo + j) →
      bPOS + m0 (bTMP + i) ≠ bACT + p)
include hdAP
/-- **Selected items land at their rank.** -/
theorem passMem_act :
    ∀ i, lo ≤ i → i < lo + j → sel i →
      (passMem m0 sel bACT bPOS bTMP lo e j).1 (bACT + (e + cntS sel lo i)) = m0 (bTMP + i) := by
  classical
  induction j with
  | zero => omega
  | succ j ih =>
    intro i h1 h2 hs
    have hp := passMem_ptr_eq (m0 := m0) (sel := sel) (bACT := bACT) (bPOS := bPOS)
      (bTMP := bTMP) (lo := lo) (e := e) j
    
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
        
        rw [Machine.upd_other _ _ _ (hdAP _ (by omega) (by omega) _ (by omega) (by omega)).symm,
          Machine.upd_other _ _ _ (by omega)]
        grind
      · subst hi
        rw [Machine.upd_other _ _ _ (hdAP _ (by omega) (by omega) _ (by omega) (by omega)).symm,
          hp, Machine.upd_same]
    grind

/-- **The positions of the selected items.** -/
theorem passMem_pos
    (hinj : ∀ i i', lo ≤ i → i < lo + j → lo ≤ i' → i' < lo + j →
      m0 (bTMP + i) = m0 (bTMP + i') → i = i') :
    ∀ i, lo ≤ i → i < lo + j → sel i →
      (passMem m0 sel bACT bPOS bTMP lo e j).1 (bPOS + m0 (bTMP + i)) = e + cntS sel lo i := by
  classical
  induction j with
  | zero => omega
  | succ j ih =>
    intro i h1 h2 hs
    have hp := passMem_ptr_eq (m0 := m0) (sel := sel) (bACT := bACT) (bPOS := bPOS)
      (bTMP := bTMP) (lo := lo) (e := e) j
    
    have hcm := cntS_succ (sel := sel) (lo := lo) (show lo ≤ lo + j by omega)
    rw [show lo + j + 1 = lo + (j + 1) by omega] at hcm
    
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
        grind
      core_grind
    grind


end

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
        Machine.upd_other _ _ _ (by omega)]
      grind
    grind

/-- **Passes with the same selection on the segment agree.** -/
theorem passMem_congr_sel {sel sel' : ℕ → Prop} (j : ℕ)
    (h : ∀ i, lo ≤ i → i < lo + j → (sel i ↔ sel' i)) :
    passMem m0 sel bACT bPOS bTMP lo e j = passMem m0 sel' bACT bPOS bTMP lo e j := by
  classical
  induction j with
  | zero => rfl
  | succ j ih =>
    core_grind

theorem cntS_congr {sel sel' : ℕ → Prop} {i : ℕ}
    (h : ∀ i', lo ≤ i' → i' < i → (sel i' ↔ sel' i')) : cntS sel lo i = cntS sel' lo i := by
  classical
  unfold cntS
  congr 1
  grind

/-- **Every rank below the count is attained.** -/
theorem cntS_surj {sel : ℕ → Prop} {hi : ℕ} (hlh : lo ≤ hi) :
    ∀ r, r < cntS sel lo hi → ∃ i, lo ≤ i ∧ i < hi ∧ sel i ∧ cntS sel lo i = r := by
  classical
  induction hi, hlh using Nat.le_induction with
  | base => simp_all [cntS_self] 
  | succ n hn ih =>
    intro r hr
    rw [cntS_succ hn] at hr
    by_cases hr' : r < cntS sel lo n
    all_goals ram_grind

end

end

end Chazelle.Core.Cluster
