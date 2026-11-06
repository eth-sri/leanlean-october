module

public import Chazelle.Core.ClusterStageA

/-!
# WP-I, part 45: inverting a permutation of `[0, n)`

`invStmt`: `OUT[IN[i]] := i` for `i < n` (registers `130800` `IN`, `130801` `OUT`, `130802` `n`,
scratch `130803 … 130805`).  If `IN` is injective on `[0, n)` with values in `[0, n)`, then
`OUT[IN[i]] = i` for all `i < n`.

Also `BTree.OK.congr`: well-formedness only depends on the queue and the parents in range.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- One entry of the inversion. -/
def invBody : Stmt := block [.addN 130804 130800 130803, .loadN 130805 130804,
  .addN 130804 130801 130805, .storeN 130804 130803, .addN 130803 130803 130001]

/-- **The inverse permutation.** -/
def invStmt : Stmt := .seq (.instr (.constN 130803 0)) (.whileLtN 130803 130802 invBody)

/-- The registers of the inversion. -/
def InvRG (r : ℕ) : Prop := 130803 ≤ r ∧ r ≤ 130805

section proofs

variable {P : Polygon} {W : ℕ}

theorem invStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {bI bO n : ℕ} (hI : c.nreg 130800 = bI) (hO : c.nreg 130801 = bO) (hn : c.nreg 130802 = n)
    (hlt : ∀ i, i < n → c.nmem (bI + i) < n)
    (hinj : ∀ i j, i < n → j < n → c.nmem (bI + i) = c.nmem (bI + j) → i = j)
    (hd : bO + n ≤ bI ∨ bI + n ≤ bO) (hwI : bI + n ≤ W) (hwO : bO + n ≤ W) (hwn : n + 1 ≤ W) :
    ∃ c' k, Exec P W invStmt c c' k ∧ k ≤ 7 * n + 3 ∧ WordsBounded W c' ∧
      PFr InvRG (fun a => bO ≤ a ∧ a < bO + n) c c' ∧
      ∀ i, i < n → c'.nmem (bO + c.nmem (bI + i)) = i := by
  have e0 := Exec.constN (P := P) hw 130803 0 (by omega)
  set c1 := { c with nreg := upd c.nreg 130803 0 }
  have hf1 : PFr InvRG (fun a => bO ≤ a ∧ a < bO + n) c c1 :=
    PFr.nreg (PFr.refl c) (fun r hr => by
      simp only [Machine.upd_apply]; unfold InvRG at hr; split_ifs <;> omega)
  obtain ⟨c', k, e, hk, hw', hi', hn', hf', hI'⟩ := forN (P := P) (W := W) (ri := 130803)
    (rn := 130802) (body := invBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130803 = j ∧ c'.nreg 130802 = n ∧
      PFr InvRG (fun a => bO ≤ a ∧ a < bO + n) c c' ∧
      ∀ i, i < j → c'.nmem (bO + c.nmem (bI + i)) = i)
    n 5 (fun j c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c2 hj ⟨hw2, hi2, hn2, hf2, hm2⟩ => by
      have r0 : ∀ r, ¬ InvRG r → c2.nreg r = c.nreg r := hf2.1
      have rI := (r0 130800 (by unfold InvRG; omega)).trans hI
      have rO := (r0 130801 (by unfold InvRG; omega)).trans hO
      have r1 := (r0 130001 (by unfold InvRG; omega)).trans hone
      have mI : c2.nmem (bI + j) = c.nmem (bI + j) := hf2.2.2.2.2 _ (by omega)
      have hv := hlt j hj
      unfold invBody
      exec_block
      all_goals try (config_simp; simp only [rI, rO, r1, hi2, mI]; omega)
      refine ⟨le_refl _, ‹_›, by config_simp; rw [hi2, r1], by config_simp; exact hn2, ?_,
        fun i hi => ?_⟩
      · refine PFr.of_eq hf2 (fun r hr => ?_) (fun a ha => ?_)
        · simp only [Machine.upd_apply]; unfold InvRG at hr; split_ifs <;> omega
        · simp only [rI, rO, hi2, mI]
          rw [Machine.upd_other _ _ _ (by omega)]
      · config_simp
        simp only [rI, rO, hi2, mI, Machine.upd_apply]
        split_ifs with h
        · have e : c.nmem (bI + i) = c.nmem (bI + j) := by omega
          have hin : i < n := by omega
          exact (hinj i j hin hj e).symm
        · have hij : i ≠ j := by rintro rfl; exact h rfl
          exact hm2 i (by omega))
    (j₀ := 0) ⟨e0.wb_right, by simp [c1], by simp [c1, hn], hf1, fun i hi => by omega⟩
    (Nat.zero_le _)
  exact ⟨c', 1 + k, .seq e0 e, by omega, hw', hf', hI'⟩

end proofs

namespace BTree

/-- Well-formedness only reads the queue and the parents in range. -/
theorem OK.congr {R R' : BTree} (hR : R.OK) (hn : R'.n = R.n) (hq : ∀ i, i < R.n → R'.q i = R.q i)
    (hp : ∀ g, g < R.n → g ≠ R.q 0 → R'.par g = R.par g) : R'.OK := by
  refine ⟨by rw [hn]; exact hR.n_pos, fun i hi => ?_, fun i hi j hj h => ?_, fun i h0 hi => ?_⟩
  · rw [hn] at hi ⊢; rw [hq i hi]; exact hR.q_lt i hi
  · rw [hn] at hi hj; rw [hq i hi, hq j hj] at h; exact hR.q_inj i hi j hj h
  · rw [hn] at hi
    obtain ⟨j, hj, hqj⟩ := hR.par_lt i h0 hi
    refine ⟨j, hj, ?_⟩
    have hne : R.q i ≠ R.q 0 := fun h => by
      have := hR.q_inj i hi 0 hR.n_pos h; omega
    rwa [hq j (by omega), hq i hi, hp _ (hR.q_lt i hi) hne]

/-- The parent function only reads the queue head and the parents. -/
theorem up_congr {R R' : BTree} (hq0 : R'.q 0 = R.q 0)
    (hp : ∀ g, g < R.n → g ≠ R.q 0 → R'.par g = R.par g) {g : ℕ} (hg : g < R.n) :
    R'.up g = R.up g := by
  unfold up root
  rw [hq0]
  by_cases h : g = R.q 0
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, hp g hg h]

end BTree

end

end Chazelle.Core.Cluster
