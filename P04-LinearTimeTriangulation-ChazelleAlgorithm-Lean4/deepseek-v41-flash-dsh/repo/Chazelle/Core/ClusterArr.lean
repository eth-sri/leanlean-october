module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.ClusterTables

/-!
# WP-I, part 26: three generic array loops

For `i < n`:
* `affStmt`: `OUT[i] := a + i`;
* `shStmt`: `OUT[i] := a + IN[i]`;
* `eqStmt`: `OUT[i] := 1` if `IN[i] = i`, else `0`.

Registers: `130550` (`OUT`), `130551` (`IN`), `130552` (`n`), `130553` (`a`); scratch `130554`
(the counter), `130555`, `130556`.  They read `130001 = 1` and `130009 = 0`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-- The scratch registers of the array loops. -/
def ArrRG (r : ℕ) : Prop := 130554 ≤ r ∧ r ≤ 130556

/-- `OUT[i] := a + i`. -/
def affBody : Stmt := block [.addN 130555 130553 130554, .addN 130556 130550 130554,
  .storeN 130556 130555, .addN 130554 130554 130001]

/-- **Affine fill.** -/
def affStmt : Stmt := .seq (.instr (.constN 130554 0)) (.whileLtN 130554 130552 affBody)

/-- `OUT[i] := a + IN[i]`. -/
def shBody : Stmt := block [.addN 130555 130551 130554, .loadN 130555 130555,
  .addN 130555 130553 130555, .addN 130556 130550 130554, .storeN 130556 130555,
  .addN 130554 130554 130001]

/-- **Shifted copy.** -/
def shStmt : Stmt := .seq (.instr (.constN 130554 0)) (.whileLtN 130554 130552 shBody)

/-- `OUT[i] := [IN[i] = i]`. -/
def eqBody : Stmt := .seq (block [.addN 130555 130551 130554, .loadN 130555 130555,
    .addN 130556 130550 130554, .storeN 130556 130009])
  (.seq (.ifLtN 130555 130554 .skip (.ifLtN 130554 130555 .skip (.instr (.storeN 130556 130001))))
    (.instr (.addN 130554 130554 130001)))

/-- **Equality flags.** -/
def eqStmt : Stmt := .seq (.instr (.constN 130554 0)) (.whileLtN 130554 130552 eqBody)

section proofs

variable {P : Polygon} {W : ℕ}

/-- The common frame of the three loops. -/
theorem arr_start {c : Config} (hw : WordsBounded W c) {bO n : ℕ} :
    Exec P W (.instr (.constN 130554 0)) c { c with nreg := upd c.nreg 130554 0 } 1 ∧
    PFr ArrRG (fun a => bO + 0 ≤ a ∧ a < bO + n) c { c with nreg := upd c.nreg 130554 0 } := by
  refine ⟨Exec.constN (P := P) hw 130554 0 (⋄), PFr.nreg (PFr.refl c) (fun r hr => ?_)⟩
  simp only [Machine.upd_apply]; unfold ArrRG at hr; split_ifs <;> omega

/-- **Affine fill**: `OUT[i] = a + i` for `i < n`. -/
theorem affStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {bO n a : ℕ} (hO : c.nreg 130550 = bO) (hn : c.nreg 130552 = n) (ha : c.nreg 130553 = a)
    (hwO : bO + n ≤ W) (hwa : a + n ≤ W) :
    ∃ c' k, Exec P W affStmt c c' k ∧ k ≤ 6 * n + 3 ∧ WordsBounded W c' ∧
      PFr ArrRG (fun x => bO ≤ x ∧ x < bO + n) c c' ∧ ∀ i, i < n → c'.nmem (bO + i) = a + i := by
  obtain ⟨e0, hf1⟩ := arr_start (P := P) (bO := bO) (n := n) hw
  obtain ⟨c', k, e, hk, hw', -, hf', hI⟩ := mapLoop (P := P) (W := W) (ri := 130554)
    (rn := 130552) (body := affBody) (Rg := ArrRG) (by unfold ArrRG; omega)
    (by unfold ArrRG; omega) (bOut := bO) (n := n) (j₀ := 0) (B := 4) (fun i => a + i)
    e0.wb_right (⍟ Machine.upd_same)
    (by simp only; rw [Machine.upd_other _ _ _ (⋄)]; exact hn) (Nat.zero_le _)
    (fun j c2 _ hjn hw2 hi2 hf2 => by
      have r0 := (hf1.trans hf2).1
      have rO := (r0 130550 (by unfold ArrRG; omega)).trans hO
      have ra := (r0 130553 (by unfold ArrRG; omega)).trans ha
      have r1 := (r0 130001 (by unfold ArrRG; omega)).trans hone
      unfold affBody
      exec_block
      all_goals try (config_simp; simp only [rO, ra, r1, hi2]; omega)
      refine ⟨le_refl _, by config_simp; rw [hi2, r1], fun r hr => ?_, rfl, rfl, rfl, ?_⟩
      · simp only [Machine.upd_apply]; unfold ArrRG at hr; split_ifs <;> omega
      · config_simp; simp only [rO, ra, hi2])
  refine ⟨c', 1 + k, .seq e0 e, ⋄, hw', (hf1.trans hf').mono (fun r h => h)
    (fun x hx => by obtain ⟨h1, h2⟩ := hx; exact ⟨⋄, h2⟩),
    fun i hi => hI i (Nat.zero_le _) hi⟩

/-- **Shifted copy**: `OUT[i] = a + IN[i]` for `i < n`. -/
theorem shStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {bO bI n a : ℕ} (hO : c.nreg 130550 = bO) (hI : c.nreg 130551 = bI)
    (hn : c.nreg 130552 = n) (ha : c.nreg 130553 = a)
    (hwO : bO + n ≤ W) (hwI : bI + n ≤ W) (hd : bO + n ≤ bI ∨ bI + n ≤ bO)
    (hwa : ∀ i, i < n → a + c.nmem (bI + i) ≤ W) :
    ∃ c' k, Exec P W shStmt c c' k ∧ k ≤ 8 * n + 3 ∧ WordsBounded W c' ∧
      PFr ArrRG (fun x => bO ≤ x ∧ x < bO + n) c c' ∧
      ∀ i, i < n → c'.nmem (bO + i) = a + c.nmem (bI + i) := by
  obtain ⟨e0, hf1⟩ := arr_start (P := P) (bO := bO) (n := n) hw
  obtain ⟨c', k, e, hk, hw', -, hf', hI'⟩ := mapLoop (P := P) (W := W) (ri := 130554)
    (rn := 130552) (body := shBody) (Rg := ArrRG) (by unfold ArrRG; omega)
    (by unfold ArrRG; omega) (bOut := bO) (n := n) (j₀ := 0) (B := 6)
    (fun i => a + c.nmem (bI + i)) e0.wb_right (⍟ Machine.upd_same)
    (by simp only; rw [Machine.upd_other _ _ _ (⋄)]; exact hn) (Nat.zero_le _)
    (fun j c2 _ hjn hw2 hi2 hf2 => by
      have hf12 := hf1.trans hf2
      have r0 : ∀ r, ¬ ArrRG r → c2.nreg r = c.nreg r := hf12.1
      have rO := (r0 130550 (by unfold ArrRG; omega)).trans hO
      have rI := (r0 130551 (by unfold ArrRG; omega)).trans hI
      have ra := (r0 130553 (by unfold ArrRG; omega)).trans ha
      have r1 := (r0 130001 (by unfold ArrRG; omega)).trans hone
      have mI : c2.nmem (bI + j) = c.nmem (bI + j) := hf12.2.2.2.2 _ (⋄)
      have := hwa j hjn
      unfold shBody
      exec_block
      all_goals try (config_simp; simp only [rO, rI, ra, r1, hi2, mI]; omega)
      refine ⟨le_refl _, by config_simp; rw [hi2, r1], fun r hr => ?_, rfl, rfl, rfl, ?_⟩
      · simp only [Machine.upd_apply]; unfold ArrRG at hr; split_ifs <;> omega
      · config_simp; simp only [rO, rI, ra, hi2, mI])
  refine ⟨c', 1 + k, .seq e0 e, ⋄, hw', (hf1.trans hf').mono (fun r h => h)
    (fun x hx => by obtain ⟨h1, h2⟩ := hx; exact ⟨⋄, h2⟩),
    fun i hi => hI' i (Nat.zero_le _) hi⟩

/-- **Equality flags**: `OUT[i] = 1` if `IN[i] = i`, else `0`, for `i < n`. -/
theorem eqStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    (hzero : c.nreg 130009 = 0) {bO bI n : ℕ} (hO : c.nreg 130550 = bO)
    (hI : c.nreg 130551 = bI) (hn : c.nreg 130552 = n)
    (hwO : bO + n ≤ W) (hwI : bI + n ≤ W) (hd : bO + n ≤ bI ∨ bI + n ≤ bO) :
    ∃ c' k, Exec P W eqStmt c c' k ∧ k ≤ 12 * n + 3 ∧ WordsBounded W c' ∧
      PFr ArrRG (fun x => bO ≤ x ∧ x < bO + n) c c' ∧
      ∀ i, i < n → c'.nmem (bO + i) = if c.nmem (bI + i) = i then 1 else 0 := by
  obtain ⟨e0, hf1⟩ := arr_start (P := P) (bO := bO) (n := n) hw
  obtain ⟨c', k, e, hk, hw', -, hf', hI'⟩ := mapLoop (P := P) (W := W) (ri := 130554)
    (rn := 130552) (body := eqBody) (Rg := ArrRG) (by unfold ArrRG; omega)
    (by unfold ArrRG; omega) (bOut := bO) (n := n) (j₀ := 0) (B := 10)
    (fun i => if c.nmem (bI + i) = i then 1 else 0) e0.wb_right (by simp only [Machine.upd_same])
    (by simp only; rw [Machine.upd_other _ _ _ (by omega)]; exact hn) (Nat.zero_le _)
    (fun j c2 _ hjn hw2 hi2 hf2 => by
      have hf12 := hf1.trans hf2
      have r0 : ∀ r, ¬ ArrRG r → c2.nreg r = c.nreg r := hf12.1
      have rO := (r0 130550 (by unfold ArrRG; omega)).trans hO
      have rI := (r0 130551 (by unfold ArrRG; omega)).trans hI
      have r0' := (r0 130009 (by unfold ArrRG; omega)).trans hzero
      have r1 := (r0 130001 (by unfold ArrRG; omega)).trans hone
      have mI : c2.nmem (bI + j) = c.nmem (bI + j) := hf12.2.2.2.2 _ (by omega)
      obtain ⟨c3, k3, e3, hk3, hw3, h3v, h3a, h3i, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3,
          Exec P W (block [.addN 130555 130551 130554, .loadN 130555 130555,
            .addN 130556 130550 130554, .storeN 130556 130009]) c2 c3 k3 ∧ k3 = 4 ∧
          WordsBounded W c3 ∧ c3.nreg 130555 = c.nmem (bI + j) ∧ c3.nreg 130556 = bO + j ∧
          c3.nreg 130554 = j ∧ (∀ r, ¬ ArrRG r → c3.nreg r = c2.nreg r) ∧
          c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output ∧
          c3.nmem = upd c2.nmem (bO + j) 0 := by
        exec_block
        all_goals try (config_simp; simp only [rO, rI, hi2, mI]; omega)
        refine ⟨rfl, ‹_›, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, ?_⟩
        · config_simp; simp only [rI, hi2, mI]
        · config_simp; simp only [rO, hi2]
        · config_simp; exact hi2
        · simp only [Machine.upd_apply]; unfold ArrRG at hr; split_ifs <;> omega
        · config_simp; simp only [rO, hi2, r0']
      have hone3 : c3.nreg 130001 = 1 := (h3r _ (by unfold ArrRG; omega)).trans r1
      -- the test and the increment
      have hfin : ∀ c4 k4, Exec P W (.ifLtN 130555 130554 .skip
          (.ifLtN 130554 130555 .skip (.instr (.storeN 130556 130001)))) c3 c4 k4 →
          c4.nreg = c3.nreg → c4.rreg = c3.rreg → c4.rmem = c3.rmem → c4.output = c3.output →
          c4.nmem = upd c2.nmem (bO + j) (if c.nmem (bI + j) = j then 1 else 0) → k4 ≤ 5 →
          ∃ c' k, Exec P W eqBody c2 c' k ∧ k ≤ 10 ∧ c'.nreg 130554 = j + 1 ∧
            (∀ r, ¬ ArrRG r → c'.nreg r = c2.nreg r) ∧ c'.rreg = c2.rreg ∧
            c'.rmem = c2.rmem ∧ c'.output = c2.output ∧
            c'.nmem = upd c2.nmem (bO + j) (if c.nmem (bI + j) = j then 1 else 0) := by
        intro c4 k4 e4 hr4 hrr4 hrm4 ho4 hm4 hk4
        have hw4 := e4.wb_right
        have e5 := Exec.addN (P := P) hw4 130554 130554 130001 (by
          rw [hr4, h3i, hone3]; omega)
        refine ⟨_, k3 + (k4 + 1), .seq e3 (.seq e4 e5), by omega, by simp [hr4, h3i, hone3],
          fun r hr => ?_, hrr4.trans hrr3, hrm4.trans hrm3, ho4.trans ho3, by simp [hm4]⟩
        simp only [Machine.upd_apply]
        rw [ite_eq_right (by unfold ArrRG at hr; omega), hr4, h3r r hr]
      by_cases h1 : c3.nreg 130555 < c3.nreg 130554
      · refine hfin c3 (0 + 1) (.ifLtN_true h1 (.skip hw3)) rfl rfl rfl rfl ?_ (by omega)
        rw [hm3, ite_eq_right (by rw [h3v, h3i] at h1; omega)]
      · by_cases h2 : c3.nreg 130554 < c3.nreg 130555
        · refine hfin c3 (0 + 1 + 2) (.ifLtN_false h1 (.ifLtN_true h2 (.skip hw3))) rfl rfl rfl
            rfl ?_ (by omega)
          rw [hm3, ite_eq_right (by rw [h3v, h3i] at h2; omega)]
        · have e4 := Exec.storeN (P := P) hw3 130556 130001
          refine hfin _ (1 + 2 + 2) (.ifLtN_false h1 (.ifLtN_false h2 e4)) rfl rfl rfl rfl ?_
            (by omega)
          show upd c3.nmem (c3.nreg 130556) (c3.nreg 130001) = _
          rw [hm3, h3a, hone3, ite_eq_left (by rw [h3v, h3i] at h1 h2; omega)]
          funext x
          simp only [Machine.upd_apply]
          split_ifs <;> rfl)
  refine ⟨c', 1 + k, .seq e0 e, by omega, hw', (hf1.trans hf').mono (fun r h => h)
    (fun x hx => by obtain ⟨h1, h2⟩ := hx; exact ⟨by omega, h2⟩),
    fun i hi => hI' i (Nat.zero_le _) hi⟩

end proofs

end

end Chazelle.Core.Cluster
