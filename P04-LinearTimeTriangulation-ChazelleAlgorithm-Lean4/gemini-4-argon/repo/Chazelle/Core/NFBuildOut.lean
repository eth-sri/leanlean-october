module

public import Chazelle.Core.NFBuildRegFill

/-!
# WP-C (BuildNF), RAM part 18: the sequence table and the header

* `seqLoop_exec`: `QT[j] = j` for `j < A`;
* `hdrS_exec`: the header of the normal form at `H`: `K`, `A`, `R`, the table bases `CT`, `AT`,
  `RT`, `QT`, `LT`, an (empty) decomposition, root `0`, and the handle into `r40003`.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- The sequence table. -/
def seqLoop : Stmt :=
  .whileLtN 43201 43102 (block [.addN 43230 44004 43201, .storeN 43230 43201,
    .addN 43201 43201 43011])

theorem wr_seqLoop : wrM (fun r => decide (r = 43201 ∨ r = 43230)) seqLoop = true := by decide

/-- The memory with the sequence table of length `j` at `QT`. -/
def seqMem (m : ℕ → ℕ) (QT j a : ℕ) : ℕ := if QT ≤ a ∧ a < QT + j then a - QT else m a

section exec

variable {P : Polygon} {W : ℕ}

/-- **The sequence table.** -/
theorem seqLoop_exec (d : Config) (hw : WordsBounded W d) {A QT : ℕ} (hA : d.nreg 43102 = A)
    (hQT : d.nreg 44004 = QT) (h1 : d.nreg 43011 = 1) (hi : d.nreg 43201 = 0)
    (hQW : QT + A ≤ W) :
    ∃ d' k, Exec P W seqLoop d d' k ∧ k ≤ 5 * A + 2 ∧ WordsBounded W d' ∧
      FrameM (fun r => decide (r = 43201 ∨ r = 43230)) d d' ∧
      d'.nmem = seqMem d.nmem QT A := by
  obtain ⟨d', k, e, ⟨hw', j, hj', hjA, hf, hm'⟩, htest, hk⟩ := Exec.whileLtN_potential
    (P := P) (W := W) (a := 43201) (b := 43102) (body := _)
    (fun e => WordsBounded W e ∧ ∃ j, e.nreg 43201 = j ∧ j ≤ A ∧
      FrameM (fun r => decide (r = 43201 ∨ r = 43230)) d e ∧ e.nmem = seqMem d.nmem QT j)
    (fun e => 5 * (A - e.nreg 43201)) (fun e he => he.1)
    (fun e ⟨hwe, j, hje, hjA, hfe, hme⟩ htest => by
      have r1 : e.nreg 44004 = QT := by rw [hfe.1 _ (by decide), hQT]
      have r2 : e.nreg 43011 = 1 := by rw [hfe.1 _ (by decide), h1]
      have r3 : e.nreg 43102 = A := by rw [hfe.1 _ (by decide), hA]
      rw [hje, r3] at htest
      have X : ∃ e' k, Exec P W (block [.addN 43230 44004 43201, .storeN 43230 43201,
          .addN 43201 43201 43011]) e e' k ∧ k = 3 ∧ e'.nreg 43201 = j + 1 ∧
          e'.nmem = seqMem d.nmem QT (j + 1) := by
        exec_block
        · rw [r1, hje]; omega
        · config_simp; rw [hje, r2]; omega
        · refine ⟨rfl, ?_, ?_⟩ <;> config_simp
          · rw [hje, r2]
          · rw [r1, hje, hme]
            funext a
            simp only [upd_apply, seqMem]
            split_ifs <;> omega
      obtain ⟨e', k, x, hk, hj', hm'⟩ := X
      exact ⟨e', k, x, ⟨x.wb_right, j + 1, hj', by omega, hfe.trans (exec_frameM x (by decide)),
        hm'⟩, by rw [hj', hje]; omega⟩)
    ⟨hw, 0, hi, Nat.zero_le _, FrameM.refl _ _, by
      funext a; simp only [seqMem]; rw [ite_eq_right (by omega)]⟩
  have hjA' : j = A := by
    rw [hj', hf.1 _ (by decide), hA] at htest; omega
  subst hjA'
  exact ⟨d', k, e, by rw [hi] at hk; omega, hw', hf, hm'⟩

end exec

/-- The header of the normal form at `H = r44000`, and the handle into `r40003`. -/
def hdrB : Stmt :=
  block [.copyN 43231 44000, .storeN 43231 43002, .addN 43231 43231 43011,
    .storeN 43231 43102, .addN 43231 43231 43011, .storeN 43231 43200,
    .addN 43231 43231 43011, .storeN 43231 44001, .addN 43231 43231 43011,
    .storeN 43231 44002, .addN 43231 43231 43011, .storeN 43231 44003,
    .addN 43231 43231 43011, .storeN 43231 44004, .addN 43231 43231 43011,
    .storeN 43231 44005, .addN 43231 43231 43011, .storeN 43231 44000,
    .addN 43231 43231 43011, .storeN 43231 43010, .addN 43231 43231 43011,
    .storeN 43231 44000, .addN 43231 43231 43011, .storeN 43231 43010,
    .copyN 40003 44000]

theorem wr_hdrB : wrM (fun r => decide (r = 43231 ∨ r = 40003)) hdrB = true := by decide

/-- The twelve header words. -/
def hdrW (K A R CT AT RT QT LT H : ℕ) (f : ℕ) : ℕ :=
  if f = 0 then K else if f = 1 then A else if f = 2 then R else if f = 3 then CT
  else if f = 4 then AT else if f = 5 then RT else if f = 6 then QT else if f = 7 then LT
  else if f = 8 then H else if f = 9 then 0 else if f = 10 then H else 0

section exec

variable {P : Polygon} {W : ℕ}

/-- **The header.** -/
theorem hdrB_exec (d : Config) (hw : WordsBounded W d) {K A R CT AT RT QT LT H : ℕ}
    (hH : d.nreg 44000 = H) (hK : d.nreg 43002 = K) (hA : d.nreg 43102 = A)
    (hR : d.nreg 43200 = R) (hCT : d.nreg 44001 = CT) (hAT : d.nreg 44002 = AT)
    (hRT : d.nreg 44003 = RT) (hQT : d.nreg 44004 = QT) (hLT : d.nreg 44005 = LT)
    (h0 : d.nreg 43010 = 0) (h1 : d.nreg 43011 = 1) (hHW : H + 12 ≤ W) :
    ∃ d' k, Exec P W hdrB d d' k ∧ k = 25 ∧ WordsBounded W d' ∧ d'.nreg 40003 = H ∧
      (∀ f, f < 12 → d'.nmem (H + f) = hdrW K A R CT AT RT QT LT H f) ∧
      (∀ a, (a < H ∨ H + 12 ≤ a) → d'.nmem a = d.nmem a) := by
  suffices X : ∃ d' k, Exec P W hdrB d d' k ∧ k = 25 ∧ d'.nreg 40003 = H ∧
      (∀ f, f < 12 → d'.nmem (H + f) = hdrW K A R CT AT RT QT LT H f) ∧
      (∀ a, (a < H ∨ H + 12 ≤ a) → d'.nmem a = d.nmem a) by
    obtain ⟨d', k, x, hk, a1, a2, a3⟩ := X
    exact ⟨d', k, x, hk, x.wb_right, a1, a2, a3⟩
  unfold hdrB
  exec_block
  all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [hH, h1]; omega)
    | skip
  refine ⟨rfl, ?_, fun f hf => ?_, fun a ha => ?_⟩ <;> config_simp
  · rw [hH]
  · simp only [hH, hK, hA, hR, hCT, hAT, hRT, hQT, hLT, h0, h1, upd_apply, hdrW]
    interval_cases f <;> ifs_omega
  · simp only [hH, h1, upd_apply]
    ifs_omega

end exec

end

end BuildRam

end Chazelle.Core
