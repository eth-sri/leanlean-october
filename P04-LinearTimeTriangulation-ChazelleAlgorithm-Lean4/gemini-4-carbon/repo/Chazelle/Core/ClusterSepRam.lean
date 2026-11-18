module

public import Chazelle.Core.ClusterPassMath

/-!
# WP-I, part 31: releasing the separator and pushing the classes

* `sepStmt`: for `i ∈ [lo, hi)`, if `DF[TMP[i]] = 1` then `POS[TMP[i]] := μ` (the separator
  vertices leave the positions); `sepMem` describes the memory, `sepStmt_exec`;
* `pushOne t`: push the class `(E[t], E[t+1])` if it has more than `s` items; `pushOne_exec`.

Registers: `sepStmt` `130300` `lo`, `130301` `hi`, `130650` (`TMP`), `130652` (`POS`), `130653`
(`DF`), `130675` (`μ`), counter `130676`, scratch `130677 … 130679`; `pushOne t` reads
`130670 + t`, `130671 + t` (the class ends), `130674` (`s`), `130700` (`STK`), updates `130701`
(the stack top, twice the number of entries), scratch `130702`, `130703`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## Releasing the separator -/

/-- One position: if `DF[v] = 1` for `v = TMP[i]` then `POS[v] := μ`. -/
def sepBody : Stmt := .seq (block [.addN 130677 130650 130676, .loadN 130678 130677,
    .addN 130677 130653 130678, .loadN 130679 130677])
  (.seq (.ifLtN 130679 130001 .skip (.ifLtN 130001 130679 .skip
    (block [.addN 130677 130652 130678, .storeN 130677 130675])))
    (.instr (.addN 130676 130676 130001)))

/-- **Release the separator.** -/
def sepStmt : Stmt := .seq (.instr (.copyN 130676 130300)) (.whileLtN 130676 130301 sepBody)

/-- The registers written by `sepStmt`. -/
def SepRG (r : ℕ) : Prop := 130676 ≤ r ∧ r ≤ 130679

open Classical in
/-- The memory after the first `j` positions. -/
noncomputable def sepMem (m0 : ℕ → ℕ) (bTMP bPOS bDF μ lo : ℕ) : ℕ → (ℕ → ℕ)
  | 0 => m0
  | j + 1 => if m0 (bDF + m0 (bTMP + (lo + j))) = 1 then
      upd (sepMem m0 bTMP bPOS bDF μ lo j) (bPOS + m0 (bTMP + (lo + j))) μ
    else sepMem m0 bTMP bPOS bDF μ lo j

open Classical in
theorem sepMem_apply (m0 : ℕ → ℕ) (bTMP bPOS bDF μ lo j x : ℕ) :
    sepMem m0 bTMP bPOS bDF μ lo j x =
      if ∃ i, lo ≤ i ∧ i < lo + j ∧ m0 (bDF + m0 (bTMP + i)) = 1 ∧ x = bPOS + m0 (bTMP + i)
      then μ else m0 x := by
  classical
  induction j with
  | zero => simp only [sepMem]; rw [ite_eq_right]; rintro ⟨i, h1, h2, -⟩; omega
  | succ j ih =>
    have hstep : (∃ i, lo ≤ i ∧ i < lo + (j + 1) ∧ m0 (bDF + m0 (bTMP + i)) = 1 ∧
        x = bPOS + m0 (bTMP + i)) ↔ (∃ i, lo ≤ i ∧ i < lo + j ∧ m0 (bDF + m0 (bTMP + i)) = 1 ∧
        x = bPOS + m0 (bTMP + i)) ∨ (m0 (bDF + m0 (bTMP + (lo + j))) = 1 ∧
        x = bPOS + m0 (bTMP + (lo + j))) := by
      constructor
      · rintro ⟨i, a, b, c, d⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < lo + j + 1 by omega) with hi | hi
        · exact Or.inl ⟨i, a, hi, c, d⟩
        · subst hi; exact Or.inr ⟨c, d⟩
      · rintro (⟨i, a, b, c, d⟩ | ⟨c, d⟩)
        · exact ⟨i, a, by omega, c, d⟩
        · exact ⟨lo + j, by omega, by omega, c, d⟩
    simp only [sepMem]
    by_cases h1 : m0 (bDF + m0 (bTMP + (lo + j))) = 1
    · rw [ite_eq_left h1, Machine.upd_apply]
      by_cases hx : x = bPOS + m0 (bTMP + (lo + j))
      · rw [ite_eq_left hx, ite_eq_left (hstep.mpr (Or.inr ⟨h1, hx⟩))]
      · rw [ite_eq_right hx, ih]
        by_cases hex : ∃ i, lo ≤ i ∧ i < lo + j ∧ m0 (bDF + m0 (bTMP + i)) = 1 ∧
            x = bPOS + m0 (bTMP + i)
        · rw [ite_eq_left hex, ite_eq_left (hstep.mpr (Or.inl hex))]
        · rw [ite_eq_right hex, ite_eq_right (fun h => by
            rcases hstep.mp h with h | h
            · exact hex h
            · exact hx h.2)]
    · rw [ite_eq_right h1, ih]
      by_cases hex : ∃ i, lo ≤ i ∧ i < lo + j ∧ m0 (bDF + m0 (bTMP + i)) = 1 ∧
          x = bPOS + m0 (bTMP + i)
      · rw [ite_eq_left hex, ite_eq_left (hstep.mpr (Or.inl hex))]
      · rw [ite_eq_right hex, ite_eq_right (fun h => by
          rcases hstep.mp h with h | h
          · exact hex h
          · exact h1 h.1)]

section proofs

variable {P : Polygon} {W : ℕ}

/-- **Release the separator**: afterwards `POS[v] = μ` for the flagged items of `[lo, hi)`. -/
theorem sepStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {lo hi bTMP bPOS bDF μ : ℕ} (hlo : c.nreg 130300 = lo) (hhi : c.nreg 130301 = hi)
    (hT : c.nreg 130650 = bTMP) (hP : c.nreg 130652 = bPOS) (hD : c.nreg 130653 = bDF)
    (hμ : c.nreg 130675 = μ) (hlh : lo ≤ hi)
    (hit : ∀ i, lo ≤ i → i < hi → c.nmem (bTMP + i) < μ) (hwT : bTMP + hi ≤ W)
    (hwP : bPOS + μ ≤ W) (hwD : bDF + μ ≤ W) (hhiW : hi + 1 ≤ W)
    (hdT : bTMP + hi ≤ bPOS ∨ bPOS + μ ≤ bTMP + lo) (hdD : bDF + μ ≤ bPOS ∨ bPOS + μ ≤ bDF) :
    ∃ c' k, Exec P W sepStmt c c' k ∧ k ≤ 15 * (hi - lo) + 3 ∧ WordsBounded W c' ∧
      c'.nmem = sepMem c.nmem bTMP bPOS bDF μ lo (hi - lo) ∧
      (∀ r, ¬ SepRG r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  classical
  set m0 := c.nmem
  have e0 := Exec.copyN (P := P) hw 130676 130300
  obtain ⟨c', k, e, hk, hw', hi', hn', hm', hr', hrr', hrm', ho', -⟩ := forN (P := P) (W := W)
    (ri := 130676) (rn := 130301) (body := sepBody)
    (fun i c2 => WordsBounded W c2 ∧ c2.nreg 130676 = i ∧ c2.nreg 130301 = hi ∧
      c2.nmem = sepMem m0 bTMP bPOS bDF μ lo (i - lo) ∧
      (∀ r, ¬ SepRG r → c2.nreg r = c.nreg r) ∧ c2.rreg = c.rreg ∧ c2.rmem = c.rmem ∧
      c2.output = c.output ∧ lo ≤ i)
    hi 13 (fun i c2 h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c2 hih ⟨hw2, hi2, hn2, hm2, hr2, hrr2, hrm2, ho2, hlo2⟩ => by
      have r : ∀ x, ¬ SepRG x → c2.nreg x = c.nreg x := hr2
      have rT := (r 130650 (by unfold SepRG; omega)).trans hT
      have rP := (r 130652 (by unfold SepRG; omega)).trans hP
      have rD := (r 130653 (by unfold SepRG; omega)).trans hD
      have rμ := (r 130675 (by unfold SepRG; omega)).trans hμ
      have r1 := (r 130001 (by unfold SepRG; omega)).trans hone
      have hv := hit i hlo2 hih
      set v := m0 (bTMP + i)
      -- reads: `TMP` and `DF` are not written
      have hread : ∀ x, ¬ (bPOS ≤ x ∧ x < bPOS + μ) → c2.nmem x = m0 x := by
        intro x hx
        rw [hm2, sepMem_apply, ite_eq_right]
        rintro ⟨i', a, b, -, rfl⟩
        have := hit i' a (by omega)
        omega
      have mT : c2.nmem (bTMP + i) = v := hread _ (by omega)
      have mD : c2.nmem (bDF + v) = m0 (bDF + v) := hread _ (by omega)
      obtain ⟨c3, k3, e3, hk3, hw3, h3v, h3f, h3r, hrr3, hrm3, ho3, hm3⟩ : ∃ c3 k3, Exec P W
          (block [.addN 130677 130650 130676, .loadN 130678 130677, .addN 130677 130653 130678,
            .loadN 130679 130677]) c2 c3 k3 ∧ k3 = 4 ∧ WordsBounded W c3 ∧ c3.nreg 130678 = v ∧
          c3.nreg 130679 = m0 (bDF + v) ∧
          (∀ x, x ≠ 130677 → x ≠ 130678 → x ≠ 130679 → c3.nreg x = c2.nreg x) ∧
          c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output ∧ c3.nmem = c2.nmem := by
        exec_block
        all_goals first | omega | (config_simp; simp only [rT, rD, hi2, mT]; omega) | skip
        refine ⟨rfl, ‹_›, by config_simp; simp only [rT, hi2, mT], by
          config_simp; simp only [rT, rD, hi2, mT, mD], fun x h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
        simp only [Machine.upd_apply]; split_ifs <;> first | omega
      have r3 : ∀ x, x ≠ 130677 → x ≠ 130678 → x ≠ 130679 → c3.nreg x = c2.nreg x := h3r
      have h3i : c3.nreg 130676 = i := (r3 _ (by omega) (by omega) (by omega)).trans hi2
      have h31 : c3.nreg 130001 = 1 := (r3 _ (by omega) (by omega) (by omega)).trans r1
      have h3P : c3.nreg 130652 = bPOS := (r3 _ (by omega) (by omega) (by omega)).trans rP
      have h3μ : c3.nreg 130675 = μ := (r3 _ (by omega) (by omega) (by omega)).trans rμ
      -- the conditional release
      have hnext1 : m0 (bDF + v) = 1 → sepMem m0 bTMP bPOS bDF μ lo (i + 1 - lo) =
          upd (sepMem m0 bTMP bPOS bDF μ lo (i - lo)) (bPOS + v) μ := by
        intro h
        rw [show i + 1 - lo = i - lo + 1 by omega]
        simp only [sepMem, show lo + (i - lo) = i by omega]
        rw [ite_eq_left h]
      have hnext0 : m0 (bDF + v) ≠ 1 → sepMem m0 bTMP bPOS bDF μ lo (i + 1 - lo) =
          sepMem m0 bTMP bPOS bDF μ lo (i - lo) := by
        intro h
        rw [show i + 1 - lo = i - lo + 1 by omega]
        simp only [sepMem, show lo + (i - lo) = i by omega]
        rw [ite_eq_right h]
      obtain ⟨c4, k4, e4, hk4, hw4, h4m, h4r, hrr4, hrm4, ho4⟩ : ∃ c4 k4, Exec P W
          (.ifLtN 130679 130001 .skip (.ifLtN 130001 130679 .skip
            (block [.addN 130677 130652 130678, .storeN 130677 130675]))) c3 c4 k4 ∧ k4 ≤ 6 ∧
          WordsBounded W c4 ∧ c4.nmem = sepMem m0 bTMP bPOS bDF μ lo (i + 1 - lo) ∧
          (∀ x, x ≠ 130677 → c4.nreg x = c3.nreg x) ∧ c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧
          c4.output = c3.output := by
        by_cases h1 : c3.nreg 130679 < c3.nreg 130001
        · refine ⟨c3, _, .ifLtN_true h1 (.skip hw3), by omega, hw3, ?_, fun _ _ => rfl, rfl, rfl,
            rfl⟩
          rw [h3f, h31] at h1
          rw [hnext0 (by omega), hm3, hm2]
        · by_cases h2 : c3.nreg 130001 < c3.nreg 130679
          · refine ⟨c3, _, .ifLtN_false h1 (.ifLtN_true h2 (.skip hw3)), by omega, hw3, ?_,
              fun _ _ => rfl, rfl, rfl, rfl⟩
            rw [h3f, h31] at h2
            rw [hnext0 (by omega), hm3, hm2]
          · have hf1 : m0 (bDF + v) = 1 := by rw [h3f, h31] at h1 h2; omega
            obtain ⟨c5, k5, e5, hk5, hw5, h5m, h5r, hrr5, hrm5, ho5⟩ : ∃ c5 k5, Exec P W
                (block [.addN 130677 130652 130678, .storeN 130677 130675]) c3 c5 k5 ∧ k5 = 2 ∧
                WordsBounded W c5 ∧ c5.nmem = upd c3.nmem (bPOS + v) μ ∧
                (∀ x, x ≠ 130677 → c5.nreg x = c3.nreg x) ∧ c5.rreg = c3.rreg ∧
                c5.rmem = c3.rmem ∧ c5.output = c3.output := by
              exec_block
              · rw [h3P, h3v]; omega
              · refine ⟨rfl, ‹_›, by config_simp; rw [h3P, h3v, h3μ], fun x hx => ?_, rfl, rfl,
                  rfl⟩
                simp only [Machine.upd_apply, hx, ite_false]
            refine ⟨c5, _, .ifLtN_false h1 (.ifLtN_false h2 e5), by omega, hw5, ?_, h5r, hrr5,
              hrm5, ho5⟩
            rw [h5m, hnext1 hf1, hm3, hm2]
      have h4i : c4.nreg 130676 = i := (h4r _ (by omega)).trans h3i
      have h41 : c4.nreg 130001 = 1 := (h4r _ (by omega)).trans h31
      have e6 := Exec.addN (P := P) hw4 130676 130676 130001 (by rw [h4i, h41]; omega)
      refine ⟨_, k3 + (k4 + 1), .seq e3 (.seq e4 e6), by omega, e6.wb_right, by simp [h4i, h41],
        ?_, h4m, fun x hx => ?_, hrr4.trans (hrr3.trans hrr2), hrm4.trans (hrm3.trans hrm2),
        ho4.trans (ho3.trans ho2), by omega⟩
      · simp only [Machine.upd_apply]; rw [ite_eq_right (by omega), h4r _ (by omega),
          r3 _ (by omega) (by omega) (by omega)]; exact hn2
      · simp only [Machine.upd_apply]
        unfold SepRG at hx
        rw [ite_eq_right (by omega), h4r _ (by omega), r3 _ (by omega) (by omega) (by omega)]
        exact hr2 x (by unfold SepRG; omega))
    (j₀ := lo) ⟨e0.wb_right, by simp [hlo], by
      simp only [Machine.upd_apply]; rw [ite_eq_right (by omega)]; exact hhi,
      by simp [m0, sepMem], fun r hr => by
        simp only [Machine.upd_apply]; rw [ite_eq_right (by unfold SepRG at hr; omega)],
      rfl, rfl, rfl, le_rfl⟩ hlh
  exact ⟨c', 1 + k, .seq e0 e, by omega, hw', hm', hr', hrr', hrm', ho'⟩

end proofs

/-! ## Pushing a class -/

/-- Push the class `(E[t], E[t+1])` if it has more than `s` items. -/
def pushOne (t : ℕ) : Stmt := .seq (.instr (.subN 130702 (130671 + t) (130670 + t)))
  (.ifLtN 130674 130702 (block [.addN 130703 130700 130701, .storeN 130703 (130670 + t),
    .addN 130703 130703 130001, .storeN 130703 (130671 + t), .addN 130701 130701 130001,
    .addN 130701 130701 130001]) .skip)

section push

variable {P : Polygon} {W : ℕ}

/-- **Push a class.** -/
theorem pushOne_exec {c : Config} (hw : WordsBounded W c) (t : ℕ) (ht : t < 3)
    (hone : c.nreg 130001 = 1) {a b s bS tp : ℕ} (ha : c.nreg (130670 + t) = a)
    (hb : c.nreg (130671 + t) = b) (hs : c.nreg 130674 = s) (hS : c.nreg 130700 = bS)
    (htp : c.nreg 130701 = tp) (hwS : bS + tp + 2 ≤ W) :
    ∃ c' k, Exec P W (pushOne t) c c' k ∧ k ≤ 9 ∧ WordsBounded W c' ∧
      (c'.nmem = if s < b - a then upd (upd c.nmem (bS + tp) a) (bS + tp + 1) b else c.nmem) ∧
      c'.nreg 130701 = (if s < b - a then tp + 2 else tp) ∧
      (∀ r, r ≠ 130701 → r ≠ 130702 → r ≠ 130703 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c1, e0, hw1, r1, h1d, hm1, hrr1, hrm1, ho1⟩ : ∃ c1,
      Exec P W (.instr (.subN 130702 (130671 + t) (130670 + t))) c c1 1 ∧ WordsBounded W c1 ∧
      (∀ r, r ≠ 130702 → c1.nreg r = c.nreg r) ∧ c1.nreg 130702 = b - a ∧ c1.nmem = c.nmem ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    have e0 := Exec.subN (P := P) hw 130702 (130671 + t) (130670 + t)
    refine ⟨_, e0, e0.wb_right, fun r hr => ?_, by simp [ha, hb], rfl, rfl, rfl, rfl⟩
    simp only [Machine.upd_apply, hr, ite_false]
  by_cases hbig : c1.nreg 130674 < c1.nreg 130702
  · rw [r1 _ (by omega), hs, h1d] at hbig
    obtain ⟨c2, k2, e2, hk2, hw2, h2m, h2t, h2r, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
        (block [.addN 130703 130700 130701, .storeN 130703 (130670 + t),
          .addN 130703 130703 130001, .storeN 130703 (130671 + t), .addN 130701 130701 130001,
          .addN 130701 130701 130001]) c1 c2 k2 ∧ k2 = 6 ∧ WordsBounded W c2 ∧
        c2.nmem = upd (upd c.nmem (bS + tp) a) (bS + tp + 1) b ∧ c2.nreg 130701 = tp + 2 ∧
        (∀ r, r ≠ 130701 → r ≠ 130702 → r ≠ 130703 → c2.nreg r = c.nreg r) ∧
        c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
      have q1 := (r1 130700 (by omega)).trans hS
      have q2 := (r1 130701 (by omega)).trans htp
      have q3 := (r1 130001 (by omega)).trans hone
      have q4 := (r1 (130670 + t) (by omega)).trans ha
      have q5 := (r1 (130671 + t) (by omega)).trans hb
      exec_block
      all_goals first | omega | (config_simp; simp only [q1, q2, q3]; omega) |
        (config_simp; rw [Machine.upd_other _ _ _ (by omega)]; simp only [q1, q2, q3]; omega) |
        skip
      refine ⟨rfl, ‹_›, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
      · config_simp
        rw [Machine.upd_other _ _ _ (show 130670 + t ≠ 130703 by omega),
          Machine.upd_other _ _ _ (show 130671 + t ≠ 130703 by omega)]
        simp only [q1, q2, q3, q4, q5, hm1]
      · config_simp; simp only [q2, q3]
      · simp only [Machine.upd_apply, h1, h3, ite_false]; exact r1 r h2
    refine ⟨c2, 1 + (k2 + 1), .seq e0 (.ifLtN_true (by rw [r1 _ (by omega), hs, h1d]; exact hbig)
      e2), by omega, hw2, by rw [ite_eq_left hbig]; exact h2m, by rw [ite_eq_left hbig]; exact h2t, h2r,
      by rw [hrr2, hrr1], by rw [hrm2, hrm1], by rw [ho2, ho1]⟩
  · rw [r1 _ (by omega), hs, h1d] at hbig
    refine ⟨c1, 1 + (0 + 2), .seq e0 (.ifLtN_false (by rw [r1 _ (by omega), hs, h1d]; exact hbig)
      (.skip hw1)), by omega, hw1, by rw [ite_eq_right hbig, hm1],
      by rw [ite_eq_right hbig, r1 _ (by omega), htp], fun r _ h2 _ => r1 r h2, hrr1, hrm1, ho1⟩

end push

end

end Chazelle.Core.Cluster
