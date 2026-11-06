module

public import Chazelle.Core.UpPhase16
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
set_option maxHeartbeats 16000000

/-!
# WP-J up phase, part 17: the registers of the next grade

`recB_exec` (the new row pointer, the counters and the chain count of the next grade) and
`gamS_exec` (`γ'_{g}` from the setup tables).
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41

@[expose] public section

/-- The registers written by `recB` (besides the allocator). -/
def RecBRG (r : ℕ) : Prop :=
  r = 170055 ∨ r = 170053 ∨ r = 170005 ∨ r = 170012 ∨ r = 170014 ∨ r = 170019 ∨ r = 170010 ∨
    r = 170009 ∨ r = 170008 ∨ r = 170007 ∨ r = 170015 ∨ r = 170016 ∨ r = 170035 ∨ r = 170036

section proofs

variable {P : Polygon} {W : ℕ}

theorem recB_exec {c : Config} (hw : WordsBounded W c) {Al T' g R' h' cnt pg D Q g1 : ℕ}
    (hA : c.nreg ALLOC = Al) (h56 : c.nreg 170056 = T') (h07 : c.nreg 170007 = g)
    (h44 : c.nreg 170044 = R') (h51 : c.nreg 170051 = h') (h08 : c.nreg 170008 = cnt)
    (h10 : c.nreg 170010 = pg) (h03 : c.nreg 170003 = D) (h09 : c.nreg 170009 = Q)
    (h52 : c.nreg 170052 = g1) (h20 : c.nreg 170020 = 1) (hDQ : D + Q < T')
    (hWT : T' + g ≤ W) (hWA : Al + 1 ≤ W) (hWp : pg + pg ≤ W) (hWD : D + Q ≤ W)
    (hWQ : c.nmem (D + Q) + 1 ≤ W) :
    ∃ c' k, Exec P W recB c c' k ∧ k = 16 ∧ WordsBounded W c' ∧
      c'.nmem (T' + g) = R' ∧ c'.nreg ALLOC = Al + 1 ∧ c'.nreg 170005 = h' ∧
      c'.nreg 170012 = cnt ∧ c'.nreg 170014 = R' ∧ c'.nreg 170019 = pg ∧
      c'.nreg 170010 = pg + pg ∧ c'.nreg 170009 = c.nmem (D + Q) ∧
      c'.nreg 170008 = c.nmem (D + Q) + 1 ∧ c'.nreg 170007 = g1 ∧ c'.nreg 170015 = 0 ∧
      c'.nreg 170016 = 0 ∧ c'.nreg 170035 = 0 ∧ c'.nreg 170036 = 1 ∧
      (∀ a, a ≠ T' + g → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ RecBRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  obtain ⟨c1, k1, e1, hk1, hw1, w1, A1, i05, i12, i14, i19, i10, i09, i07, i15, i16, i35, i36,
      m1, fr1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W recB1 c c1 k1 ∧ k1 = 15 ∧ WordsBounded W c1 ∧
      c1.nmem (T' + g) = R' ∧ c1.nreg ALLOC = Al + 1 ∧ c1.nreg 170005 = h' ∧
      c1.nreg 170012 = cnt ∧ c1.nreg 170014 = R' ∧ c1.nreg 170019 = pg ∧
      c1.nreg 170010 = pg + pg ∧ c1.nreg 170009 = c.nmem (D + Q) ∧ c1.nreg 170007 = g1 ∧
      c1.nreg 170015 = 0 ∧ c1.nreg 170016 = 0 ∧ c1.nreg 170035 = 0 ∧ c1.nreg 170036 = 1 ∧
      (∀ a, a ≠ T' + g → c1.nmem a = c.nmem a) ∧
      (∀ r, ¬ RecBRG r → r ≠ ALLOC → c1.nreg r = c.nreg r) ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    rw [hAl] at hA ⊢
    unfold recB1
    exec_block
    all_goals
      try (config_simp; (try simp only [hA, h56, h07, h44, h51, h08, h10, h03, h09, h52, h20]); omega)
    refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun a h1 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
    all_goals try (config_simp <;> (try simp only [hA, h56, h07, h44, h51, h08, h10, h03, h09,
      h52, h20, Machine.upd_apply]) <;> (try split_ifs) <;> first | omega | rfl)
    unfold RecBRG at h1
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have c20 : c1.nreg 170020 = 1 := by
    rw [fr1 _ (by ufo RecBRG) (by rwo [hAl])]; exact h20
  obtain ⟨c2, k2, e2, hk2, hw2, j08, fr2, hm2, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
      (block [.addN 170008 170009 170020]) c1 c2 k2 ∧ k2 = 1 ∧ WordsBounded W c2 ∧
      c2.nreg 170008 = c.nmem (D + Q) + 1 ∧ (∀ r, r ≠ 170008 → c2.nreg r = c1.nreg r) ∧
      c2.nmem = c1.nmem ∧ c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
    exec_block
    all_goals try (config_simp; (try simp only [i09, c20]); omega)
    refine ⟨rfl, ‹_›, by config_simp; simp only [i09, c20], fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have g2 : ∀ r, r ≠ 170008 → c2.nreg r = c1.nreg r := fr2
  refine ⟨c2, k1 + k2, .seq e1 e2, by omega, hw2, by rwx [hm2],
    by rw [g2 _ (by rwo [hAl])]; exact A1, by rwx [g2 _ (by omega)],
    by rwx [g2 _ (by omega)], by rwx [g2 _ (by omega)],
    by rwx [g2 _ (by omega)], by rwx [g2 _ (by omega)],
    by rwx [g2 _ (by omega)], j08, by rwx [g2 _ (by omega)],
    by rwx [g2 _ (by omega)], by rwx [g2 _ (by omega)],
    by rwx [g2 _ (by omega)], by rwx [g2 _ (by omega)],
    fun a ha => by rw [hm2, m1 a ha], fun r h1 h2 => ?_, by rw [hrr2, hrr1], by rw [hrm2, hrm1],
    by rw [ho2, ho1]⟩
  rw [g2 r (fun e => h1 (by ufo RecBRG)), fr1 r h1 h2]

theorem gamA_exec {c : Config} (hw : WordsBounded W c) {S p g1 cb G2 : ℕ}
    (h00 : c.nreg 170000 = S) (h02 : c.nreg 170002 = p) (h07 : c.nreg 170007 = g1)
    (h21 : c.nreg 170021 = 2) (h25 : c.nreg 170025 = 4)
    (hcb : c.nmem (S + p + 4 + g1) = cb) (hG2 : c.nmem (S + 2 + cb) = G2)
    (hW1 : S + p + 4 + g1 ≤ W) (hW2 : S + 2 + cb ≤ W) (hW8 : 8 ≤ W) :
    ∃ c' k, Exec P W gamA c c' k ∧ k = 10 ∧ WordsBounded W c' ∧
      c'.nreg 160024 = 1 ∧ c'.nreg 160080 = 2 ∧ c'.nreg 160021 = S + 2 ∧
      c'.nreg 160003 = g1 ∧ c'.nreg 160032 = G2 ∧
      (∀ r, r ≠ 160024 → r ≠ 160080 → r ≠ 160021 → r ≠ 160003 → r ≠ 170053 → r ≠ 170054 →
        r ≠ 160032 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold gamA
  exec_block
  all_goals try (config_simp; (try simp only [h00, h02, h07, h21, h25, hcb]); omega)
  refine ⟨rfl, ‹_›, by config_simp, by config_simp, by config_simp; simp only [h00, h21],
    by config_simp; exact h07, ?_, fun r a1 a2 a3 a4 a5 a6 a7 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [h00, h02, h07, h21, h25, hcb, hG2]
  · simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])

/-- **`γ'_{g}`** for the grade in `170007`. -/
theorem gamS_exec {c : Config} (hw : WordsBounded W c) {S p g1 : ℕ}
    (h00 : c.nreg 170000 = S) (h02 : c.nreg 170002 = p) (h07 : c.nreg 170007 = g1)
    (h21 : c.nreg 170021 = 2) (h25 : c.nreg 170025 = 4) (hg1 : 1 ≤ g1) (hgp : g1 ≤ p + 1)
    (hS : ∀ i, i ≤ p + 1 → c.nmem (S + 2 + i) = 2 ^ i ∧ c.nmem (S + p + 4 + i) = Cost.ceilBeta i)
    (hWS : S + 2 * p + 6 ≤ W) (hWγ : gradeGran g1 + g1 + 2 ≤ W) (hW8 : 8 ≤ W) :
    ∃ c' k, Exec P W gamS c c' k ∧ k ≤ 9 * g1 + 24 ∧ WordsBounded W c' ∧
      c'.nreg 170011 = gradeGran g1 ∧
      (∀ r, (r < 160000 ∨ 170000 ≤ r) → r ≠ 170053 → r ≠ 170054 → r ≠ 170011 →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hcb := (hS g1 hgp).2
  have hcbl : Cost.ceilBeta g1 ≤ g1 := Cost.ceilBeta_le g1
  have hG2 := (hS (Cost.ceilBeta g1) (by omega)).1
  obtain ⟨c1, k1, e1, hk1, hw1, i24, i80, i21, i03, i32, fr1, hm1, hrr1, hrm1, ho1⟩ :=
    gamA_exec (P := P) hw h00 h02 h07 h21 h25 hcb hG2 (by omega) (by omega) hW8
  have hGg : 2 ^ Cost.ceilBeta g1 ≤ gradeGran g1 := by ufo gradeGran
  obtain ⟨c2, k2, e2, hk2, hw2, j04, fr2, hm2, hrr2, hrm2, ho2⟩ :=
    clogS_exec (P := P) hw1 i21 i03 i24 (fun i hi => by rw [hm1]; exact (hS i (by omega)).1)
      hg1 (by omega)
  have hcl : Nat.clog 2 g1 ≤ g1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hgg : gradeGran g1 = 2 ^ Cost.ceilBeta g1 + g1 * (Nat.clog 2 g1 + 2) := by
    ufring gradeGran fuseLoss
  obtain ⟨c3, k3, e3, hk3, hw3, j32, fr3, hm3, hrr3, hrm3, ho3⟩ :=
    mulS_exec (P := P) (lam := g1) (G2 := 2 ^ Cost.ceilBeta g1) hw2 j04 (by rwx [fr2 _ (by omega) (by omega) (by omega)])
      (by rwx [fr2 _ (by omega) (by omega) (by omega)])
      (by rwx [fr2 _ (by omega) (by omega) (by omega)])
      (by rwx [fr2 _ (by omega) (by omega) (by omega)]) (by rwo [← hgg])
  obtain ⟨c4, k4, e4, hk4, hw4, j11, fr4, hm4, hrr4, hrm4, ho4⟩ : ∃ c4 k4, Exec P W
      (block [.copyN 170011 160032]) c3 c4 k4 ∧ k4 = 1 ∧ WordsBounded W c4 ∧
      c4.nreg 170011 = c3.nreg 160032 ∧ (∀ r, r ≠ 170011 → c4.nreg r = c3.nreg r) ∧
      c4.nmem = c3.nmem ∧ c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧ c4.output = c3.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  refine ⟨c4, k1 + (k2 + (k3 + k4)), .seq e1 (.seq e2 (.seq e3 e4)), by omega, hw4,
    by rw [j11, j32, hgg], fun r h1 h2 h3 h4 => ?_, by rw [hm4, hm3, hm2, hm1],
    by rw [hrr4, hrr3, hrr2, hrr1], by rw [hrm4, hrm3, hrm2, hrm1], by rw [ho4, ho3, ho2, ho1]⟩
  rw [fr4 r h4, fr3 r (by omega) (by omega) (by omega) (by omega),
    fr2 r (by omega) (by omega) (by omega),
    fr1 r (by omega) (by omega) (by omega) (by omega) h2 h3 (by omega)]

end proofs

end

end Chazelle.Core.Up
