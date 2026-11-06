module

public import Chazelle.Core.UpPhase6
public import Chazelle.Core.UpPhaseArith
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
set_option maxHeartbeats 16000000

/-!
# WP-J up phase, part 7: the length and the descriptor of a chain

* `lenS`: `len = min (2^g, n - 1 - s)` in `170017` (`lenS_exec`);
* `descU`: the descriptor of chain `(g, i)` in `170030`: grade `0` by `desc0S`, grade `g ≥ 1` by
  the union of the children `2i`, `2i + 1` of grade `g - 1` (their row at `170014`, the entry
  offset `6i` in `170035`, `2i + 1` in `170036`, the child count in `170012`), or the child `2i`
  itself (`descU_exec`).
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41 SweepPrim SignK WalkKey

@[expose] public section

/-- `len := min (2^g, n - 1 - s)`. -/
def lenS : Stmt := .seq (block [.subN 170033 170028 170016])
  (.ifLtN 170033 170010 (block [.copyN 170017 170033]) (block [.copyN 170017 170010]))

/-- The descriptor of a chain of grade `g ≥ 1`. -/
def descGS : Stmt := .seq (block [.addN 170034 170014 170035, .loadN 160035 170034])
  (.ifLtN 170036 170012
    (.seq (block [.addN 170034 170034 170022, .loadN 160036 170034])
      (.seq unionS (block [.copyN 170030 160037])))
    (block [.copyN 170030 160035]))

/-- **The descriptor of chain `(g, i)`.** -/
def descU : Stmt := .ifLtN 170007 170020 (.seq desc0S (block [.copyN 170030 170060])) descGS

section proofs

variable {P : Polygon} {W : ℕ}

theorem lenS_exec {c : Config} (hw : WordsBounded W c) {n1 s pg : ℕ}
    (h28 : c.nreg 170028 = n1) (h16 : c.nreg 170016 = s) (h10 : c.nreg 170010 = pg) :
    ∃ c' k, Exec P W lenS c c' k ∧ k ≤ 4 ∧ WordsBounded W c' ∧
      c'.nreg 170017 = min pg (n1 - s) ∧
      (∀ r, r ≠ 170017 → r ≠ 170033 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c1, k1, e1, hk1, hw1, i33, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      (block [.subN 170033 170028 170016]) c c1 k1 ∧ k1 = 1 ∧ WordsBounded W c1 ∧
      c1.nreg 170033 = n1 - s ∧ (∀ r, r ≠ 170033 → c1.nreg r = c.nreg r) ∧
      c1.nmem = c.nmem ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp; rw [h28, h16], fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
    simp
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have c10 : c1.nreg 170010 = pg := by rwx [fr1 _ (by decide)]
  by_cases h : c1.nreg 170033 < c1.nreg 170010
  · obtain ⟨c2, k2, e2, hk2, hw2, i17, fr2, hm2, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
        (block [.copyN 170017 170033]) c1 c2 k2 ∧ k2 = 1 ∧ WordsBounded W c2 ∧
        c2.nreg 170017 = c1.nreg 170033 ∧ (∀ r, r ≠ 170017 → c2.nreg r = c1.nreg r) ∧
        c2.nmem = c1.nmem ∧ c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
      exec_block
      refine ⟨rfl, ‹_›, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
      simp
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
    refine ⟨c2, k1 + (k2 + 1), .seq e1 (.ifLtN_true h e2), by omega, hw2, ?_,
      fun r a1 a2 => by rw [fr2 r a1, fr1 r a2], by rw [hm2, hm1], by rw [hrr2, hrr1],
      by rw [hrm2, hrm1], by rw [ho2, ho1]⟩
    rw [i17, i33]; rwo [i33, c10] at h
  · obtain ⟨c2, k2, e2, hk2, hw2, i17, fr2, hm2, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
        (block [.copyN 170017 170010]) c1 c2 k2 ∧ k2 = 1 ∧ WordsBounded W c2 ∧
        c2.nreg 170017 = c1.nreg 170010 ∧ (∀ r, r ≠ 170017 → c2.nreg r = c1.nreg r) ∧
        c2.nmem = c1.nmem ∧ c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
      exec_block
      refine ⟨rfl, ‹_›, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
      simp
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
    refine ⟨c2, k1 + (k2 + 2), .seq e1 (.ifLtN_false h e2), by omega, hw2, ?_,
      fun r a1 a2 => by rw [fr2 r a1, fr1 r a2], by rw [hm2, hm1], by rw [hrr2, hrr1],
      by rw [hrm2, hrm1], by rw [ho2, ho1]⟩
    rw [i17, c10]; rwo [i33, c10] at h

/-- **The descriptor of a grade-0 chain** (the edge `v_i v_{i+1}`). -/
theorem descU_exec0 (hG : GoodEnv P) (hWn : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {TD hp i : ℕ} (h07 : c.nreg 170007 = 0) (h20 : c.nreg 170020 = 1) (hA : c.nreg ALLOC = TD)
    (h04 : c.nreg 170004 = hp) (h16 : c.nreg 170016 = i) (h01 : c.nreg 170001 = P.n)
    (h23 : c.nreg 170023 = 5) (hi : i + 2 ≤ P.n) (hH : HostAt c.nmem hp (Host.whole P.n))
    (hhp : hp + 7 ≤ TD) (hW : TD + 5 ≤ W) (hW8 : 8 ≤ W) :
    ∃ c' k, Exec P W descU c c' k ∧ k ≤ 1902 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = TD + 5 ∧ c'.nreg 170030 = TD ∧ c'.nmem TD = hp ∧
      (∀ C : Chain, C.P = Qof P → C.s = gradeStart 0 i → C.m = gradeLen P.n 0 i →
        ChainDescAt c'.nmem TD (Qof P) (Host.whole P.n) C) ∧
      (∀ a, (a < TD ∨ TD + 5 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ D0RG r → r ≠ 170030 → bandOf r ≠ bBrute → Bk r = false → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      (∀ r, Bk r = false → bandOf r ≠ bUp → bandOf r ≠ bBrute → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  obtain ⟨c1, k1, e1, hk1, hw1, h1A, h160, w0, hdesc, hm1, fr1, frr1, hrm1, ho1⟩ :=
    desc0S_exec hG hWn hw hA h04 h16 h01 h20 h23 hi hW hW8
  obtain ⟨c2, k2, e2, hk2, hw2, o30, fr2, hm2, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
      (block [.copyN 170030 170060]) c1 c2 k2 ∧ k2 = 1 ∧ WordsBounded W c2 ∧
      c2.nreg 170030 = c1.nreg 170060 ∧ (∀ r, r ≠ 170030 → c2.nreg r = c1.nreg r) ∧
      c2.nmem = c1.nmem ∧ c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
    simp
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have hH1 : HostAt c1.nmem hp (Host.whole P.n) :=
    hostAt_agree (A := TD) hH rfl (by omega) fun a ha => hm1 a (Or.inl ha)
  refine ⟨c2, k1 + k2 + 1, .ifLtN_true (by rwo [h07, h20]) (.seq e1 e2), by omega, hw2,
    by rw [fr2 _ (by rwd [hAl])]; exact h1A, by rw [o30, h160], by rwx [hm2],
    fun C hCP hCs hCm => by
      rw [hm2]; refine hdesc C hCP (by rw [hCs]; ufs gradeStart) ?_ hH1
      rw [hCm]; unfold gradeLen; sio only [pow_zero, Nat.mul_one],
    fun a ha => by rw [hm2, hm1 a ha], fun r h1 h2 h3 h4 h5 => by
      rw [fr2 r h2, fr1 r h1 h3 h4 h5],
    fun r h1 h2 h3 => by rw [hrr2, frr1 r h1 h2 h3], by rw [hrm2, hrm1], by rw [ho2, ho1]⟩

/-- **The descriptor of a chain of grade `g ≥ 1`** from its children. -/
theorem descU_execG (hG : GoodEnv P) (hWn : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {TD hp g i R cnt : ℕ} (h07 : c.nreg 170007 = g) (hg : 1 ≤ g) (h20 : c.nreg 170020 = 1)
    (hA : c.nreg ALLOC = TD) (h14 : c.nreg 170014 = R) (h35 : c.nreg 170035 = 6 * i)
    (h36 : c.nreg 170036 = 2 * i + 1) (h12 : c.nreg 170012 = cnt) (h22 : c.nreg 170022 = 3)
    (h23 : c.nreg 170023 = 5) (hcnt : cnt = gradeCount P.n (g - 1))
    (hi : i < gradeCount P.n g) (hn : 2 ≤ P.n)
    (hL : ∀ C : Chain, C.P = Qof P → C.s = gradeStart (g - 1) (2 * i) →
      C.m = gradeLen P.n (g - 1) (2 * i) →
      ChainDescAt c.nmem (c.nmem (R + 6 * i)) (Qof P) (Host.whole P.n) C)
    (hLh : c.nmem (c.nmem (R + 6 * i)) = hp) (hL5 : c.nmem (R + 6 * i) + 5 ≤ TD)
    (hR : 2 * i + 1 < cnt → ∀ C : Chain, C.P = Qof P → C.s = gradeStart (g - 1) (2 * i + 1) →
      C.m = gradeLen P.n (g - 1) (2 * i + 1) →
      ChainDescAt c.nmem (c.nmem (R + 6 * i + 3)) (Qof P) (Host.whole P.n) C)
    (hRh : 2 * i + 1 < cnt → c.nmem (c.nmem (R + 6 * i + 3)) = hp)
    (hR5 : 2 * i + 1 < cnt → c.nmem (R + 6 * i + 3) + 5 ≤ TD)
    (hhp : hp + 7 ≤ TD) (hW : TD + 5 ≤ W) (hWR : R + 6 * i + 3 ≤ W) :
    ∃ c' k, Exec P W descU c c' k ∧ k ≤ 320 ∧ WordsBounded W c' ∧
      TD ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ TD + 5 ∧ c'.nreg 170030 + 5 ≤ c'.nreg ALLOC ∧
      c'.nmem (c'.nreg 170030) = hp ∧
      (∀ C : Chain, C.P = Qof P → C.s = gradeStart g i → C.m = gradeLen P.n g i →
        ChainDescAt c'.nmem (c'.nreg 170030) (Qof P) (Host.whole P.n) C) ∧
      (∀ a, a < TD → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ DescRG r → Bk r = false → r ≠ 160035 → r ≠ 160036 → r ≠ 160037 → r ≠ 160024 →
        r ≠ 170030 → r ≠ 170034 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ r, Bk r = false → r ≠ 160049 → c'.rreg r = c.rreg r) ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  have hgg : g - 1 + 1 = g := by omega
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hnot : ¬ c.nreg 170007 < c.nreg 170020 := by rwo [h07, h20]
  -- the left child
  obtain ⟨c1, k1, e1, hk1, hw1, l34, l35, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      (block [.addN 170034 170014 170035, .loadN 160035 170034]) c c1 k1 ∧ k1 = 2 ∧
      WordsBounded W c1 ∧ c1.nreg 170034 = R + 6 * i ∧ c1.nreg 160035 = c.nmem (R + 6 * i) ∧
      (∀ r, r ≠ 170034 → r ≠ 160035 → c1.nreg r = c.nreg r) ∧ c1.nmem = c.nmem ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try (config_simp; (try simp [h14, h35]); omega)
    refine ⟨rfl, ‹_›, by config_simp; simp [h14, h35], by config_simp; simp [h14, h35],
      fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
    simp
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have g1 : ∀ r, r ≠ 170034 → r ≠ 160035 → c1.nreg r = c.nreg r := fr1
  set BL := c.nmem (R + 6 * i) with hBL
  have hs0 : gradeStart g i = gradeStart (g - 1) (2 * i) := by
    rw [← gradeStart_succ, hgg]
  by_cases hr : 2 * i + 1 < cnt
  · -- two children
    have htest : c1.nreg 170036 < c1.nreg 170012 := by
      rwx [g1 _ (by decide) (by decide), g1 _ (by decide) (by decide), h36, h12]
    obtain ⟨c2, k2, e2, hk2, hw2, l34', l36, fr2, hm2, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
        (block [.addN 170034 170034 170022, .loadN 160036 170034]) c1 c2 k2 ∧ k2 = 2 ∧
        WordsBounded W c2 ∧ c2.nreg 170034 = R + 6 * i + 3 ∧
        c2.nreg 160036 = c.nmem (R + 6 * i + 3) ∧
        (∀ r, r ≠ 170034 → r ≠ 160036 → c2.nreg r = c1.nreg r) ∧ c2.nmem = c1.nmem ∧
        c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
      have c22 : c1.nreg 170022 = 3 := by rwx [g1 _ (by decide) (by decide)]
      exec_block
      all_goals try (config_simp; (try simp [l34, c22]); omega)
      refine ⟨rfl, ‹_›, by config_simp; simp [l34, c22],
        by config_simp; simp [l34, c22, hm1], fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
      simp
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
    set BR := c.nmem (R + 6 * i + 3) with hBR
    obtain ⟨hl2, hsum, hsR⟩ := gradeLen_succ_two (n := P.n) (g := g - 1) (i := i) hn
      (by rwx [← hcnt])
    rw [hgg] at hsum
    obtain ⟨CL, hCLP, hCLs, hCLm⟩ : ∃ C : Chain, C.P = Qof P ∧
        C.s = gradeStart (g - 1) (2 * i) ∧ C.m = gradeLen P.n (g - 1) (2 * i) := by
      have hfit := gradeLen_fit (n := P.n) (g := g - 1) (i := 2 * i) hn (by omega)
      exact ⟨⟨Qof P, _, _, gradeLen_pos hn (by omega), by rwo [hQn]⟩, rfl, rfl, rfl⟩
    obtain ⟨CR, hCRP, hCRs, hCRm⟩ : ∃ C : Chain, C.P = Qof P ∧
        C.s = gradeStart (g - 1) (2 * i + 1) ∧ C.m = gradeLen P.n (g - 1) (2 * i + 1) := by
      have hfit := gradeLen_fit (n := P.n) (g := g - 1) (i := 2 * i + 1) hn (by omega)
      exact ⟨⟨Qof P, _, _, gradeLen_pos hn (by omega), by rwo [hQn]⟩, rfl, rfl, rfl⟩
    have hfitR := gradeLen_fit (n := P.n) (g := g - 1) (i := 2 * i + 1) hn (by omega)
    have g2 : ∀ r, r ≠ 170034 → r ≠ 160035 → r ≠ 160036 → c2.nreg r = c.nreg r :=
      fun r a1 a2 a3 => by rw [fr2 r a1 a3, g1 r a1 a2]
    obtain ⟨c3, k3, e3, hk3, hw3, u3A, u37, u3h, udesc, hm3, fr3, frr3, hrm3, ho3⟩ :=
      unionS_exec (P := P) hG hWn hw2 (pl := BL) (pr := BR) (TD := TD) (hp := hp)
        (C₁ := CL) (C₂ := CR)
        (by rw [g2 _ (by rwd [hAl]) (by rwd [hAl]) (by rwd [hAl])]; exact hA)
        (by rwx [fr2 _ (by decide) (by decide)]) l36
        (by rwx [g2 _ (by decide) (by decide) (by decide)])
        (by rw [hm2, hm1]; exact hL CL hCLP hCLs hCLm)
        (by rw [hm2, hm1]; exact hR hr CR hCRP hCRs hCRm)
        (by rwx [hm2, hm1]) (by rw [hm2, hm1]; exact hRh hr) hhp hCLP hCRP
        (by rw [hCRs, hCLs, hCLm, hsR]) (by rwo [hCLs, hCLm, hCRm, ← hsR]) hL5 (hR5 hr) hW
    obtain ⟨c4, k4, e4, hk4, hw4, o30, fr4, hm4, hrr4, hrm4, ho4⟩ : ∃ c4 k4, Exec P W
        (block [.copyN 170030 160037]) c3 c4 k4 ∧ k4 = 1 ∧ WordsBounded W c4 ∧
        c4.nreg 170030 = c3.nreg 160037 ∧ (∀ r, r ≠ 170030 → c4.nreg r = c3.nreg r) ∧
        c4.nmem = c3.nmem ∧ c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧ c4.output = c3.output := by
      exec_block
      refine ⟨rfl, ‹_›, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
      simp
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
    have hA4 : c4.nreg ALLOC = TD + 5 := by rw [fr4 _ (by rwd [hAl])]; exact u3A
    refine ⟨c4, k1 + (k2 + (k3 + k4) + 1) + 2,
      .ifLtN_false hnot (.seq e1 (.ifLtN_true htest (.seq e2 (.seq e3 e4)))), by omega, hw4,
      by omega, by omega, by rw [o30, u37, hA4], by rw [o30, u37, hm4]; exact u3h,
      fun C hCP hCs hCm => by
        rw [o30, u37, hm4]
        exact udesc C hCP (by rw [hCs, hs0, hCLs]) (by rw [hCm, hsum, hCLm, hCRm]),
      fun a ha => by rw [hm4, hm3 a (Or.inl ha), hm2, hm1],
      fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
        rw [fr4 r h7, fr3 r h1 h2 h5 h6 h9]; exact g2 r h8 h3 h4,
      fun r h1 h2 => by rw [hrr4, frr3 r h1 h2, hrr2, hrr1], by rw [hrm4, hrm3, hrm2, hrm1],
      by rw [ho4, ho3, ho2, ho1]⟩
  · -- one child
    have htest : ¬ c1.nreg 170036 < c1.nreg 170012 := by
      rwx [g1 _ (by decide) (by decide), g1 _ (by decide) (by decide), h36, h12]
    obtain ⟨c2, k2, e2, hk2, hw2, o30, fr2, hm2, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
        (block [.copyN 170030 160035]) c1 c2 k2 ∧ k2 = 1 ∧ WordsBounded W c2 ∧
        c2.nreg 170030 = c1.nreg 160035 ∧ (∀ r, r ≠ 170030 → c2.nreg r = c1.nreg r) ∧
        c2.nmem = c1.nmem ∧ c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
      exec_block
      refine ⟨rfl, ‹_›, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
      simp
      repeat (rw [Machine.upd_other _ _ _ (by omega)])
    have hlen1 := gradeLen_succ_one (n := P.n) (g := g - 1) (i := i) hn (by rwx [hgg])
      (by rwo [← hcnt])
    rw [hgg] at hlen1
    have hA2 : c2.nreg ALLOC = TD := by
      rw [fr2 _ (by rwd [hAl]), g1 _ (by rwd [hAl]) (by rwd [hAl])]
      exact hA
    refine ⟨c2, k1 + (k2 + 2) + 2, .ifLtN_false hnot (.seq e1 (.ifLtN_false htest e2)),
      by omega, hw2, by omega, by omega, by rwx [o30, l35, hA2],
      by rwx [o30, l35, hm2, hm1],
      fun C hCP hCs hCm => by
        rw [o30, l35, hm2, hm1]
        exact hL C hCP (by rw [hCs, hs0]) (by rw [hCm, hlen1]),
      fun a ha => by rw [hm2, hm1], fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
        rw [fr2 r h7]; exact g1 r h8 h3,
      fun r h1 h2 => by rw [hrr2, hrr1], by rw [hrm2, hrm1], by rw [ho2, ho1]⟩

end proofs

end

end Chazelle.Core.Up
