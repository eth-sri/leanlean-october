module

meta import Chazelle.Programs.RegisterGuard

public import Chazelle.Core.UpPhase18

/-!
# WP-J up phase, part 19: the execution of one grade

`gradeB_exec`: from `GradeInv` at grade `g ≤ p` to `GradeInv` at grade `g + 1` (the new grade
record `h'` with the row `R'` of grade `g`).  The package contracts are bundled as `BruteM`,
`L41M`, `GranM`.
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41

@[expose] public section

section proofs

variable {O : OracleIface} {P : Polygon} {W : ℕ}

set_option maxHeartbeats 64000000 in
/-- **One grade.** -/
theorem gradeB_exec {sB sL sG : Stmt} {κB κL : ℕ} {κG : ℕ → ℕ} (hB : BruteM sB κB)
    (hL : L41M O sL κL) (hGr : GranM sG κG) (hV : O.Valid) (hG : GoodEnv P)
    (hWh : hostWords P.n ≤ W) (hn : 2 ≤ P.n) {c : Config} (hw : WordsBounded W c)
    {g h hp R S D : ℕ} (hI : GradeInv O P c g h hp R S D) (hg : g ≤ topGrade P.n)
    (hW : c.nreg ALLOC + gradeC κB κL κG O.κ P.n g + stepB κB κL κG O.κ g + 8 ≤ W)
    (hWγ : gradeGran (g + 1) + g + 3 ≤ W) :
    ∃ c' k h' R', Exec P W (gradeB sB sL sG O.prep) c c' k ∧
      k ≤ gradeC κB κL κG O.κ P.n g ∧ WordsBounded W c' ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      GradeInv O P c' (g + 1) h' hp R' S D ∧
      (MemEqBelow (c.nreg ALLOC) c'.nmem c.nmem) ∧
      (MemEqBelow (c.nreg ALLOC) c'.rmem c.rmem) ∧ c'.output = c.output ∧
      (∀ r, GK r → c'.nreg r = c.nreg r) ∧
      (∀ r, OutB (bandOf r) → c'.rreg r = c.rreg r) := by
  have hAl : ALLOC = 9999 := rfl
  
  have hW128 : 128 * P.n + 8 ≤ W := by register_guard
  obtain ⟨hu, i00, i02, i03, i06, i09, i15, i16, i35, i36, hM⟩ := hI
  obtain ⟨A, hA⟩ := exists_eq' (a' := c.nreg ALLOC)
  rw [hA] at hM hW
  obtain ⟨hT0, hmh0, hR0, hS0, hD0⟩ := hM.holds
  obtain ⟨-, hSet, hHalf, -, -, ⟨hh4, hSA, hDA⟩, hTA, -, -⟩ := hT0
  rw [hS0] at hSet hSA
  rw [hD0] at hHalf hDA
  rw [hmh0] at hTA
  have h2g := two_pow_le_of_le_top hn hg
  set cnt := gradeCount P.n g with hcnt
  set K := stepB κB κL κG O.κ g with hK
  
  unfold gradeC at hW
  rw [← hcnt, ← hK] at hW
  clear_value K
  -- the chains
  have hMc : Robust A c.nmem fun m => ChainMem O P m h hp g R (c.nreg 170018) 0 A :=
    robust_of hM le_rfl fun m h' => ⟨h'.1, h'.2.1, h'.2.2.1, trivial⟩
  have hb1 : A + (cnt + 1) * (K + 8) ≤ W := by
    have e : (cnt + 1) * (K + 8) = cnt * (K + 8) + (K + 8) := by ring
    have := Nat.mul_le_mul_left cnt (show K + 8 ≤ K + 19 by omega)
    omega
  obtain ⟨c1, k1, e1, hk1, hw1, a11, a12, hu1, hM1, m1, r1, o1, f1, ff1⟩ :=
    chainsL_exec (O := O) hB hL hGr hV hG hWh hn hw hu hA i15 i16 rfl i35 i36 h2g hMc (by rwa [← hK])
  have g1 : ∀ r, GK r → c1.nreg r = c.nreg r := fun r hr => by
    obtain ⟨k, a, b, c', d, e, f⟩ := hr.kept; exact f1 r k a b c' d e f
  have u1 : ∀ r, URegR r → c1.nreg r = c.nreg r := fun r hr =>
    f1 r hr.kept (by register_guard) (by register_guard)
      (by register_guard) (by register_guard)
      (by register_guard) (by register_guard)
  obtain ⟨A1, hA1⟩ := exists_eq' (a' := c1.nreg ALLOC)
  rw [hA1] at a11 a12 hM1
  have hk1' : k1 ≤ cnt * (K + 2) + 2 := by rwa [hK]
  have hKc := Nat.mul_le_mul_left cnt (show K + 2 ≤ K + 19 by omega)
  have hc19 : cnt * (K + 19) = cnt * (K + 2) + 17 * cnt := by ring
  -- the row
  obtain ⟨c2, k2, e2, hk2, hw2, A2e, a22, j44, hE2, m2, fr2, hrr2, hrm2, ho2⟩ :=
    rowS_exec (O := O) (P := P) (hp := hp) (g := g) hw1 hA1 hu1.r08 rfl hu1.r20 hu1.r21 hu1.r22
      hu1.r29 (robust_of hM1 le_rfl fun m h' => h'.2.2.2) (by omega)
  have g2 : ∀ r, GK r → c2.nreg r = c1.nreg r := fun r hr =>
    fr2 r (by have := hr.range; unfold RowRG; omega) hr.ne_alloc
  have u2 : ∀ r, URegR r → c2.nreg r = c1.nreg r := fun r hr =>
    fr2 r (by unfold URegR at hr; unfold RowRG; omega) (by unfold URegR at hr; rw [hAl]; omega)
  have hmc2 : MemEqBelow A c2.nmem c.nmem := fun a ha => by
    rw [m2 a ((by omega)), m1 a ha]
  have U2 := fun r hr => (u2 r hr).trans (u1 r hr)
  -- the header
  obtain ⟨c3, k3, e3, hk3, hw3, A3e, j51, j52, j56, j57, j50, w0, w1, w2, w3, m3, fr3, hrr3,
      hrm3, ho3⟩ :=
    recA_exec (P := P) (h := h) (g := g) hw2 A2e ((U2 170005 (by reg_omega)).trans hu.r05)
      ((U2 170007 (by reg_omega)).trans hu.r07)
      ((U2 170020 (by reg_omega)).trans hu.r20)
      ((U2 170021 (by reg_omega)).trans hu.r21)
      ((U2 170022 (by reg_omega)).trans hu.r22)
      ((U2 170025 (by reg_omega)).trans hu.r25)
      (by omega) (by omega) (by omega)
  have u3 : ∀ r, URegR r → c3.nreg r = c2.nreg r := fun r hr =>
    fr3 r (by unfold URegR at hr; unfold RecRG; omega) (by unfold URegR at hr; rw [hAl]; omega)
  have g3 : ∀ r, GK r → c3.nreg r = c2.nreg r := fun r hr =>
    fr3 r (by have := hr.range; unfold RecRG; omega) hr.ne_alloc
  -- the old rows
  have hT : c2.nmem (h + 2) + g ≤ A := by ram_rw [hmc2]; omega
  obtain ⟨c4, k4, e4, hk4, hw4, A4e, a42, hcp, m4, fr4, hrr4, hrm4, ho4⟩ :=
    copyL_exec (P := P) hw3 j50
      (((u3 170007 (by reg_omega)).trans (U2 170007 (by reg_omega))).trans hu.r07)
      j57 j56 A3e
      (((u3 170020 (by reg_omega)).trans (U2 170020 (by reg_omega))).trans hu.r20)
      (by omega) (by omega) (by omega) (by omega)
  have u4 : ∀ r, URegR r → c4.nreg r = c.nreg r := fun r hr => by
    rw [fr4 r (by unfold URegR at hr; unfold CopyRG; omega) (by unfold URegR at hr; rw [hAl]; omega),
      u3 r hr, u2 r hr, u1 r hr]
  have g4 : ∀ r, GK r → c4.nreg r = c.nreg r := fun r hr => by
    rw [fr4 r (by have := hr.range; unfold CopyRG; omega) hr.ne_alloc,
      g3 r hr, g2 r hr, g1 r hr]
  have hmc4 : MemEqBelow A c4.nmem c.nmem := fun a ha => by
    rw [m4 a ((by omega)), m3 a ((by omega)), hmc2 a ha]
  -- the new row, the registers of the next grade
  set Q := (P.n - 2) / 2 ^ g with hQ
  clear_value Q
  have hQn : Q ≤ P.n := by rw [hQ]; have := Nat.div_le_self (P.n - 2) (2 ^ g); omega
  have hQ2 : c4.nmem (D + Q) = Q / 2 := by ram_rw [hmc4]; exact hHalf Q hQn
  have hj44 : c4.nreg 170044 = A1 := by
    rw [fr4 _ (by register_guard) (by rw [hAl]; omega),
      fr3 _ (by register_guard) (by rw [hAl]; omega)]; exact j44
  have hTT : A + 1 ≤ A1 + 3 * cnt + 4 := by omega
  obtain ⟨c5, k5, e5, hk5, hw5, w5, A5e, j05, j12, j14, j19, j10, j09, j08, j07, j15, j16, j35,
      j36, m5, fr5, hrr5, hrm5, ho5⟩ :=
    recB_exec (P := P) (T' := A1 + 3 * cnt + 4) (g := g) (R' := A1) (h' := A1 + 3 * cnt)
      (cnt := cnt) (pg := 2 ^ g) (D := D) (Q := Q) (g1 := g + 1) hw4 A4e
      ((fr4 170056 (by register_guard) (by rw [hAl]; omega)).trans j56)
      ((u4 170007 (by reg_omega)).trans hu.r07) hj44
      ((fr4 170051 (by register_guard) (by rw [hAl]; omega)).trans j51)
      ((u4 170008 (by reg_omega)).trans hu.r08)
      ((u4 170010 (by reg_omega)).trans hu.r10)
      ((u4 170003 (by reg_omega)).trans i03)
      ((u4 170009 (by reg_omega)).trans i09)
      ((fr4 170052 (by register_guard) (by rw [hAl]; omega)).trans j52)
      ((u4 170020 (by reg_omega)).trans hu.r20) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by rw [hQ2]; omega)
  have w5r : ∀ r, URegR r → ¬ RecBRG r → c5.nreg r = c.nreg r := fun r h1 h2 => by
    rw [fr5 r h2 (by unfold URegR at h1; rw [hAl]; omega), u4 r h1]
  have g5 : ∀ r, GK r → c5.nreg r = c.nreg r := fun r hr => by
    rw [fr5 r (by have := hr.range; unfold RecBRG; omega) hr.ne_alloc,
      g4 r hr]
  have hSc : ∀ i, i ≤ topGrade P.n + 1 → c5.nmem (S + 2 + i) = 2 ^ i ∧
      c5.nmem (S + topGrade P.n + 4 + i) = Cost.ceilBeta i := fun i hi => by
    ram_rw [m5, m5, hmc4, hmc4]
    exact hSet.2.2.1 i hi
  obtain ⟨c6, k6, e6, hk6, hw6, j11, fr6, hm6, hrr6, hrm6, ho6⟩ :=
    gamS_exec (P := P) (S := S) (p := topGrade P.n) (g1 := g + 1) hw5
      ((w5r 170000 (by reg_omega) (by reg_omega)).trans i00)
      ((w5r 170002 (by reg_omega) (by reg_omega)).trans i02) j07
      ((w5r 170021 (by reg_omega) (by reg_omega)).trans hu.r21)
      ((w5r 170025 (by reg_omega) (by reg_omega)).trans hu.r25)
      (by omega) (by omega) hSc (by omega) (by omega) (by omega)
  have v6 := fun r a b d e => fr6 r (Or.inr a) b d e
  have hA6 := (fr6 ALLOC ((by decide)) (by decide) (by decide) (by decide)).trans A5e
  -- memory
  have mc62 : MemEqBelow (A1 + 3 * cnt) c6.nmem c2.nmem := fun a ha => by
    rw [hm6, m5 a (by clear * - ha; omega), m4 a (Or.inl (by clear * - ha; omega)),
      m3 a (Or.inl ha)]
  have mc61 : MemEqBelow A1 c6.nmem c1.nmem := fun a ha => by
    rw [mc62 a (by clear * - ha; omega), m2 a (Or.inl ha)]
  have mc6 : MemEqBelow A c6.nmem c.nmem := fun a ha => by
    rw [mc61 a (by clear * - ha a11; omega), m1 a ha]
  have hQ' : Q / 2 = (P.n - 2) / 2 ^ (g + 1) := by
    rw [hQ, Nat.div_div_eq_div_mul, ← pow_succ]
  refine ⟨c6, k1 + (k2 + (k3 + (k4 + (k5 + k6)))), A1 + 3 * cnt, A1,
    .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 e6)))), ?_, hw6,
    by clear * - hA a11 hA6; omega,
    by clear * - hA a12 a22 A2e hk3 A3e A4e a42 hk5 hA6; omega,
    ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, j11, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun a ha => mc6 a (hA ▸ ha), fun a ha => by
      rw [hrm6, hrm5, hrm4, hrm3, hrm2, r1 a (hA ▸ ha)],
    by rw [ho6, ho5, ho4, ho3, ho2, o1], fun r hr => by
      have := hr.range
      rw [fr6 r (by clear * - this; omega) (by clear * - this; omega)
        (by clear * - this; omega) (by clear * - this; omega), g5 r hr],
    fun r hr => by
      rw [hrr6, hrr5, hrr4, hrr3, hrr2, ff1 r hr]⟩
  · unfold gradeC; rw [← hcnt, ← hK]
    clear * - hk1' hk2 hk3 hk4 hk5 hk6 hc19; omega
  · ram_rw [v6, w5r]; exact hu.r01
  · ram_rw [v6, w5r]; exact hu.r04
  · ram_rw [v6, j05]
  · ram_rw [v6, j07]
  · ram_rw [v6, j08, hQ2, gradeCount_succ, ← hQ]
  · ram_rw [v6, j10, pow_succ]; ring
  · ram_rw [v6, j12, Nat.add_sub_cancel]; try rfl
  · ram_rw [v6, j14]
  · ram_rw [v6, j19, Nat.add_sub_cancel]
  · ram_rw [v6, w5r]; exact hu.r20
  · ram_rw [v6, w5r]; exact hu.r21
  · ram_rw [v6, w5r]; exact hu.r22
  · ram_rw [v6, w5r]; exact hu.r23
  · ram_rw [v6, w5r]; exact hu.r25
  · ram_rw [v6, w5r]; exact hu.r26
  · ram_rw [v6, w5r]; exact hu.r28
  · ram_rw [v6, w5r]; exact hu.r29
  · ram_rw [v6, w5r _ (by register_guard) (by reg_omega)]; exact hu.r37
  · ram_rw assumption [v6, w5r]
  · ram_rw assumption [v6, w5r]
  · ram_rw assumption [v6, w5r]
  · ram_rw assumption [v6, w5r]
  · simp [v6, j09, hQ2, hQ']
  · simp [v6, j15]
  · simp [v6, j16]
  · simp [v6, j35]
  · simp [v6, j36]
  · rw [hA6]
    intro m hm
    clear * - hm hM mc6 hm6 m5 m4 m3 w0 w1 w2 w3 hmc2 hS0 hD0 hcp w5 hE2 mc61 mc62 hcnt a11 hh4
      hSA hDA hTA hg
    have hmc : MemEqBelow A m c.nmem := fun a ha => (hm a (by omega)).trans (mc6 a ha)
    obtain ⟨hTm, hmhm, -, hSm, hDm⟩ := hM m hmc
    obtain ⟨-, hSetm, hHalfm, hHm, hhpm, -, -, hrowm, hEm⟩ := hTm
    rw [hSm] at hSetm; rw [hDm] at hHalfm; rw [hmhm] at hrowm hEm
    have mc63 : MemEqBelow (A1 + 3 * cnt + 4) c6.nmem c3.nmem := fun a ha => by
      ram_rw [hm6, m5 a, m4 a (Or.inl ha)]
    have e0 : m (A1 + 3 * cnt) = g + 1 :=
      (hm _ (by omega)).trans ((mc63 _ (by omega)).trans w0)
    have e1 : m (A1 + 3 * cnt + 1) = S :=
      (hm _ (by omega)).trans ((mc63 _ (by omega)).trans (w1.trans ((hmc2 _ (by omega)).trans hS0)))
    have e2 : m (A1 + 3 * cnt + 2) = A1 + 3 * cnt + 4 :=
      (hm _ (by omega)).trans ((mc63 _ (by omega)).trans w2)
    have e3 : m (A1 + 3 * cnt + 3) = D :=
      (hm _ (by omega)).trans ((mc63 _ (by omega)).trans (w3.trans ((hmc2 _ (by omega)).trans hD0)))
    have hTc : c2.nmem (h + 2) = c.nmem (h + 2) := hmc2 _ (by omega)
    have et : ∀ j, j < g → m (A1 + 3 * cnt + 4 + j) = m (m (h + 2) + j) := fun j hj => by
      ram_rw [hmc (h + 2), hmc (c.nmem (h + 2) + j),
        hm (A1 + 3 * cnt + 4 + j), hm6, m5, hcp j hj,
        m3 _ (Or.inl (by omega)), hTc, hmc2]
    have eg : m (A1 + 3 * cnt + 4 + g) = A1 := (hm _ (by omega)).trans (by rwa [hm6])
    refine ⟨⟨by rw [e0]; omega, by rwa [e1], by rwa [e3], hHm,
      by omega, ⟨by omega, by rw [e1]; omega, by rw [e3]; omega⟩, by rw [e2, e0]; omega,
      fun g' hg' => ?_, fun g' i hg' hi => ?_⟩, e0, fun _ => by
        rw [e2, Nat.add_sub_cancel, eg], e1, e3⟩
    · rw [e0] at hg'
      rw [e2]
      rcases Nat.lt_or_ge g' g with h1 | h1
      · rw [et g' h1]; have := hrowm g' h1; clear * - this a11; omega
      · rw [show g' = g by clear * - hg' h1; omega, eg, ← hcnt]; clear * -; omega
    · rw [e0] at hg'
      simp only [rowE]
      rw [e2]
      rcases Nat.lt_or_ge g' g with h1 | h1
      · rw [et g' h1]; exact (hEm g' i h1 hi).mono (by clear * - a11; omega)
      · have hgg : g' = g := by clear * - hg' h1; omega
        rw [hgg] at hi ⊢
        have hi' : i < cnt := by rwa [hcnt]
        have b0 : A1 + 3 * i < A1 + 3 * cnt := by clear * - hi'; omega
        have b1 : A1 + 3 * i + 1 < A1 + 3 * cnt := by clear * - hi'; omega
        have b2 : A1 + 3 * i + 2 < A1 + 3 * cnt := by clear * - hi'; omega
        have hmm : MemEqBelow (A1 + 3 * cnt) m c2.nmem := fun a ha =>
          (hm a (by clear * - ha; omega)).trans (mc62 a ha)
        rw [eg, hmm _ b0, hmm _ b1, hmm _ b2]
        exact (hE2 i hi' m fun a ha => (hm a (by clear * - ha; omega)).trans (mc61 a ha)).mono
          (by clear * -; omega)

end proofs

end

end Chazelle.Core.Up
