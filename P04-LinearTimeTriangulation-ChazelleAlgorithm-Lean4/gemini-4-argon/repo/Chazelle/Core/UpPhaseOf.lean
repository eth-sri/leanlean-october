module

public import Chazelle.Core.UpPhase21
public import Chazelle.Core.UpPhaseCost2
public import Chazelle.Core.Granularize
public import Chazelle.Core.Lemma41Of

/-!
# WP-J: the up phase meets `UpPhaseSpec`

`upS = initA; halfS; initH; initR; gradesL; outS` and **`upPhase_of`**: with a valid oracle
interface `O`, `Lemma41Spec O` and `BruteSpec` (and the proved `GranularizeSpec`), the up phase
meets `UpPhaseSpec (gradeCtx O)`.  `upPhase_of'` takes `MergeSpec` and `ShootCutSpec O` instead
of `Lemma41Spec O` (`lemma41_of`).
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41

@[expose] public section

/-- The outputs: `coreReg 1 := h`, `coreReg 2 :=` the normal form of the top chain. -/
def outS : Stmt := block [.copyN 230001 170005, .addN 170053 170014 170020, .loadN 230002 170053]

/-- **The up phase.** -/
def upS (sB sL sG sP : Stmt) : Stmt :=
  .seq initA (.seq halfS (.seq initH (.seq initR (.seq (gradesL sB sL sG sP) outS))))

section proofs

variable {O : OracleIface}

theorem gradeGran_zero : gradeGran 0 = 1 := by
  unfold gradeGran Cost.ceilBeta; simp

set_option maxHeartbeats 16000000 in
theorem outS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {h R : ℕ}
    (h05 : c.nreg 170005 = h) (h14 : c.nreg 170014 = R) (h20 : c.nreg 170020 = 1)
    (hWR : R + 1 ≤ W) :
    ∃ c' k, Exec P W outS c c' k ∧ k = 3 ∧ WordsBounded W c' ∧
      c'.nreg 230001 = h ∧ c'.nreg 230002 = c.nmem (R + 1) ∧
      (∀ r, r ≠ 230001 → r ≠ 230002 → r ≠ 170053 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold outS
  exec_block
  all_goals try (config_simp; (try simp only [h05, h14, h20]); omega)
  refine ⟨rfl, ‹_›, by config_simp; exact h05, by config_simp; simp only [h14, h20],
    fun r a1 a2 a3 => ?_, rfl, rfl, rfl, rfl⟩
  simp only
  repeat (rw [Machine.upd_other _ _ _ (by omega)])

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 8192 in
/-- **WP-J: the up phase meets its contract.** -/
theorem upPhase_of (hV : O.Valid) (hL41 : Lemma41Spec O) (hBr : BruteSpec) :
    UpPhaseSpec (gradeCtx O) := by
  obtain ⟨sL, κL, hL⟩ := hL41
  obtain ⟨sB, κB, hB⟩ := hBr
  obtain ⟨sG, κG, hGr⟩ := granularize
  obtain ⟨K, hK⟩ := upT_le κB κL κG O.κ
  have hB' : BruteM sB κB := by unfold BruteM; exact hB
  have hL' : L41M O sL κL := by unfold L41M; exact hL
  have hGr' : GranM sG κG := by unfold GranM; exact hGr
  clear hB hL hGr
  refine ⟨upS sB sL sG O.prep, K + 300, fun P W c hw ⟨hG, hWn3, hSet⟩ hbud => ?_⟩
  have hAl : ALLOC = 9999 := rfl
  have hn3 : 3 ≤ P.n := hG.1.1
  have hn : 2 ≤ P.n := by omega
  obtain ⟨A0, hA0⟩ : ∃ A0, c.nreg ALLOC = A0 := ⟨_, rfl⟩
  obtain ⟨S, hS0⟩ : ∃ S, c.nreg (coreReg 0) = S := ⟨_, rfl⟩
  rw [hA0, hS0] at hSet
  have hbud' : A0 + (K * P.n + K + 300 * P.n + 300) ≤ W := by
    have hKn : (K + 300) * (P.n + 1) = K * P.n + K + 300 * P.n + 300 := by ring
    have := hbud; beta_reduce at this; rwa [hA0, hKn] at this
  have hWh : hostWords P.n ≤ W := by unfold hostWords; omega
  obtain ⟨sS0, sS1, sST, sSA⟩ := hSet.holds
  have h230 : c.nreg 230000 = S := hS0
  -- initA
  obtain ⟨c1, k1, e1, hk1, hw1, i20, i21, i22, i23, i25, i26, i29, i37, i00, i01, i02, i06, i28,
      fr1, hm1, hrr1, hrm1, ho1⟩ :=
    initA_exec (P := P) hw h230 sS1 (by omega) (by omega) (by omega) (by omega)
  have hA1 : c1.nreg ALLOC = A0 := by
    rw [fr1 _ (by rw [hAl]; unfold bandOf bUp; omega)]; exact hA0
  -- halfS
  obtain ⟨c2, k2, e2, hk2, hw2, j03, a21, a22, a23, hHalf, hm2, fr2, hrr2, hrm2, ho2⟩ :=
    halfS_exec (P := P) hw1 hA1 i01 i20 i21 (by omega)
  obtain ⟨A2, hA2⟩ : ∃ A2, c2.nreg ALLOC = A2 := ⟨_, rfl⟩
  rw [hA2] at a21 a22 a23
  -- initH
  obtain ⟨c3, k3, e3, hk3, hw3, A3e, j04, hH3, hm3, fr3, hrr3, hrm3, ho3⟩ :=
    initH_exec (P := P) hw2 hA2 (by omega) (by omega) (by omega) (by omega)
  have u3 : ∀ r, 170000 ≤ r → r < 170080 → ¬ HalfRG r → r ≠ 170004 →
      c3.nreg r = c1.nreg r := fun r a b h1 h2 => by
    rw [fr3 r (by unfold bandOf bL41; omega) h2 (by rw [hAl]; omega),
      fr2 r h1 (by rw [hAl]; omega)]
  -- initR
  obtain ⟨c4, k4, e4, hk4, hw4, r05, A4e, w0, w1, w2, w3, r07, r08, r09, r10, r11, r12, r14, r19,
      r15, r16, r35, r36, mw4, fr4, hrr4, hrm4, ho4⟩ :=
    initR_exec (P := P) (S := S) (D := A0) (n1 := P.n - 1) hw3 A3e
      (by rwa [u3 _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega)])
      (by rw [fr3 _ (by unfold bandOf bL41; omega) (by omega) (by rw [hAl]; omega)]; exact j03)
      (by rwa [u3 _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega)])
      (by rwa [u3 _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega)])
      (by rwa [u3 _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega)])
      (by rwa [u3 _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega)])
      (by rwa [u3 _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega)])
      (by rwa [u3 _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega)])
      (by omega) (by omega)
  have u4 : ∀ r, 170000 ≤ r → r < 170080 → ¬ HalfRG r → r ≠ 170004 → ¬ InitRRG r →
      c4.nreg r = c1.nreg r := fun r a b h1 h2 h3 => by
    rw [fr4 r h3 (by rw [hAl]; omega), u3 r a b h1 h2]
  have U : ∀ r, 170000 ≤ r → r < 170080 → ¬ HalfRG r → r ≠ 170004 → ¬ InitRRG r →
      ∀ v, c1.nreg r = v → c4.nreg r = v := fun r a b h1 h2 h3 v hv => (u4 r a b h1 h2 h3).trans hv
  -- the grade invariant at grade `0`
  have hI4 : GradeInv O P c4 0 (A2 + 7) A2 0 S A0 := by
    refine ⟨⟨U _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega)
        (by unfold InitRRG; omega) _ i01,
      by rw [fr4 _ (by unfold InitRRG; omega) (by rw [hAl]; omega)]; exact j04, r05, r07,
      by rw [r08]; unfold gradeCount; simp; omega, by rw [r10, pow_zero],
      by rw [r11, gradeGran_zero], by rw [r12]; unfold gradeCount; simp; omega, r14,
      by rw [r19]; simp,
      U _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega) (by unfold InitRRG; omega) _ i20,
      U _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega) (by unfold InitRRG; omega) _ i21,
      U _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega) (by unfold InitRRG; omega) _ i22,
      U _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega) (by unfold InitRRG; omega) _ i23,
      U _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega) (by unfold InitRRG; omega) _ i25,
      U _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega) (by unfold InitRRG; omega) _ i26,
      U _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega) (by unfold InitRRG; omega) _ i28,
      U _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega) (by unfold InitRRG; omega) _ i29,
      U _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega) (by unfold InitRRG; omega) _ i37⟩,
      U _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega) (by unfold InitRRG; omega) _ i00,
      U _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega) (by unfold InitRRG; omega) _ i02,
      by rw [fr4 _ (by unfold InitRRG; omega) (by rw [hAl]; omega),
        fr3 _ (by unfold bandOf bL41; omega) (by omega) (by rw [hAl]; omega)]; exact j03,
      U _ (by omega) (by omega) (by unfold HalfRG; omega) (by omega) (by unfold InitRRG; omega) _ i06,
      by rw [r09]; simp; omega, r15, r16, r35, r36, ?_⟩
    rw [A4e]
    intro m hm
    have m4 : ∀ a, a < A2 + 7 → m a = c3.nmem a := fun a ha =>
      (hm a (by omega)).trans (mw4 a (Or.inl ha))
    have m3 : ∀ a, a < A2 → m a = c2.nmem a := fun a ha =>
      (m4 a (by omega)).trans (hm3 a (Or.inl ha))
    have m0 : ∀ a, a < A0 → m a = c.nmem a := fun a ha => by
      rw [m3 a (by omega), hm2 a ha, hm1]
    have e0 : m (A2 + 7) = 0 := (hm _ (by omega)).trans w0
    have e1 : m (A2 + 7 + 1) = S := (hm _ (by omega)).trans w1
    have e2 : m (A2 + 7 + 2) = A2 + 7 + 4 := (hm _ (by omega)).trans w2
    have e3 : m (A2 + 7 + 3) = A0 := (hm _ (by omega)).trans w3
    obtain ⟨t0, t1, t2, t3⟩ := hSet m (fun a ha => m0 a ha)
    refine ⟨⟨by rw [e0]; omega, by rw [e1]; exact ⟨t0, t1, t2, le_refl _⟩,
      fun x hx => by rw [e3, m3 _ (by omega)]; exact hHalf x hx,
      L41.hostAt_agree hH3 rfl (by omega) m4, by omega,
      ⟨by omega, by rw [e1]; omega, by rw [e3]; omega⟩, by rw [e2, e0]; try omega,
      fun g hg => by rw [e0] at hg; exact absurd hg (Nat.not_lt_zero g),
      fun g i hg _ => by rw [e0] at hg; exact absurd hg (Nat.not_lt_zero g)⟩,
      e0, fun h => by omega, e1, e3⟩
  -- all grades
  have hup := hK P.n hn
  obtain ⟨c5, k5, h', R', e5, hk5, hw5, a51, a52, hI5, m5, rm5, o5, f5, ff5⟩ :=
    gradesL_exec (O := O) hB' hL' hGr' hV hG hWh hn hw4 hI4 (by rw [A4e]; omega)
  obtain ⟨hu5, x00, x02, x03, x06, x09, x15, x16, x35, x36, hM5⟩ := hI5
  obtain ⟨hT5, hmh5, hR5, -, -⟩ := hM5.holds
  have hR5' := hR5 (by omega)
  rw [show topGrade P.n + 1 - 1 = topGrade P.n by omega] at hR5'
  have hc1 : 0 < gradeCount P.n (topGrade P.n) := by rw [gradeCount_top hn]; omega
  have hrow := hT5.2.2.2.2.2.2.2.1 (topGrade P.n) (by omega)
  rw [hR5'] at hrow
  -- the outputs
  obtain ⟨c6, k6, e6, hk6, hw6, o1, o2, fr6, hm6, hrr6, hrm6, ho6⟩ :=
    outS_exec (P := P) hw5 hu5.r05 hu5.r14 hu5.r20 (by omega)
  have hA6 : c6.nreg ALLOC = c5.nreg ALLOC := fr6 _ (by rw [hAl]; omega) (by rw [hAl]; omega)
    (by rw [hAl]; omega)
  -- the frame of the phase
  have hout : ∀ r, bandOf r ∉ phaseBands → r ≠ ALLOC → c6.nreg r = c.nreg r := by
    intro r h1 h2
    have hb : OutB (bandOf r) := by
      unfold phaseBands at h1; simp only [Finset.mem_Icc, not_and_or, not_le] at h1
      unfold OutB; omega
    have hr : r < 10000 ∨ 250000 ≤ r := by unfold OutB bandOf at hb; omega
    rw [fr6 r (by omega) (by omega) (by omega), f5 r (Or.inl ⟨Or.inl hb, h2⟩),
      fr4 r (by unfold InitRRG; omega) h2, fr3 r (by unfold bandOf bL41; omega) (by omega) h2,
      fr2 r (by unfold HalfRG; omega) h2, fr1 r (by unfold bandOf bUp; omega)]
  have hkeep : c6.nreg (coreReg 0) = c.nreg (coreReg 0) := by
    show c6.nreg 230000 = c.nreg 230000
    rw [fr6 _ (by omega) (by omega) (by omega),
      f5 _ (Or.inl ⟨Or.inr rfl, by rw [hAl]; omega⟩),
      fr4 _ (by unfold InitRRG; omega) (by rw [hAl]; omega),
      fr3 _ (by unfold bandOf bL41; omega) (by omega) (by rw [hAl]; omega),
      fr2 _ (by unfold HalfRG; omega) (by rw [hAl]; omega), fr1 _ (by unfold bandOf bUp; omega)]
  have mem5 : ∀ a, a < A0 → c5.nmem a = c.nmem a := fun a ha => by
    rw [m5 a (by rw [A4e]; omega), mw4 a (Or.inl (by omega)), hm3 a (Or.inl (by omega)),
      hm2 a ha, hm1]
  refine ⟨c6, k1 + (k2 + (k3 + (k4 + (k5 + k6)))),
    .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 e6)))), ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have hKn : (K + 300) * (P.n + 1) = K * P.n + K + 300 * P.n + 300 := by ring
    show _ ≤ (K + 300) * (P.n + 1)
    rw [hKn]; omega
  · intro i hi
    simp only [Finset.mem_singleton] at hi
    subst hi
    exact hkeep
  · show (gradeCtx O).holds P c6.nmem (c6.nreg 230001) (c6.nreg ALLOC)
    rw [hm6, o1, hA6]
    exact holds_of_upTab hn (robust_of hM5 le_rfl fun m h => h.1)
  · show P.n - 1 ≤ 2 ^ (c6.nmem (c6.nreg 230001) - 1)
    rw [hm6, o1, hmh5, show topGrade P.n + 1 - 1 = topGrade P.n by omega]
    exact Nat.le_pow_clog (by norm_num) _
  · obtain ⟨hN, -⟩ := hT5.2.2.2.2.2.2.2.2 (topGrade P.n) 0 (by omega) hc1
    simp only [rowE, hR5', Nat.mul_zero, Nat.add_zero] at hN
    let C0 := gChain P (topGrade P.n) 0 hn hc1
    obtain ⟨-, -, -, -, -, -, N, hNW, hc⟩ := hN C0 rfl rfl rfl
    refine ⟨C0, N, ⟨rfl, by show gradeStart (topGrade P.n) 0 = 0; unfold gradeStart; simp,
      by show gradeLen P.n (topGrade P.n) 0 + 1 = P.n; rw [gradeLen_top hn]; omega⟩, ?_, hc⟩
    show Robust (c6.nreg ALLOC) c6.nmem fun m => NFAt m (c6.nreg 230002) N
    rwa [hm6, o2, hA6]
  · refine ⟨hout, fun r h1 => ?_, fun a ha => by rw [hm6, mem5 a (by omega)],
      fun a ha => ?_, by rw [ho6, o5, ho4, ho3, ho2, ho1], by omega, by omega⟩
    · have hb : OutB (bandOf r) := by
        unfold phaseBands at h1; simp only [Finset.mem_Icc, not_and_or, not_le] at h1
        unfold OutB; omega
      rw [hrr6, ff5 r hb, hrr4, hrr3, hrr2, hrr1]
    · rw [hrm6, rm5 a (by rw [A4e]; omega), hrm4, hrm3, hrm2, hrm1]

/-- **WP-J** with Lemma 4.1 from `MergeSpec` and `ShootCutSpec O`. -/
theorem upPhase_of' (hM : MergeSpec) (hV : O.Valid) (hSC : ShootCutSpec O) (hBr : BruteSpec) :
    UpPhaseSpec (gradeCtx O) :=
  upPhase_of hV (lemma41_of O hM hSC) hBr

end proofs

end

end Chazelle.Core.Up
