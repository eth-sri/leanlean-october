module

public import Chazelle.Core.SweepEvLoopStartP
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
set_option maxHeartbeats 32000000
set_option maxRecDepth 20000

/-!
# The sweep (WP-D), stage 3: the start of the event loop (task L0, the run step)

`start_irs`: the run step of `start` with the raw post `SRaw`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

theorem stHead_val (m f : ℕ → ℕ) :
    regB m stHead f kE = f cGL ∧ regB m stHead f kH = 0 ∧ regB m stHead f kN = 0 ∧
      regB m stHead f sP = 0 ∧ regB m stHead f aF = 0 ∧ regB m stHead f dF = 0 := by
  simp only [stHead, regB, regI, upd, kE, kH, kN, sP, aF, dF, cGL, sw]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- The registers of the head. -/
def HdR (q : ℕ) : Prop := q = kE ∨ q = kH ∨ q = kN ∨ q = sP ∨ q = aF ∨ q = dF

theorem stHead_other (m f : ℕ → ℕ) {q : ℕ} (h : ¬ HdR q) : regB m stHead f q = f q :=
  regB_other m stHead f (fun i hi => by
    simp only [stHead, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] <;> intro he <;>
      subst he <;> exact h (by simp [HdR]))

theorem hdR_stR {q : ℕ} (h : HdR q) : StR q := by
  unfold HdR at h; unfold StR
  simp only [kE, kH, kN, kL, gN, gR, sP, dF, lC, aF, sw] at h ⊢
  omega

theorem zX_stR : StR zX := by unfold StR zX; simp [kE, kH, kN, kL, gN, gR, sP, dF, lC, sw]
theorem lC_stR : StR lC := by unfold StR; simp [kE, kH, kN, kL, gN, gR, sP, dF, lC, sw]

/-- A register outside all write sets of the start keeps its value along the parts. -/
def Untouched (q : ℕ) : Prop :=
  bandOf q ∉ oracleBands ∧ ¬ HdR q ∧ ¬ WS q ∧ ¬ FPR q ∧ ¬ LblR kN kL q ∧ ¬ GapR q ∧ q ≠ zX ∧
    q ≠ lC ∧ q ≠ ALLOC

theorem untouched_of {q : ℕ} (hq : bandOf q ∉ oracleBands) (h : ¬ StR q) (ha : q ≠ ALLOC) :
    Untouched q :=
  ⟨hq, fun h' => h (hdR_stR h'), fun h' => h (ws_stR h'), fun h' => h (fpr_stR h'),
    fun h' => h (lblR_stR h'), fun h' => h (gapR_stR h'), fun h' => h (h' ▸ zX_stR),
    fun h' => h (h' ▸ lC_stR), ha⟩

theorem untouched_sw {j : ℕ} (hj : j < 10000)
    (h : ¬ (2400 ≤ j ∧ j ≤ 2406) ∧ ¬ (2440 ≤ j ∧ j ≤ 2442) ∧ j ≠ 2450 ∧ j ≠ 2451 ∧ j ≠ 2431 ∧
      ¬ (2480 ≤ j ∧ j < 2500) ∧ ¬ (700 ≤ j ∧ j < 2200) ∧ ¬ (2610 ≤ j ∧ j ≤ 2612) ∧
      ¬ (3000 ≤ j ∧ j < 6000)) : Untouched (sw j) := by
  refine untouched_of (not_oracle_sw (by ufo sw) (by ufo sw)) ?_
    (by ufo ALLOC sw)
  unfold StR
  simp only [kE, kH, kN, kL, gN, gR, sP, dF, lC, sw]
  omega

/-- **The run step of the start.** -/
theorem start_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction}
    {N₁ N₂ : NF} (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    {rs ax : List (ℕ × ℕ × ℕ × ℕ × ℕ)} (hSD : StopData P J N₂ c rs ax)
    (hlay : c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC ∧ c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC)
    (hlB : c₀.nreg ALLOC ≤ c.nreg lB) (hlB7 : c.nreg lB + 7 ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + startK (c₀.nreg TLR) ≤ W) :
    IRS P W c₀ start c (startK (c₀.nreg TLR)) (SRaw P J N₂ rs ax c) := by
  have hK₀ := E.hK.fix hI
  have hP := E.hP
  have hNF := E.hNF₂
  have hst := hSD.2.2.2.2.1
  have hlen := hSD.1
  have hlax := hSD.2.1
  unfold start startK
  unfold startK at hroom
  -- 1. the head
  have hokH : okB W c.nmem stHead c.nreg := by
    simp only [stHead, okB, okI]
    exact ⟨iscr_sw (by simp [kE, sw]) (by simp [kE, sw]),
      ⟨iscr_sw (by simp [kH, sw]) (by simp [kH, sw]), Nat.zero_le _⟩,
      ⟨iscr_sw (by simp [kN, sw]) (by simp [kN, sw]), Nat.zero_le _⟩,
      ⟨iscr_sw (by simp [sP, sw]) (by simp [sP, sw]), Nat.zero_le _⟩,
      ⟨iscr_sw (by simp [aF, sw]) (by simp [aF, sw]), Nat.zero_le _⟩,
      ⟨iscr_sw (by simp [dF, sw]) (by simp [dF, sw]), Nat.zero_le _⟩, trivial⟩
  refine IRS.seq (K₁ := stHead.length) (K₂ := stStepK + (stStepK + ((fposK 3 (c₀.nreg TLR) + 4) +
    ((fposK 1 (c₀.nreg TLR) + fposK 2 (c₀.nreg TLR) + 5) + 16)))) (IRS.block stHead hI hokH) ?_ |>.mono
    (by simp [stHead]) (fun _ => id)
  rintro c₂ hI₂ - - hc₂
  obtain ⟨vE, vH, vN, vP, vA, vD⟩ := stHead_val c.nmem c.nreg
  have o2 : ∀ q, ¬ HdR q → c₂.nreg q = c.nreg q := fun q hq => by
    rw [hc₂]; exact stHead_other _ _ hq
  have m2 : c₂.nmem = c.nmem := by rw [hc₂]
  have e2E : c₂.nreg kE = pK0 J := by
    rw [hc₂]; show regB _ _ _ kE = _; rwr [vE, (E.hM.fix hI).gl]
  have e2H : c₂.nreg kH = 0 := by rw [hc₂]; exact vH
  have e2N : c₂.nreg kN = 0 := by rw [hc₂]; exact vN
  have e2P : c₂.nreg sP = 0 := by rw [hc₂]; exact vP
  have e2A : c₂.nreg aF = 0 := by rw [hc₂]; exact vA
  have e2D : c₂.nreg dF = 0 := by rw [hc₂]; exact vD
  have nh : ∀ j, j = 2600 ∨ j = 2601 ∨ j = 2602 ∨ j = 2430 → ¬ HdR (sw j) := by
    rintro j (rfl | rfl | rfl | rfl) <;> simp [HdR, kE, kH, kN, sP, aF, dF, sw]
  have hA2 : c₂.nreg ALLOC = c.nreg ALLOC := o2 _ (by simp [HdR, kE, kH, kN, sP, aF, dF, ALLOC, sw])
  have sC2 : c₂.nreg sC = c.nreg sC := o2 _ (nh 2601 (by norm_num))
  have sB2 : c₂.nreg sB = c.nreg sB := o2 _ (nh 2600 (by norm_num))
  have aB2 : c₂.nreg aB = c.nreg aB := o2 _ (nh 2602 (by norm_num))
  have hSD2  := stopData_transport hSD sC2 sB2 aB2 hlay
    (fun a _ => by rw [m2])
  have hlay2 : c₂.nreg sB + 5 * c₂.nreg sC ≤ c₂.nreg ALLOC ∧
      c₂.nreg aB + 5 * c₂.nreg sC ≤ c₂.nreg ALLOC := by rwx [sC2, sB2, aB2, hA2]
  have hS2 : StI P J N₂ rs ax c₂ := by
    have hl : lblOf c₂ kN kL = [] := by simp [lblOf, e2N]
    refine ⟨by omega, by omega, by omega, fun i hi h => by omega, by rws [hl],
      fun i h => by omega, fun v hv => by rw [hl] at hv; simp at hv, by omega, ?_⟩
    rw [e2A, e2P]
    simp
  -- 2. the first stop step
  refine IRS.seq (K₁ := stStepK) (stStep_irs E hI₂ hSD2 hlay2 hS2 e2E e2H (by rwo [hA2])) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨S3, a3, b3, fr3, A3, m3⟩
  have ws : ∀ j, j = 2600 ∨ j = 2601 ∨ j = 2602 ∨ j = 2430 ∨ j = 2400 ∨ j = 2401 ∨ j = 2451 →
      ¬ WS (sw j) := by
    rintro j (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp [WS, LblR, zX, zE, zH, zO, zA, zN, zL, zM, aF, sP, kN, kL, sw]
  have kp3 : ∀ j, (j = 2600 ∨ j = 2601 ∨ j = 2602 ∨ j = 2430 ∨ j = 2400 ∨ j = 2401 ∨ j = 2451) →
      c₃.nreg (sw j) = c₂.nreg (sw j) := fun j hj =>
    fr3 _ (not_oracle_sw (by ufo sw) (by unfold sw; rcases hj with h|h|h|h|h|h|h <;> omega))
      (ws j hj) (by unfold ALLOC sw; rcases hj with h|h|h|h|h|h|h <;> omega)
  have hSD3 : StopData P J N₂ c₃ rs ax := stopData_transport hSD2 (kp3 2601 (by norm_num))
    (kp3 2600 (by norm_num)) (kp3 2602 (by norm_num)) hlay2 m3
  have hlay3 : c₃.nreg sB + 5 * c₃.nreg sC ≤ c₃.nreg ALLOC ∧
      c₃.nreg aB + 5 * c₃.nreg sC ≤ c₃.nreg ALLOC := by
    have e1 : c₃.nreg sC = c₂.nreg sC := kp3 2601 (by norm_num)
    have e2 : c₃.nreg sB = c₂.nreg sB := kp3 2600 (by norm_num)
    have e3 : c₃.nreg aB = c₂.nreg aB := kp3 2602 (by norm_num)
    rw [e1, e2, e3]
    exact ⟨hlay2.1.trans A3, hlay2.2.trans A3⟩
  have e3E : c₃.nreg kE = pK0 J := (kp3 2400 (by norm_num)).trans e2E
  have e3H : c₃.nreg kH = 0 := (kp3 2401 (by norm_num)).trans e2H
  -- 3. the second stop step
  refine IRS.seq (K₁ := stStepK) (stStep_irs E hI₃ hSD3 hlay3 S3 e3E e3H (by omega)) ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨S4, a4, b4, fr4, A4, m4⟩
  have kp4 : ∀ j, (j = 2600 ∨ j = 2601 ∨ j = 2602 ∨ j = 2430 ∨ j = 2400 ∨ j = 2401 ∨ j = 2451) →
      c₄.nreg (sw j) = c₃.nreg (sw j) := fun j hj =>
    fr4 _ (not_oracle_sw (by ufo sw) (by unfold sw; rcases hj with h|h|h|h|h|h|h <;> omega))
      (ws j hj) (by unfold ALLOC sw; rcases hj with h|h|h|h|h|h|h <;> omega)
  -- the pointer
  have hptr : ∀ i (hi : i < rs.length), i < c₄.nreg sP ↔ soff P J rs[i] = Lst J := by
    obtain ⟨h1a, h1b⟩ := stepRes a3 b3 0 e2P.symm
    exact ptr_char hP hNF hst (s1 := c₃.nreg sP) h1a h1b a4 b4 (S4.2.2.2.1)
  -- 4. the label from a face
  obtain ⟨sN4, sP4, sPl4, sAt4, sLen4, sLab4, sReg4, aF4, aFi4⟩ := S4
  refine IRS.seq (K₁ := fposK 3 (c₀.nreg TLR) + 4) (stLab_irs E hI₄ aF4 (by omega)) ?_
  rintro c₅ hI₅ hA₅ hA₅' ⟨l5a, l5b, fr5, A5, m5⟩
  -- 5. the gap regions
  refine IRS.seq (K₁ := fposK 1 (c₀.nreg TLR) + fposK 2 (c₀.nreg TLR) + 5)
    (stGap_irs E hI₅ (by omega)) ?_
  rintro c₆ hI₆ hA₆ hA₆' ⟨g1, g2, g3, fr6, A6, m6⟩
  -- registers kept by stLab and stGap
  have u : ∀ q, Untouched q → c₆.nreg q = c.nreg q := by
    rintro q ⟨hq, h1, h2, h3, h4, h5, -, -, hqa⟩
    rw [fr6 q hq h3 h5 hqa, fr5 q hq h3 h4 hqa, fr4 q hq h2 hqa, fr3 q hq h2 hqa, o2 q h1]
  have lB6 : c₆.nreg lB = c.nreg lB := u _ (untouched_sw (j := 2430) (by norm_num) (by omega))
  -- 6. the log record
  refine (stLog_irs E.hK hI₆ (by rwx [lB6]) (by rw [lB6]; have := hI.hw.1 ALLOC; omega)).mono
    le_rfl ?_
  rintro c₇ ⟨lc7, fr7, mem7, r70, r71, r72, r73⟩
  rw [lB6] at mem7 r70 r71 r72 r73
  -- values at the end
  have k7  := fr7
  have nP : ∀ q, (q = sP ∨ q = aF) → ¬ FPR q ∧ ¬ LblR kN kL q ∧ ¬ GapR q ∧ q ≠ zX ∧ q ≠ lC ∧
      bandOf q ∉ oracleBands ∧ q ≠ ALLOC := by
    rintro q (rfl | rfl) <;> refine ⟨?_, ?_, ?_, ?_, ?_, not_oracle_sw (by simp [sP, aF, sw])
      (by simp [sP, aF, sw]), by simp [sP, aF, ALLOC, sw]⟩ <;>
      simp [FPR, FR, LblR, GapR, zT, fE, fA, fR, kN, kL, gN, gR, sP, aF, zX, lC, sw]
  have sP7 : c₇.nreg sP = c₄.nreg sP := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := nP sP (Or.inl rfl)
    rw [k7 _ h4 h5, fr6 _ h6 h1 h3 h7, fr5 _ h6 h1 h2 h7]
  have u2 : ∀ q, bandOf q ∉ oracleBands → ¬ WS q → ¬ FPR q → ¬ LblR kN kL q → ¬ GapR q →
      q ≠ ALLOC → c₆.nreg q = c₂.nreg q := fun q hq h2 h3 h4 h5 hqa => by
    rw [fr6 q hq h3 h5 hqa, fr5 q hq h3 h4 hqa, fr4 q hq h2 hqa, fr3 q hq h2 hqa]
  have hd : ∀ j, (j = 2400 ∨ j = 2401 ∨ j = 2451) → c₇.nreg (sw j) = c₂.nreg (sw j) := by
    intro j hj
    have hj' : 2400 ≤ j ∧ j ≤ 2451 := by omega
    rw [k7 _ (by ufo zX sw) (by ufo lC sw)]
    refine u2 _ (not_oracle_sw (by ufo sw) (by ufo sw)) ?_ ?_ ?_ ?_
      (by ufo ALLOC sw)
    · unfold WS LblR; sio only [zX, zE, zH, zO, zA, zN, zL, zM, aF, sP, kN, kL, sw]
    · unfold FPR FR; sio only [zT, fE, fA, fR, sw]
    · unfold LblR; sio only [kN, kL, sw]
    · unfold GapR; sio only [gN, gR, sw]
  have hl57 : ∀ q, LblR kN kL q → c₇.nreg q = c₅.nreg q := by
    intro q hq
    have hq' : 242402 ≤ q ∧ q ≤ 242406 := by
      unfold LblR at hq; sio only [kN, kL, sw] at hq
    rw [k7 q (by ufo zX sw) (by ufo lC sw)]
    exact fr6 q (not_oracle_sw (by omega) (by omega))
      (by unfold FPR FR; sio only [zT, fE, fA, fR, sw])
      (by unfold GapR; sio only [gN, gR, sw]) (by ufo ALLOC)
  have hlbl7  := lblOf_congrK hl57
  have hg67 : ∀ q, GapR q → c₇.nreg q = c₆.nreg q := fun q hq => by
    unfold GapR at hq
    exact k7 q (by sio only [gN, gR, zX, sw] at hq ⊢)
      (by sio only [gN, gR, lC, sw] at hq ⊢)
  have hlab45 : c₄.nreg aF = 1 → lblOf c₅ kN kL = lblOf c₄ kN kL := fun h =>
    lblOf_congrK (l5a h)
  have hN75  := hl57 kN (Or.inl rfl)
  have hL75 : c₇.nreg kL = c₅.nreg kL := hl57 kL (Or.inr ⟨le_rfl, by omega⟩)
  have one : ∀ (cc : Config), cc.nreg kN = 1 → lblOf cc kN kL = [cc.nreg kL] := fun cc h => by
    simp [lblOf, h]
  have hnot : (∀ i (hi : i < rs.length), soff P J rs[i] = Lst J → (ax.getD i d5).1 ≠ 1) →
      c₄.nreg aF ≠ 1 := by
    intro hall h1
    obtain ⟨i, hi, hia⟩ := aFi4.1 h1
    exact hall i (by omega) ((hptr i (by omega)).1 hi) hia
  have hA7 : c₇.nreg ALLOC = c₆.nreg ALLOC := k7 _ (by simp [ALLOC, zX, sw]) (by simp [ALLOC, lC, sw])
  refine ⟨?_, ?_, ?_, lc7, by rw [sP7]; exact sPl4, fun i hi => by rw [sP7]; exact hptr i hi, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hd 2400 (Or.inl rfl)).trans e2E
  · exact (hd 2401 (Or.inr (Or.inl rfl))).trans e2H
  · exact (hd 2451 (Or.inr (Or.inr rfl))).trans e2D
  · rw [hN75]
    by_cases h : c₄.nreg aF = 1
    · rw [l5a h kN (Or.inl rfl)]; exact sN4
    · rwn [(l5b h).1]
  · intro v hv
    rw [hlbl7] at hv
    by_cases h : c₄.nreg aF = 1
    · rw [hlab45 h] at hv; exact sReg4 v hv
    · obtain ⟨h1, h2, -⟩ := l5b h
      rw [one c₅ h1] at hv
      simp only [List.mem_singleton] at hv
      rwx [hv]
  · intro i hi hik hia v hv
    have hi'  := (hptr i hi).2 hik
    have h1  := aFi4.2 ⟨i, hi', hia⟩
    rw [hlbl7, hlab45 h1]
    exact sLab4 i hi' v hv
  · intro hall
    obtain ⟨h1, h2, h3⟩ := l5b (hnot hall)
    exact ⟨by rwx [hN75], by rwx [hL75], by rwx [hL75]⟩
  · rwx [hg67 gN (Or.inl rfl)]
  · intro i hi
    rw [hg67 gN (Or.inl rfl)] at hi
    have hi2 : i < 2 := by omega
    rw [hg67 (gR + i) (by ufo GapR)]
    exact g2 i hi
  · intro V hV
    obtain ⟨i, hi, hiV⟩ := g3 V hV
    have hi2 : i < 2 := by omega
    exact ⟨i, by rwx [hg67 gN (Or.inl rfl)],
      by rwx [hg67 (gR + i) (by ufo GapR)]⟩
  · rw [r70, k7 kE (by simp [kE, zX, sw]) (by simp [kE, lC, sw])]
  · rw [r71, k7 kH (by simp [kH, zX, sw]) (by simp [kH, lC, sw])]
  · rw [r72, k7 kN (by simp [kN, zX, sw]) (by simp [kN, lC, sw])]
  · intro i hi
    rw [r73 i hi, k7 (kL + i) (by ufo kL zX sw) (by ufo kL lC sw)]
  · intro x hx hx'
    rw [mem7 x hx', m6 x (by omega), m5 x (by omega), m4 x (by omega), m3 x (by omega), m2]
  · intro r hr hs hra
    have hu := untouched_of hr hs hra
    rw [k7 r hu.2.2.2.2.2.2.1 hu.2.2.2.2.2.2.2.1]
    exact u r hu
  · omega


end

end SweepEv

end Chazelle.Core
