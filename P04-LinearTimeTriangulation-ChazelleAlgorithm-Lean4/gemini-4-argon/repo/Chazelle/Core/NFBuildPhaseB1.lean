module

public import Chazelle.Core.NFBuildPhaseBAux

/-!
# WP-C (BuildNF), RAM part 22: phase B up to the end of the main pass

`phaseB1_exec`: `setupB`, `lohiS` and the main pass `passLoop`, from the state after the sort,
reach `PassInv (2K)` with the fixed registers `BConst`.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK NFLoc
open BuildNF (stk gapsB)

@[expose] public section

/-- The first part of phase B. -/
def phaseB1 : Stmt := .seq setupB (.seq lohiS passLoop)

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- **Phase B up to the end of the main pass.** -/
theorem phaseB1_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {M : Model} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {D T SE B H : ℕ}
    (hI : BuildNF.Input M (Qof P) L E) (hlen : E.length = 2 * L.length)
    (hD : c.nreg 40000 = D) (hT : c.nreg 42000 = T) (hN : c.nreg 42001 = 2 * L.length)
    (hB : c.nreg 43001 = B) (hK : c.nreg 43002 = L.length) (h0 : c.nreg 43010 = 0)
    (h1 : c.nreg 43011 = 1) (hSEr : c.nreg 30005 = SE) (hH : c.nreg 9999 = H)
    (hwf : ModelDescWF P H c.nmem D) (hM : ModelDescAt c.nmem D (Qof P) M)
    (hR : RecsAt c.nmem T L) (hTH : T + 8 * L.length ≤ H) (hCL : ChordListAt c.nmem B L)
    (hBH : B + 3 * L.length ≤ H) (hSE : ∀ j, j < E.length → c.nmem (SE + j) = E.getD j 0)
    (hSEH : SE + E.length ≤ H) (hroom : H + sizeB L.length ≤ W) :
    ∃ c₃ k, Exec P W phaseB1 c c₃ k ∧ k ≤ 11702 * E.length + 48 ∧ 12 * E.length ≤ k ∧
      WordsBounded W c₃ ∧
      BConst D T L.length B H (loOf c.nmem D) (hdOf c.nmem D P.n) (c.nmem D) c₃ ∧
      ∃ (F : PassFix P W M L E D H T SE B (H + 12) (H + 12 + 5 * L.length)
          (H + 17 + 26 * L.length) (H + 17 + 28 * L.length) (loOf c.nmem D)
          (hdOf c.nmem D P.n) c.nmem) (c₂ : Config), PassInv F c₂ c₃ E.length := by
  set K := L.length
  have hHW : H ≤ W := by unfold sizeB at hroom; omega
  obtain ⟨hDW, hCW⟩ := locChainWF_of hwf hHW hWn
  -- 1. setup
  obtain ⟨c₁, k₁, x₁, hk₁, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15,
    s16, s17, s18, s19, s20⟩ := setupB_exec (P := P) c hw hK hN h1 hH hSEr hroom
  have w₁ := x₁.wb_right
  have f₁ := exec_frameB x₁ wr_setupB
  have g₁ : ∀ r, BsetupB r = false → c₁.nreg r = c.nreg r := f₁.1
  -- 2. the counted interval
  obtain ⟨c₂, k₂, x₂, hk₂, l1, l2, l3, l4, f₂⟩ := lohiS_exec (P := P) c₁ w₁ (D := D)
    (by rw [g₁ _ (by decide), hD]) (by rw [f₁.2.2.1]; exact twice_m_le hM hCW)
    (by omega) (by unfold hostWords at hWn; omega) (by unfold hostWords at hWn; omega)
  rw [f₁.2.2.1] at l1 l2 l3
  have w₂ := x₂.wb_right
  have g₂ : ∀ r, r ≠ 41023 → r ≠ 41019 → r ≠ 44020 → r ≠ 44021 → r ≠ 44022 →
      c₂.nreg r = c₁.nreg r := fun r a1 a2 a3 a4 a5 => f₂.1 r (by
    simp only [decide_eq_false_iff_not]; omega)
  have mm₂ : c₂.nmem = c.nmem := by rw [f₂.2.2.1, f₁.2.2.1]
  have G₂ : ∀ r, BsetupB r = false → r ≠ 41023 → r ≠ 41019 → r ≠ 44020 → r ≠ 44021 →
      r ≠ 44022 → c₂.nreg r = c.nreg r := fun r h a1 a2 a3 a4 a5 => by
    rw [g₂ r a1 a2 a3 a4 a5, g₁ r h]
  have C₂ : BConst D T K B H (loOf c.nmem D) (hdOf c.nmem D P.n) (c.nmem D) c₂ :=
    { rD := by rw [G₂ 40000 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num), hD]
      rT := by rw [G₂ 42000 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num), hT]
      rN := by rw [G₂ 42001 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num), hN]
      r1a := by rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s1]
      rB := by rw [G₂ 43001 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num), hB]
      rK := by rw [G₂ 43002 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num), hK]
      r0 := by rw [G₂ 43010 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num), h0]
      r1 := by rw [G₂ 43011 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num), h1]
      r3 := by rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s2]
      rR := by rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s3]
      rH := by rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s4]
      rCT := by rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s5]
      rAT := by rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s6]
      rRT := by rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s7]
      rQT := by rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s8]
      rLT := by rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s9]
      rST := by rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s10]
      rWT := by rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s11]
      rCA := by rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s12]
      rFA := by rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s13]
      rFC := by rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s14]
      rA := by rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s15]
      rlo := l1
      rhd := l2
      r19 := l4
      r23 := l3 }
  -- 3. the main pass
  obtain ⟨hcI, hcW⟩ := BuildRam.countedIv (P := P) hM
  have hlohi : loOf c.nmem D ≤ hiOf c.nmem D P.n := by
    unfold loOf hiOf; split_ifs <;> omega
  have F : PassFix P W M L E D H T SE B (H + 12) (H + 12 + 5 * K) (H + 17 + 26 * K)
      (H + 17 + 28 * K) (loOf c.nmem D) (hdOf c.nmem D P.n) c.nmem :=
    { inp := hI, good := hG, hwords := hWn, len := hlen, wf := hwf, desc := hM, HW := hHW,
      recs := hR, TH := hTH, chl := hCL, BH := hBH, codes := hSE, SEH := hSEH,
      l1 := by omega, l2 := by omega, l3 := by omega, l4 := by omega,
      l5 := by unfold sizeB at hroom; omega
      cnt := fun p hp => by rw [hcI p hp, hdOf_eq]; omega
      cntW := by rw [hdOf_eq]; omega }
  have n100 : c₂.nreg 43100 = 0 := by
    rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s16]
  have n103 : c₂.nreg 43103 = SE + 0 := by
    rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s19,
      Nat.add_zero]
  have n104 : c₂.nreg 43104 = SE := by
    rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s20]
  have n101 : c₂.nreg 43101 = (stk E 0).length := by
    rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s17]; rfl
  have n102 : c₂.nreg 43102 = (gapsB M (Qof P) L E 0).length := by
    rw [g₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), s18]; rfl
  have nN : c₂.nreg 42001 = E.length := by rw [C₂.rN, hlen]
  have I₀ : PassInv F c₂ c₂ 0 :=
    { m_le := Nat.zero_le _, r100 := n100, r103 := n103, r104 := n104, r101 := n101,
      sp_le := by simp [stk, BuildNF.cw, BuildStack.run], r102 := n102,
      rD := C₂.rD, rT := C₂.rT, rN := nN, r1a := C₂.r1a, rB := C₂.rB,
      r0 := C₂.r0, r1 := C₂.r1, rCT := C₂.rCT, rAT := C₂.rAT, rST := C₂.rST, rWT := C₂.rWT,
      rlo := C₂.rlo, rhd := C₂.rhd, r19 := C₂.r19, r23 := C₂.r23,
      low := fun a _ => by rw [mm₂],
      stack := fun k hk => by simp [stk, BuildNF.cw, BuildStack.run] at hk,
      chords := fun x _ hx => by simp at hx,
      arcs := fun j hj => by simp [gapsB] at hj,
      frame := FrameM.refl _ _ }
  obtain ⟨c₃, k₃, x₃, hk₃, hk₃', w₃, I₃⟩ := passLoop_exec F I₀ w₂
  have C₃ := C₂.frame I₃.frame (by decide)
  exact ⟨c₃, _, .seq x₁ (.seq x₂ x₃), by omega, by omega, w₃, C₃, F, c₂, I₃⟩

end exec

end

end BuildRam

end Chazelle.Core
