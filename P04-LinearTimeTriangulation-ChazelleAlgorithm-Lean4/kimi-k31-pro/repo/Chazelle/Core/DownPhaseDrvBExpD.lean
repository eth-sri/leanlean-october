module

public import Chazelle.Core.DownPhaseDrvBExpC
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics

/-!
# Down-phase base (D9), RAM: expansion of a host block, part 4 (the program)

`expS`: initialise the item pointer `r212023 = HB + 1`, the item counter `r212024 = 0` and the
output pointer `r212025` (`PA`, or `PA + 3 NP` when the walk order is reversed), then run
`itemS` for every host item.  **`expSpec : ExpSpec`** (contract in `DownPhaseDrvBPieces`).
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt Programs
open BuildRam (FrameM FrameM.mono FrameM.trans exec_frameM wrM)

@[expose] public section

/-- Initialise the pointers and the counter. -/
def initS : Stmt := .seq (block [.addN 212023 212022 212000, .copyN 212024 212001])
  (.ifLtN 212001 212011 (.instr (.copyN 212025 212015))
    (block [.addN 212025 212015 212016, .addN 212025 212025 212016,
      .addN 212025 212025 212016]))

/-- **The expansion of a host block** into the point array. -/
def expS : Stmt := .seq initS (.whileLtN 212024 212021 itemS)

theorem wr_initS : wrM Bexp initS = true := by decide

/-- The final state is the point array in walk order. -/
theorem ESt.arr {W n PA : ℕ} {li : Bool} {L : List SymPt} {c₀ c : Config}
    (hS : ESt W n PA li L c₀ c L.length) : PtArrB c.nmem PA (wlist li L) := by
  intro k hk
  cases li
  · simp only [wlist, Bool.false_eq_true, ↓reduceIte, List.length_reverse] at hk ⊢
    have h := hS.pts (L.length - 1 - k) (by omega)
    simp only [slotE, Bool.false_eq_true, ↓reduceIte] at h
    rw [show L.length - 1 - (L.length - 1 - k) = k by omega] at h
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_reverse,
      ← List.getD_eq_getElem _ (.vtx 0)]
    exact h
  · simp only [wlist, ↓reduceIte] at hk ⊢
    simpa [slotE] using hS.pts k hk

section exec

variable {P : Polygon} {W : ℕ}

theorem initS_exec (c : Config) (hw : WordsBounded W c) (li : Bool) (NP : ℕ)
    (h0 : c.nreg 212000 = 1) (h1 : c.nreg 212001 = 0)
    (h11 : c.nreg 212011 = if li then 1 else 0) (h16 : c.nreg 212016 = NP)
    (hHB : c.nreg 212022 + 1 ≤ c.nreg 212015) (hPW : c.nreg 212015 + 3 * NP ≤ W) :
    ∃ c₁ k₁, Exec P W initS c c₁ k₁ ∧ k₁ ≤ 7 ∧ c₁.nreg 212023 = c.nreg 212022 + 1 ∧
      c₁.nreg 212024 = 0 ∧ c₁.nreg 212025 = ptrE li (c.nreg 212015) NP 0 ∧
      c₁.nmem = c.nmem := by
  unfold initS
  refine spec_seq ?_
  exec_block
  · rwo [h0]
  · cases li
    · refine spec_ifLtN_false (by config_simp; rws [h1, h11]) ?_
      exec_block
      · config_simp; rwo [h16]
      · config_simp; rwo [h16]
      · config_simp; rwo [h16]
      · refine ⟨by omega, ?_, ?_, ?_, rfl⟩ <;> config_simp
        · rw [h0]
        · rw [h1]
        · rsio [h16] only [ptrE, Bool.false_eq_true, ↓reduceIte]
    · refine spec_ifLtN_true (by config_simp; rws [h1, h11]) ?_
      refine spec_instr (Machine.Exec.copyN ‹_› _ _) fun _ => ?_
      refine ⟨by omega, ?_, ?_, ?_, rfl⟩ <;> config_simp
      · rw [h0]
      · rw [h1]
      · simp [ptrE]

end exec

/-- **The expansion of a host block** (`ExpSpec`, contract of the base case). -/
theorem expSpec : ExpSpec := by
  refine ⟨expS, 40, fun P W c H li hw hH hWF h21 h16 h11 h10 h0 h1 h2 hHB hPW => ?_⟩
  obtain ⟨c₁, k₁, x₁, hk₁, h23, h24, h25, hm⟩ :=
    initS_exec (P := P) c hw li (H.pts P.n).length h0 h1 h11 h16 (by omega) hPW
  have f₁ := exec_frameM x₁ wr_initS
  have S₀ : ESt W P.n (c.nreg 212015) li (H.pts P.n) c c₁ 0 :=
    ⟨x₁.wb_right, Nat.zero_le _, hPW, f₁, (f₁.1 _ (by decide)).trans h0,
      (f₁.1 _ (by decide)).trans h1, (f₁.1 _ (by decide)).trans h11,
      (f₁.1 _ (by decide)).trans h10, fun a _ => by rw [hm],
      fun k hk => absurd hk (Nat.not_lt_zero _), h25⟩
  have hz : (Host.pts P.n (H.take 0)).length = 0 := by simp [Host.pts]
  have I₀ : IInv W P.n (c.nreg 212015) (c.nreg 212022) li H c 0 c₁ :=
    ⟨by rw [hz]; exact S₀, by rw [h23], h24⟩
  obtain ⟨c', k₂, x₂, ⟨hS', -, -⟩, hk₂⟩ := forLoopPot (P := P) (W := W) (ir := 212024)
    (nr := 212021) (body := itemS) (IInv W P.n (c.nreg 212015) (c.nreg 212022) li H c)
    (fun q => 30 * ((Host.pts P.n (H.take q)).length + q)) H.length
    (fun q e ⟨hS, _, h24⟩ => ⟨hS.wb, h24, (hS.fr.1 _ (by decide)).trans h21⟩)
    (fun q e hq hI => itemS_exec (P := P) hH hWF h2 hHB hq hI) I₀ (Nat.zero_le _)
  have hfull : H.take H.length = H := List.take_of_length_le le_rfl
  rw [hfull] at hS' hk₂
  rw [hz] at hk₂
  refine ⟨c', k₁ + k₂, .seq x₁ x₂, ?_, hS'.arr, hS'.mem, hS'.fr⟩
  simp only [Host.pts] at hk₂ ⊢
  omega

end

end DrvB

end Chazelle.Core
