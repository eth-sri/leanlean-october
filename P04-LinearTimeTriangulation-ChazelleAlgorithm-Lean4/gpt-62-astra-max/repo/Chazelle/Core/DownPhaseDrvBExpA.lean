module

public import Chazelle.Core.DownPhaseDrvBPieces
public import Chazelle.Core.DownPhaseDrvRLib

/-!
# Down-phase base (D9), RAM: expansion of a host block, part 1 (point writes)

The expansion (`DrvB.ExpSpec`) writes the points of a host into the point array `PtArrB` at
`PA = r212015`, in walk order (`wlist li`): point `k` of `H.pts n` goes to the slot
`slotE li NP k` (`k`, or `NP - 1 - k` when `li = false`).  The output pointer `r212025` moves
forwards (`li`) or backwards (`¬ li`).

* `ESt`: the state of the expansion after `K` points;
* `wrV`, `wrE`: write the vertex `r212030`, the edge point `(r212027, r212028)`
  (`wrV_exec`, `wrE_exec`).
-/

set_option linter.unnecessarySeqFocus false

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt Programs
open BuildRam (FrameM FrameM.mono FrameM.trans exec_frameM wrM)

@[expose] public section

/-- The registers written by the expansion. -/
def Bexp : ℕ → Bool := fun r => decide (212023 ≤ r ∧ r ≤ 212031)

/-- The slot of point `k` (of `NP`) in the walk-order array. -/
def slotE (li : Bool) (NP k : ℕ) : ℕ := if li then k else NP - 1 - k

/-- The output pointer after `K` points. -/
def ptrE (li : Bool) (PA NP K : ℕ) : ℕ := if li then PA + 3 * K else PA + 3 * (NP - K)

/-- Write the vertex `r212030` at the output pointer (forwards or backwards). -/
def wrV : Stmt := .ifLtN 212001 212011
  (block [.storeN 212025 212001, .addN 212025 212025 212000, .storeN 212025 212030,
    .addN 212025 212025 212000, .addN 212025 212025 212000])
  (block [.subN 212025 212025 212000, .subN 212025 212025 212000, .storeN 212025 212030,
    .subN 212025 212025 212000, .storeN 212025 212001])

/-- Write the edge point `(r212027, r212028)` at the output pointer. -/
def wrE : Stmt := .ifLtN 212001 212011
  (block [.storeN 212025 212000, .addN 212025 212025 212000, .storeN 212025 212027,
    .addN 212025 212025 212000, .storeN 212025 212028, .addN 212025 212025 212000])
  (block [.subN 212025 212025 212000, .storeN 212025 212028, .subN 212025 212025 212000,
    .storeN 212025 212027, .subN 212025 212025 212000, .storeN 212025 212000])

/-- **The state of the expansion** after the first `K` points of `L`. -/
structure ESt (W n PA : ℕ) (li : Bool) (L : List SymPt) (c₀ c : Config) (K : ℕ) : Prop where
  wb : WordsBounded W c
  le : K ≤ L.length
  hW : PA + 3 * L.length ≤ W
  fr : FrameM Bexp c₀ c
  r0 : c.nreg 212000 = 1
  r1 : c.nreg 212001 = 0
  rli : c.nreg 212011 = if li then 1 else 0
  rn : c.nreg 212010 = n
  mem : ∀ a, (a < PA ∨ PA + 3 * L.length ≤ a) → c.nmem a = c₀.nmem a
  pts : ∀ k, k < K → PtAtB c.nmem (PA + 3 * slotE li L.length k) (L.getD k (.vtx 0))
  ptr : c.nreg 212025 = ptrE li PA L.length K

theorem PtAtB.congr {m m' : ℕ → ℕ} {a : ℕ} {x : SymPt} (h : PtAtB m a x)
    (hm : ∀ b, a ≤ b → b < a + 3 → m' b = m b) : PtAtB m' a x := by
  cases x with
  | vtx i =>
    exact ⟨(hm a le_rfl (by omega)).trans h.1, (hm (a + 1) (by omega) (by omega)).trans h.2⟩
  | onEdge e h' =>
    exact ⟨(hm a le_rfl (by omega)).trans h.1, (hm (a + 1) (by omega) (by omega)).trans h.2.1,
      (hm (a + 2) (by omega) (by omega)).trans h.2.2⟩

theorem slotE_lt {li : Bool} {NP k : ℕ} (hk : k < NP) : slotE li NP k < NP := by
  unfold slotE; split <;> omega

theorem slotE_ne {li : Bool} {NP k k' : ℕ} (hk : k < NP) (hk' : k' < NP) (h : k ≠ k') :
    slotE li NP k ≠ slotE li NP k' := by
  unfold slotE; split <;> omega

/-- **One more point**: the new slot written, nothing else changed. -/
theorem ESt.step {W n PA : ℕ} {li : Bool} {L : List SymPt} {c₀ c c' : Config} {K : ℕ}
    (hS : ESt W n PA li L c₀ c K) (hK : K < L.length) (hw : WordsBounded W c')
    (hf : FrameM (fun r => decide (r = 212025)) c c')
    (hm : ∀ a, (a < PA + 3 * slotE li L.length K ∨ PA + 3 * slotE li L.length K + 3 ≤ a) →
      c'.nmem a = c.nmem a)
    (hp : PtAtB c'.nmem (PA + 3 * slotE li L.length K) (L.getD K (.vtx 0)))
    (hptr : c'.nreg 212025 = ptrE li PA L.length (K + 1)) :
    ESt W n PA li L c₀ c' (K + 1) := by
  have hsl := slotE_lt (li := li) hK
  have hreg : ∀ r, r ≠ 212025 → c'.nreg r = c.nreg r := fun r hr =>
    hf.1 r (by simpa using hr)
  refine ⟨hw, by omega, hS.hW, hS.fr.trans (hf.mono fun r hr => ?_), ?_, ?_, ?_, ?_, ?_, ?_, hptr⟩
  · simp only [decide_eq_true_eq] at hr; subst hr; decide
  · rw [hreg _ (by decide)]; exact hS.r0
  · rw [hreg _ (by decide)]; exact hS.r1
  · rw [hreg _ (by decide)]; exact hS.rli
  · rw [hreg _ (by decide)]; exact hS.rn
  · intro a ha
    rw [hm a (by omega)]; exact hS.mem a ha
  · intro k hk
    rcases Nat.lt_or_ge k K with hk' | hk'
    · have hne := slotE_ne (li := li) (by omega) hK (Nat.ne_of_lt hk')
      refine (hS.pts k hk').congr fun b hb1 hb2 => hm b ?_
      rcases Nat.lt_or_gt_of_ne hne with h | h <;> omega
    · have : k = K := by omega
      subst this; exact hp

/-- **Register writes** (other than the output pointer) keep the state. -/
theorem ESt.frame {W n PA : ℕ} {li : Bool} {L : List SymPt} {c₀ c c' : Config} {K : ℕ}
    (hS : ESt W n PA li L c₀ c K) (hw : WordsBounded W c') (hf : FrameM Bexp c c')
    (h25 : c'.nreg 212025 = c.nreg 212025) (hm : c'.nmem = c.nmem) :
    ESt W n PA li L c₀ c' K := by
  refine ⟨hw, hS.le, hS.hW, hS.fr.trans hf, ?_, ?_, ?_, ?_, ?_, ?_, h25.trans hS.ptr⟩
  · rw [hf.1 _ (by decide)]; exact hS.r0
  · rw [hf.1 _ (by decide)]; exact hS.r1
  · rw [hf.1 _ (by decide)]; exact hS.rli
  · rw [hf.1 _ (by decide)]; exact hS.rn
  · intro a ha; rw [hm]; exact hS.mem a ha
  · intro k hk; rw [hm]; exact hS.pts k hk

theorem wr_wrV : wrM (fun r => decide (r = 212025)) wrV = true := by decide
theorem wr_wrE : wrM (fun r => decide (r = 212025)) wrE = true := by decide

section exec

variable {P : Polygon} {W : ℕ}

/-- **Writing a vertex.** -/
theorem wrV_exec {n PA : ℕ} {li : Bool} {L : List SymPt} {c₀ c : Config} {K : ℕ}
    (hS : ESt W n PA li L c₀ c K) (hK : K < L.length)
    (hx : L.getD K (.vtx 0) = .vtx (c.nreg 212030)) :
    ∃ c' k, Exec P W wrV c c' k ∧ k ≤ 7 ∧ ESt W n PA li L c₀ c' (K + 1) ∧
      FrameM (fun r => decide (r = 212025)) c c' := by
  have hwb := hS.wb
  have hW := hS.hW
  obtain ⟨c', k, ex, hk, hm, hp, hptr⟩ : ∃ c' k, Exec P W wrV c c' k ∧ k ≤ 7 ∧
      (∀ a, (a < PA + 3 * slotE li L.length K ∨ PA + 3 * slotE li L.length K + 3 ≤ a) →
        c'.nmem a = c.nmem a) ∧
      PtAtB c'.nmem (PA + 3 * slotE li L.length K) (L.getD K (.vtx 0)) ∧
      c'.nreg 212025 = ptrE li PA L.length (K + 1) := by
    have h0 := hS.r0
    have h1 := hS.r1
    have hl := hS.rli
    have hp := hS.ptr
    rw [hx]
    cases li
    · refine spec_ifLtN_false (by simp only [h1, hl]; simp) ?_
      exec_block
      simp only [ptrE, slotE, Bool.false_eq_true, ite_false] at hp ⊢
      simp only [h0, h1, hp, PtAtB, Machine.upd_same]
      refine ⟨by omega, fun a ha => ?_, ?_, by omega⟩
      · simp only [upd]; split_ifs <;> omega
      · simp only [upd]; split_ifs <;> omega
    · refine spec_ifLtN_true (by simp only [h1, hl]; simp) ?_
      simp only [ptrE, slotE, ↓reduceIte] at hp ⊢
      exec_block
      all_goals config_simp
      all_goals simp only [h0, h1, hp, PtAtB, Machine.upd_same]
      · omega
      · omega
      · omega
      refine ⟨by omega, fun a ha => ?_, ?_, by omega⟩
      · simp only [upd]; split_ifs <;> omega
      · refine ⟨?_, ?_⟩ <;> simp only [upd] <;> (try split_ifs) <;> omega
  exact ⟨c', k, ex, hk, hS.step hK ex.wb_right (exec_frameM ex wr_wrV) hm hp hptr,
    exec_frameM ex wr_wrV⟩

/-- **Writing an edge point.** -/
theorem wrE_exec {n PA : ℕ} {li : Bool} {L : List SymPt} {c₀ c : Config} {K : ℕ}
    (hS : ESt W n PA li L c₀ c K) (hK : K < L.length)
    (hx : L.getD K (.vtx 0) = .onEdge (c.nreg 212027) (c.nreg 212028)) :
    ∃ c' k, Exec P W wrE c c' k ∧ k ≤ 8 ∧ ESt W n PA li L c₀ c' (K + 1) ∧
      FrameM (fun r => decide (r = 212025)) c c' := by
  have hwb := hS.wb
  have hW := hS.hW
  obtain ⟨c', k, ex, hk, hm, hp, hptr⟩ : ∃ c' k, Exec P W wrE c c' k ∧ k ≤ 8 ∧
      (∀ a, (a < PA + 3 * slotE li L.length K ∨ PA + 3 * slotE li L.length K + 3 ≤ a) →
        c'.nmem a = c.nmem a) ∧
      PtAtB c'.nmem (PA + 3 * slotE li L.length K) (L.getD K (.vtx 0)) ∧
      c'.nreg 212025 = ptrE li PA L.length (K + 1) := by
    have h0 := hS.r0
    have h1 := hS.r1
    have hl := hS.rli
    have hp := hS.ptr
    rw [hx]
    cases li
    · refine spec_ifLtN_false (by simp only [h1, hl]; simp) ?_
      exec_block
      simp only [ptrE, slotE, Bool.false_eq_true, ite_false] at hp ⊢
      simp only [h0, hp, PtAtB, Machine.upd_same]
      refine ⟨by omega, fun a ha => ?_, ?_, by omega⟩
      · simp only [upd]; split_ifs <;> omega
      · refine ⟨?_, ?_, ?_⟩ <;> simp only [upd] <;> (try split_ifs) <;> omega
    · refine spec_ifLtN_true (by simp only [h1, hl]; simp) ?_
      simp only [ptrE, slotE, ↓reduceIte] at hp ⊢
      exec_block
      all_goals config_simp
      all_goals simp only [h0, hp, PtAtB, Machine.upd_same]
      · omega
      · omega
      · omega
      refine ⟨by omega, fun a ha => ?_, ?_, by omega⟩
      · simp only [upd]; split_ifs <;> omega
      · refine ⟨?_, ?_, ?_⟩ <;> simp only [upd] <;> (try split_ifs) <;> omega
  exact ⟨c', k, ex, hk, hS.step hK ex.wb_right (exec_frameM ex wr_wrE) hm hp hptr,
    exec_frameM ex wr_wrE⟩

end exec

end

end DrvB

end Chazelle.Core
