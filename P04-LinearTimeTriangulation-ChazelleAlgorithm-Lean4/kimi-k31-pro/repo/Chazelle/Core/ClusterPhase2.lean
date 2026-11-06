module

public import Chazelle.Core.ClusterPhase1Exec
public import Chazelle.Rwx
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics

/-!
# WP-I, part 69: the second phase — definitions and helper facts

`phase2 = regsS; stkS; driverStmt; flagS; labS; outS; bumpS`.
-/

namespace Chazelle.Core.Cluster

open Machine Machine.Stmt Programs Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

/-- The registers holding the driver layout. -/
def RegsR (r : ℕ) : Prop := r = 130001 ∨ r = 130009 ∨ (130320 ≤ r ∧ r ≤ 130345) ∨
  (130601 ≤ r ∧ r ≤ 130620) ∨ (130632 ≤ r ∧ r ≤ 130655) ∨ (130674 ≤ r ∧ r ≤ 130700)

theorem SS.Regs.of_frameR {S : SS} {c c' : Config} (h : S.Regs c)
    (hr : ∀ r, RegsR r → c'.nreg r = c.nreg r) : S.Regs c' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38,
    h39, h40, h41, h42, h43, h44⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hr _ (by ufo RegsR)]; assumption)

/-- **The potential of the initial stack.** -/
theorem segPot_segL {s μ L : ℕ} {bo : ℕ → ℕ} (hL : ∀ b, cntBelow bo μ b < 2 ^ L) (j : ℕ) :
    segPot (segL s μ bo j) ≤ L * cntLt bo μ j := by
  induction j with
  | zero => simp [segL, segPot]
  | succ j ih =>
    rw [cntLt_succ]
    simp [segL, segPot, List.map_append, List.sum_append] at ih ⊢
    have hlen : len (cntLt bo μ j, cntLt bo μ (j + 1)) = cntBelow bo μ j := len_seg j
    have hsz : Nat.size (cntBelow bo μ j) ≤ L := Nat.size_le.mpr (hL j)
    have : cntBelow bo μ j * Nat.size (cntBelow bo μ j) ≤ L * cntBelow bo μ j := by
      rw [Nat.mul_comm L]; exact Nat.mul_le_mul_left _ hsz
    unfold optSeg; split_ifs
    · sinl only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hlen]
    · sinl only [List.map_nil, List.sum_nil]

/-- The stored graph only reads the map. -/
theorem memGraph_congr {m m' : ℕ → ℕ} {B μ E A : ℕ} (hA : ∀ a, a < A → m' a = m a)
    (hB : B + 2 < A) (hO : m B + 2 * E ≤ A) (hV : m (B + 2) + 2 * E ≤ A)
    (hopp : ∀ d, d < 2 * E → m (m B + d) < 2 * E) :
    memGraph m' B μ E = memGraph m B μ E := by
  have eB : m' B = m B := hA _ (by omega)
  have eB2 : m' (B + 2) = m (B + 2) := hA _ (by omega)
  have hmd : ∀ u v, MemDart m' B E u v ↔ MemDart m B E u v := fun u v => by
    unfold MemDart
    rw [eB, eB2]
    constructor
    · rintro ⟨d, hd, h1, h2⟩
      have ho := hopp d hd
      rw [hA (m (B + 2) + d) (by omega)] at h1
      rw [hA (m B + d) (by omega), hA (m (B + 2) + m (m B + d)) (by omega)] at h2
      exact ⟨d, hd, h1, h2⟩
    · rintro ⟨d, hd, h1, h2⟩
      have ho := hopp d hd
      refine ⟨d, hd, by rwx [hA (m (B + 2) + d) (by omega)], ?_⟩
      rwx [hA (m B + d) (by omega), hA (m (B + 2) + m (m B + d)) (by omega)]
  ext u v
  simp [memGraph, hmd]

theorem segL_congr {s μ : ℕ} {bo bo' : ℕ → ℕ} (h : ∀ w, w < μ → bo w = bo' w) (j : ℕ) :
    segL s μ bo j = segL s μ bo' j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [segL, ih, cntLt_congr h]

end

end Chazelle.Core.Cluster
