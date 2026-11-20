module

public import Chazelle.Core.ClusterPhase1Exec

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
  cases h
  constructor <;>
    (rwa [hr _ (by unfold RegsR; omega)])

/-- **The potential of the initial stack.** -/
theorem segPot_segL {s μ L : ℕ} {bo : ℕ → ℕ} (hL : ∀ b, cntBelow bo μ b < 2 ^ L) (j : ℕ) :
    segPot (segL s μ bo j) ≤ L * cntLt bo μ j := by
  induction j with
  | zero => simp [segL, segPot]
  | succ j ih =>
    rw [cntLt_succ]
    simp only [segL, segPot, List.map_append, List.sum_append] at ih ⊢
    have hlen : len (cntLt bo μ j, cntLt bo μ (j + 1)) = cntBelow bo μ j := len_seg j
    have hsz := Nat.size_le.mpr (hL j)
    have : cntBelow bo μ j * Nat.size (cntBelow bo μ j) ≤ L * cntBelow bo μ j := by
      rw [Nat.mul_comm L]; exact Nat.mul_le_mul_left _ hsz
    unfold optSeg; split_ifs
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hlen]; nlinarith
    · simp only [List.map_nil, List.sum_nil]; nlinarith

/-- The stored graph only reads the map. -/
theorem memGraph_congr {m m' : ℕ → ℕ} {B μ E A : ℕ} (hA : MemEqBelow A m' m)
    (hB : B + 2 < A) (hO : m B + 2 * E ≤ A) (hV : m (B + 2) + 2 * E ≤ A)
    (hopp : ∀ d, d < 2 * E → m (m B + d) < 2 * E) :
    memGraph m' B μ E = memGraph m B μ E := by
  have eB : m' B = m B := hA _ (by omega)
  have eB2 := hA _ (by omega)
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
      refine ⟨d, hd, by ram_simp [hA] <;> omega, ?_⟩
      ram_simp [hA] <;> omega
  simp [memGraph, hmd]

theorem segL_congr {s μ : ℕ} {bo bo' : ℕ → ℕ} (h : ∀ w, w < μ → bo w = bo' w) (j : ℕ) :
    segL s μ bo j = segL s μ bo' j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [segL, ih, cntLt_congr h]

end

end Chazelle.Core.Cluster
