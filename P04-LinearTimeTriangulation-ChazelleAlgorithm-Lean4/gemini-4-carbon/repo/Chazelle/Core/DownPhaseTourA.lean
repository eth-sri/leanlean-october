module

public import Chazelle.Core.DownPhaseLocal

/-!
# WP-M (X, part 4): side `A` of the tour of a chain

The tour of the corrected walk `C.sideWalk β` passes every chain edge twice, once with
increasing vertex index (**side `A`**) and once with decreasing index.  `tourA β k` is the tour
index at which chain edge `k` (from vertex `k` to `k + 1`) is walked on side `A`, so walk edge
`tourA β k + 6` goes from `C.vertex k` to `C.vertex (k + 1)`.

Consecutive side-`A` edges are consecutive walk edges except at the tour start
(`k + 1 = sideS β mod 2m`, the top vertex when the slit leaves on side `A`)
(`tourA_succ`).  At side-`A` positions the points and the left sectors are those of the chain
(`sidePt_tourA`, `sideLeft_tourA_vtx`, `sideLeft_tourA_edge`).
-/

namespace Chazelle.Core

namespace TourA

@[expose] public section

open Set
open Chazelle.Chain (sidePt sideLeft sideLeftOf sideE)
open Chazelle.Geometry (lerp)

variable (C : Chain) (β : Bool)

/-- The start of the tour, reduced. -/
noncomputable def sA : ℕ := C.sideS β % (2 * C.m)

/-- **The side-`A` tour index** of chain edge `k`. -/
noncomputable def tourA (k : ℕ) : ℕ := (k + 2 * C.m - sA C β) % (2 * C.m)

variable {C β}

theorem sA_lt : sA C β < 2 * C.m := Nat.mod_lt _ C.two_m_pos

theorem tourA_lt (k : ℕ) : tourA C β k < 2 * C.m := Nat.mod_lt _ C.two_m_pos

theorem mod_tourA {k : ℕ} (hk : k < 2 * C.m) : (C.sideS β + tourA C β k) % (2 * C.m) = k := by
  have hs := sA_lt (C := C) (β := β)
  unfold tourA
  rw [Nat.add_mod, show C.sideS β % (2 * C.m) = sA C β from rfl, Nat.mod_mod]
  have e : sA C β + (k + 2 * C.m - sA C β) % (2 * C.m) ≡ k [MOD 2 * C.m] := by
    have h1 : sA C β + (k + 2 * C.m - sA C β) % (2 * C.m) ≡
        sA C β + (k + 2 * C.m - sA C β) [MOD 2 * C.m] :=
      Nat.ModEq.add_left _ (Nat.mod_modEq _ _)
    have h2 : sA C β + (k + 2 * C.m - sA C β) = k + 2 * C.m := by omega
    rw [h2] at h1
    exact h1.trans (by simp [Nat.ModEq])
  rw [e, Nat.mod_eq_of_lt hk]

theorem sideIdx_tourA {k : ℕ} (hk : k < C.m) : C.sideIdx β (tourA C β k) = k := by
  rw [Chain.sideIdx_eq, mod_tourA (by omega)]
  unfold sideE; rw [ite_eq_left hk.le]

theorem sideIdx_tourA_succ {k : ℕ} (hk : k < C.m) : C.sideIdx β (tourA C β k + 1) = k + 1 := by
  rw [C.sideIdx_succ, mod_tourA (by omega)]
  unfold sideE; rw [ite_eq_left (by omega)]

theorem vtx_tourA {k : ℕ} (hk : k < C.m) :
    (C.sideWalk β).vtx (tourA C β k + 6) = C.vertex k := by
  rw [C.sideWalk_vtx_tour β (tourA_lt k).le]
  unfold Chain.sideTour; rw [sideIdx_tourA hk]

theorem vtx_tourA_succ {k : ℕ} (hk : k < C.m) :
    (C.sideWalk β).vtx ((tourA C β k + 6 + 1) % (C.sideWalk β).n) = C.vertex (k + 1) := by
  rw [C.sideWalk_next_tour β (tourA_lt k), C.sideWalk_vtx_tour β (tourA_lt k)]
  unfold Chain.sideTour; rw [sideIdx_tourA_succ hk]

/-- **The points of side `A`.** -/
theorem sidePt_tourA {k : ℕ} (hk : k < C.m) (s : ℝ) :
    sidePt (C.sideWalk β) (tourA C β k + 6) s = lerp (C.vertex k) (C.vertex (k + 1)) s := by
  unfold sidePt; rw [vtx_tourA hk, vtx_tourA_succ hk]

/-- **Contiguity of side `A`**: consecutive side-`A` edges are consecutive walk edges, except at
the tour start. -/
theorem tourA_succ {k : ℕ} (hk : k + 1 < 2 * C.m) (hne : k + 1 ≠ sA C β) :
    tourA C β (k + 1) = tourA C β k + 1 := by
  have hs := sA_lt (C := C) (β := β)
  unfold tourA
  rcases Nat.lt_or_ge k (sA C β) with h | h
  · -- `k < sA`, so `k + 1 < sA`
    have h' : k + 1 < sA C β := lt_of_le_of_ne h hne
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show k + 1 + 2 * C.m - sA C β = (k + 1 - sA C β) + 2 * C.m by omega,
      show k + 2 * C.m - sA C β = (k - sA C β) + 2 * C.m by omega,
      Nat.add_mod_right, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- The side-`A` tour index is positive away from the tour start. -/
theorem tourA_pos {k : ℕ} (hk : k < 2 * C.m) (hne : k ≠ sA C β) : 0 < tourA C β k := by
  by_contra h
  push Not at h
  have h0 : tourA C β k = 0 := by omega
  have := mod_tourA (C := C) (β := β) hk
  rw [h0, add_zero] at this
  exact hne (this.symm.trans rfl)

/-- **The left sector at a side-`A` vertex** away from the tour start: the corner of the chain. -/
theorem sideLeft_tourA_vtx {k : ℕ} (h0 : 0 < k) (hk : k < C.m) (hne : k ≠ sA C β) (x : Point) :
    sideLeft (C.sideWalk β) (tourA C β k + 6) 0 x ↔
      sideLeftOf (C.vertex (k - 1)) (C.vertex k) (C.vertex (k + 1)) x := by
  have hpos := tourA_pos (C := C) (β := β) (show k < 2 * C.m by omega) hne
  have hsucc : tourA C β k = tourA C β (k - 1) + 1 := by
    have := tourA_succ (C := C) (β := β) (k := k - 1) (by omega) (by rw [Nat.sub_add_cancel h0]; exact hne)
    rw [Nat.sub_add_cancel h0] at this; exact this
  rw [C.sideLeft_tour_inner β hpos (tourA_lt k)]
  unfold Chain.sideTour
  rw [hsucc, Nat.add_sub_cancel, sideIdx_tourA (by omega), ← hsucc, sideIdx_tourA hk,
    sideIdx_tourA_succ hk]

/-- **The left sector inside a side-`A` edge**: the left half-plane of the chain edge. -/
theorem sideLeft_tourA_edge (hP : C.P.Simple) {k : ℕ} (hk : k < C.m) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (x : Point) :
    sideLeft (C.sideWalk β) (tourA C β k + 6) s x ↔
      0 < Chazelle.det (C.vertex k) (C.vertex (k + 1)) x := by
  have hne : (C.sideWalk β).vtx (tourA C β k + 6) ≠
      (C.sideWalk β).vtx ((tourA C β k + 6 + 1) % (C.sideWalk β).n) := by
    rw [vtx_tourA hk, vtx_tourA_succ hk]; exact C.sideVertex_succ_ne hP k
  rw [Chazelle.Chain.sideLeft_edge hne hs, vtx_tourA hk, vtx_tourA_succ hk]

/-- The side-`A` walk edges are counted. -/
theorem counted_tourA (k : ℕ) : (chainModel C).counted (tourA C β k + 6) := by
  have := tourA_lt (C := C) (β := β) k
  show 6 ≤ tourA C β k + 6 ∧ tourA C β k + 6 < 2 * C.m + 6
  omega

end

end TourA

end Chazelle.Core
