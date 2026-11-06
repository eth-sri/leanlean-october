module

public import Chazelle.Core.SweepIoConv

/-!
# The sweep RAM (WP-D), answers: the classes of walk positions

Walk positions of a chain model that the answers convert to the model of `C` (`PosClass`): a
vertical side of the box, a tour edge, or the start of the up-slit edge (the top).  Points on the
query ray (strictly inside the height band of the box) of the chain or of the box are of this
class (`posClass_of`), and so are the query positions (`query_abs`: a query point lies strictly
inside the height band — the bottom corners of the box have no horizontal direction in their left
sector).  Their points are points of the chain or of a vertical side of the box (`posClass_pt`).
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc sideLeftOf sideCcw sideCross sidePrev sideNext)

@[expose] public section

theorem absy_lt (C : Chain) {p : Point} (hp : p ∈ C.set) : |p.2| < C.radius :=
  lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set hp).2 C.coordBound_lt_radius

/-- **The positions converted to the model of `C`.** -/
def PosClass (C : Chain) (Q : Polygon) (x : WPos) : Prop :=
  (x.edge = 1 ∨ x.edge = 3) ∨ (6 ≤ x.edge ∧ x.edge < 2 * C.m + 6) ∨
    (x.edge = 2 * C.m + 6 ∧ (chainModel C).param Q x = 0)

theorem pos_eq_sidePt' (C : Chain) (Q : Polygon) (x : WPos) :
    (chainModel C).pos Q x = sidePt (chainModel C).W x.edge ((chainModel C).param Q x) := rfl

/-- **Points of the chain or of the box on a ray strictly inside the height band** have positions
of the class. -/
theorem posClass_of {C : Chain} {Q : Polygon} {x : WPos} (he : x.edge < (chainModel C).W.n)
    (h0 : 0 ≤ (chainModel C).param Q x) (h1 : (chainModel C).param Q x < 1)
    (hy : |((chainModel C).pos Q x).2| < C.radius)
    (hc : ((chainModel C).pos Q x).2 ≤ C.top.2 ∨ |((chainModel C).pos Q x).1| = C.radius) :
    PosClass C Q x := by
  have hn := cm_n C
  have hR := C.radius_pos
  have htR := C.top_snd_lt_radius
  have htx := C.abs_top_fst_lt_radius
  set t := (chainModel C).param Q x with ht
  rw [pos_eq_sidePt' C Q x, ← ht] at hy hc
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := C.sidePt_box C.sideBeta t
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  rw [hW] at hy hc
  unfold PosClass
  rcases (show x.edge < 6 ∨ (6 ≤ x.edge ∧ x.edge < 2 * C.m + 6) ∨ x.edge = 2 * C.m + 6 by
    omega) with hlt | hmid | hend
  · rcases (show x.edge = 0 ∨ x.edge = 1 ∨ x.edge = 2 ∨ x.edge = 3 ∨ x.edge = 4 ∨ x.edge = 5 by
      omega) with h | h | h | h | h | h
    · rw [h, b0] at hy; simp only at hy; rw [abs_of_pos hR] at hy; exact absurd hy (lt_irrefl _)
    · exact Or.inl (Or.inl h)
    · rw [h, b2] at hy; simp only at hy; rw [abs_neg, abs_of_pos hR] at hy
      exact absurd hy (lt_irrefl _)
    · exact Or.inl (Or.inr h)
    · rw [h, b4] at hy; simp only at hy; rw [abs_of_pos hR] at hy; exact absurd hy (lt_irrefl _)
    · exfalso
      rw [h, b5] at hy hc; simp only at hy hc
      rcases hc with hc | hc
      · nlinarith
      · rw [hc] at htx; exact lt_irrefl _ htx
  · exact Or.inr (Or.inl hmid)
  · refine Or.inr (Or.inr ⟨hend, ?_⟩)
    rw [hend, b6] at hc; simp only at hc
    rcases hc with hc | hc
    · rcases h0.lt_or_eq with h0 | h0
      · nlinarith
      · exact h0.symm
    · rw [hc] at htx; exact absurd htx (lt_irrefl _)

/-- **The points of the class** are points of the chain or of a vertical side of the box. -/
theorem posClass_pt {C : Chain} {Q : Polygon} {x : WPos} (hx : PosClass C Q x)
    (h0 : 0 ≤ (chainModel C).param Q x) (h1 : (chainModel C).param Q x < 1)
    (hy : |((chainModel C).pos Q x).2| < C.radius) :
    (chainModel C).pos Q x ∈ C.set ∨
      (|((chainModel C).pos Q x).1| = C.radius ∧ |((chainModel C).pos Q x).2| < C.radius) := by
  have hR := C.radius_pos
  set t := (chainModel C).param Q x with ht
  rw [pos_eq_sidePt' C Q x, ← ht] at hy ⊢
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := C.sidePt_box C.sideBeta t
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  rw [hW] at hy ⊢
  rcases hx with (h | h) | ⟨h6, hlt⟩ | ⟨hend, hz⟩
  · right; rw [h, b1]; simp only; rw [abs_neg, abs_of_pos hR]
    exact ⟨rfl, by rwa [h, b1] at hy⟩
  · right; rw [h, b3]; simp only; rw [abs_of_pos hR]
    exact ⟨rfl, by rwa [h, b3] at hy⟩
  · left
    have := C.sideWalk_tour_pt_mem C.sideBeta (i := x.edge - 6) (t := t) (by omega)
      (fun h => by omega) h0 h1
    rwa [show x.edge - 6 + 6 = x.edge by omega] at this
  · left
    rw [hend, ht, hz]
    exact C.sideWalk_tour_pt_mem C.sideBeta (i := 2 * C.m) (t := 0) le_rfl (fun _ => rfl) le_rfl
      one_pos

/-- **The bottom corners of the box have no horizontal direction in their left sector.** -/
theorem not_sideLeft_bottom (C : Chain) {σ : ℝ} (_hσ : σ = 1 ∨ σ = -1) {p : ℕ}
    (hp : p = 2 ∨ p = 3) :
    ¬ sideLeft (chainModel C).W p 0 (rayPt (sidePt (chainModel C).W p 0) σ 1) := by
  have hR := C.radius_pos
  have hn := cm_n C
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  unfold sideLeft sideLeftOf sidePrev sideNext sideCcw
  rw [hW, Chazelle.Chain.sidePt_zero, ite_eq_left rfl]
  rw [hW] at hn
  rcases hp with rfl | rfl
  · rw [show (2 + (C.sideWalk C.sideBeta).n - 1) % (C.sideWalk C.sideBeta).n = 1 by
        rw [hn, show 2 + (2 * C.m + 7) - 1 = 1 + (2 * C.m + 7) by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)],
      show (2 + 1) % (C.sideWalk C.sideBeta).n = 3 by rw [hn]; exact Nat.mod_eq_of_lt (by omega),
      C.sideWalk_vtx_one, C.sideWalk_vtx_two, C.sideWalk_vtx_three]
    simp only [sideCross, Chazelle.Chain.sideDot, rayPt, Prod.fst_sub, Prod.snd_sub]
    intro h
    rcases h with ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> nlinarith
  · rw [show (3 + (C.sideWalk C.sideBeta).n - 1) % (C.sideWalk C.sideBeta).n = 2 by
        rw [hn, show 3 + (2 * C.m + 7) - 1 = 2 + (2 * C.m + 7) by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)],
      show (3 + 1) % (C.sideWalk C.sideBeta).n = 4 by rw [hn]; exact Nat.mod_eq_of_lt (by omega),
      C.sideWalk_vtx_two, C.sideWalk_vtx_three, C.sideWalk_vtx_four]
    simp only [sideCross, Chazelle.Chain.sideDot, rayPt, Prod.fst_sub, Prod.snd_sub]
    intro h
    rcases h with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> nlinarith

/-- **A query point lies strictly inside the height band of the box.** -/
theorem query_abs {C : Chain} {Q : Polygon} {x : WPos} (he : x.edge < (chainModel C).W.n)
    (h0 : 0 ≤ (chainModel C).param Q x) (h1 : (chainModel C).param Q x < 1)
    (htop : ((chainModel C).pos Q x).2 ≤ C.top.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hsec : sideLeft (chainModel C).W x.edge ((chainModel C).param Q x)
      (rayPt ((chainModel C).pos Q x) σ 1)) :
    |((chainModel C).pos Q x).2| < C.radius := by
  have hn := cm_n C
  have hR := C.radius_pos
  have htR := C.top_snd_lt_radius
  have htm : |C.top.2| < C.radius := absy_lt C C.top_mem_set
  set t := (chainModel C).param Q x with ht
  rw [pos_eq_sidePt' C Q x, ← ht] at htop hsec ⊢
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := C.sidePt_box C.sideBeta t
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  rcases (show x.edge < 6 ∨ (6 ≤ x.edge ∧ x.edge < 2 * C.m + 6) ∨ x.edge = 2 * C.m + 6 by
    omega) with hlt | hmid | hend
  · rcases (show x.edge = 0 ∨ x.edge = 1 ∨ x.edge = 2 ∨ x.edge = 3 ∨ x.edge = 4 ∨ x.edge = 5 by
      omega) with h | h | h | h | h | h
    · rw [hW, h, b0] at htop; simp only at htop; linarith
    · rw [hW, h, b1]; simp only
      rw [hW, h, b1] at htop; simp only at htop
      rw [abs_lt]; constructor <;> nlinarith
    · exfalso
      have ht0 : t = 0 := by
        rcases h0.lt_or_eq with h0 | h0
        · exfalso
          apply Sweep.not_sideLeft_horizontal h0 h1 (W := (chainModel C).W) (p := 2) _ σ
          · rwa [← h]
          · rw [hW, C.sideWalk_vtx_two, show (2 + 1) % (C.sideWalk C.sideBeta).n = 3 by
              rw [C.sideWalk_n]; exact Nat.mod_eq_of_lt (by omega), C.sideWalk_vtx_three]
        · exact h0.symm
      rw [h, ht0] at hsec
      exact not_sideLeft_bottom C hσ (Or.inl rfl) hsec
    · rcases h0.lt_or_eq with h0' | h0'
      · rw [hW, h, b3]; simp only
        rw [abs_lt]; constructor <;> nlinarith
      · exfalso
        rw [h, ← h0'] at hsec
        exact not_sideLeft_bottom C hσ (Or.inr rfl) hsec
    · rw [hW, h, b4] at htop; simp only at htop; linarith
    · rw [hW, h, b5] at htop; simp only at htop; nlinarith
  · have := C.sideWalk_tour_pt_mem C.sideBeta (i := x.edge - 6) (t := t) (by omega)
      (fun h => by omega) h0 h1
    rw [show x.edge - 6 + 6 = x.edge by omega] at this
    exact absy_lt C (by rw [hW]; exact this)
  · rw [hW, hend, b6] at htop ⊢; simp only at htop ⊢
    have : t * (C.radius - C.top.2) ≤ 0 := by linarith
    have ht0 : t = 0 := by nlinarith
    rwa [ht0, zero_mul, add_zero]

end

end SweepIo

end Chazelle.Core
