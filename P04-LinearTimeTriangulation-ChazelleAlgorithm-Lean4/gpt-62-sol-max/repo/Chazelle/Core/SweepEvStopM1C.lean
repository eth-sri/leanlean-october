module

public import Chazelle.Core.SweepEvStopTasks3
public import Chazelle.Core.SweepEvStopBrute2
public import Chazelle.Core.SweepIoCand1G

/-!
# The sweep (WP-D), stage 2: the candidate of `C₁` of a stop origin, mathematics

* `m1c_wall`: a wall code (`kind = 1`): the origin's position `(oPE, oPH)` of the walk of `C₂` is
  on a vertical side of the box; in the walk of `C₁` the same position (box twin) is the origin,
  with the ray in its left sector;
* `m1c_noarr`: without an arrival position in the walk of `C₁`, the direction is not free for `C₁`
  (shared code).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {J : Merge.Junction} {P : Polygon} {N : NF}

/-- **A wall code** in the walk of `C₁`: the box twin of the origin's position. -/
theorem m1c_wall (hP : J.P.Simple) (hN : IsNF J.rightModel (Qof P) N) {k b e h : ℕ}
    (hok : StOK P J N 1 k b) (hpos : OrgPos P J N 1 k b e h) :
    (e = 1 ∨ e = 3) ∧ e < J.leftModel.W.n ∧
      ProperPos J.leftModel (Qof P) P.n ⟨e, h⟩ ∧
      J.leftModel.pos (Qof P) ⟨e, h⟩ = stOrig J (Qof P) N 1 k b ∧
      |(stOrig J (Qof P) N 1 k b).2| < J.left.radius ∧
      |(stOrig J (Qof P) N 1 k b).1| = J.left.radius ∧
      sideLeft J.leftModel.W e (J.leftModel.param (Qof P) ⟨e, h⟩)
        (rayPt (stOrig J (Qof P) N 1 k b) (dirOf b) 1) := by
  have hok' := hok
  obtain ⟨-, hb, hw, -⟩ := hok
  obtain ⟨hk, hlt⟩ := hw rfl
  obtain ⟨he, hpp, hcl, hz, -, hend⟩ := hpos
  have hx := hend rfl
  have he6 : e < 6 := by have := congrArg WPos.edge hx; simp only at this; rwa [this]
  have hbox : e = 1 ∨ e = 3 := by
    rcases hcl with h' | h' | h'
    · exact h'
    · simp only at h'; omega
    simp_all
  obtain ⟨-, -, hy, -, hx1⟩ := stOrig_facts hP hN hok'
  obtain ⟨ha, hbw, hpar, hposT⟩ :=
    boxTwin_pos (C₁ := J.right) (C₂ := J.left) rfl hbox (Qof P) h
  have hR := J.whole.radius_pos
  -- the ray in the left sector in the walk of `C₂`
  have hA := endPos_attach hN hk (1 - b)
  rw [← hx] at hA
  obtain ⟨y, a', b', hab, hset, hl, hr, -⟩ := rec_ends hN hk
  have hpt : sidePt J.rightModel.W e (J.rightModel.param (Qof P) ⟨e, h⟩) =
      J.rightModel.pos (Qof P) ⟨e, h⟩ := rfl
  have hin : ∀ s, 0 < s → s < b' - a' →
      rayPt (sidePt J.rightModel.W e (J.rightModel.param (Qof P) ⟨e, h⟩))
        (dirOf b) s ∈ (N.chord k).toSet J.rightModel (Qof P) := by
    intro s hs0 hs1
    rw [hpt, hx, hset]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl
    · have e1 : endPos N k (1 - 0) = (N.chord k).rpos := by unfold endPos; simp
      rw [e1, hr, dirOf_zero]
      simp only [Visibility.hseg, rayPt, mem_ofPred_eq]
      refine ⟨trivial, by linarith, by linarith⟩
    · have e1 : endPos N k (1 - 1) = (N.chord k).lpos := by unfold endPos; simp
      rw [e1, hl, dirOf_one]
      simp only [Visibility.hseg, rayPt, mem_ofPred_eq]
      refine ⟨trivial, by linarith, by linarith⟩
  have hsl₂ := SweepStop.sideLeft_of_attach hA (SweepStop.dirOf_cases' b) (ε := b' - a') (by linarith) hin
  rw [hpt, hz] at hsl₂
  -- the parameter is positive
  have ht : J.rightModel.param (Qof P) ⟨e, h⟩ ≠ 0 := by
    intro h0
    have e0 : J.rightModel.pos (Qof P) ⟨e, h⟩ = J.rightModel.wa e := by
      unfold Model.pos; rw [h0]; simp [Geometry.lerp]
    rw [hz] at e0
    rw [e0] at hy
    have hW : J.rightModel.W = J.right.sideWalk J.right.sideBeta := rfl
    unfold Model.wa at hy
    rw [hW] at hy
    rcases hbox with h' | h' <;> rw [h'] at hy
    · rw [J.right.sideWalk_vtx_one] at hy; simp [show J.right.radius = J.whole.radius from rfl, abs_of_pos hR] at hy
    · rw [J.right.sideWalk_vtx_three] at hy; simp [show J.right.radius = J.whole.radius from rfl, abs_of_pos hR] at hy
  refine ⟨hbox, by rw [cm_n]; rcases hbox with h' | h' <;> omega,
    by unfold ProperPos; rwa [← hpar], by rw [← hposT, hz], hy, hx1 rfl, ?_⟩
  rw [← hpar]
  exact (sideLeft_congr ht ha hbw _).1 hsl₂

end

end SweepEv

end Chazelle.Core
