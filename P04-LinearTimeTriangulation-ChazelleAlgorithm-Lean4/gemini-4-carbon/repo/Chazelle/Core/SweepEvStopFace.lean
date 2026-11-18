module

public import Chazelle.Core.SweepEvFace
public import Chazelle.Core.ShootCutBox

/-!
# The sweep (WP-D), stage 2: the regions faced at a position of the walk of `C₂` (task F, math)

For a proper position `x = (e, h)` of a chain model (key `e + t`, `t` the parameter) that is a
walk vertex or not a cut, and the spine answer `j` of double identification (`locJ`):

* `frc_after`, `frc_before`: a non-cut position faces the region of the arc at `j` just after
  and just before it (any parameter);
* `frc_box_noncut`: a walk vertex on the box (`e < 6`) is never a cut (box corners and the top of
  the slit are outside the height band of the chords);
* at a walk vertex of the tour, `face_after_eq` … `face_before_ne` (`SweepEvFace`).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideInArc)
open OracleQ (sj sk ek succP predP)

namespace Sweep

section FaceR

variable {M : Model} {Q : Polygon} {N : NF}

/-- **A non-cut position faces the region of the arc at `j` just after it.** -/
theorem frc_after (hN : IsNF M Q N) {j : ℕ} (hj : j < N.arcs.length) {e : ℕ} {t : ℝ}
    (he : e < M.W.n) (ht0 : 0 ≤ t) (_ht1 : t < 1)
    (hl1 : N.F M Q = ∅ ∨ sideInArc (sk M Q N j) (ek M Q N j) ((e : ℝ) + t)) :
    AfterFaces M e t (regOf M Q N (N.arc (sj N j)).reg) := by
  obtain ⟨-, harc⟩ := arc_regOf hN hj
  rcases hl1 with hF | hin
  · exact ⟨1, one_pos, fun s hs0 _ hs2 => faces_of_empty harc hF he (by linarith) hs2⟩
  · obtain ⟨δ, hδ, h⟩ := sideInArc_nhds hin
    refine ⟨δ, hδ, fun s hs0 hs1 hs2 => ?_⟩
    refine harc.2.2.2.2.2.2 e (t + s) he (by linarith) hs2 ?_
    rw [← add_assoc]; exact (h s hs0 hs1).2

/-- **A non-cut position faces the region of the arc at `j` just before it.** -/
theorem frc_before (hN : IsNF M Q N) {j : ℕ} (hj : j < N.arcs.length) {e : ℕ} {t : ℝ}
    (he : e < M.W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hl1 : N.F M Q = ∅ ∨ sideInArc (sk M Q N j) (ek M Q N j) ((e : ℝ) + t)) :
    BeforeFaces M e t (regOf M Q N (N.arc (sj N j)).reg) := by
  obtain ⟨-, harc⟩ := arc_regOf hN hj
  rcases ht0.lt_or_eq with htp | rfl
  · rcases hl1 with hF | hin
    · refine ⟨1, one_pos, fun _ s hs0 _ hst => ?_, fun h => absurd h htp.ne'⟩
      exact faces_of_empty harc hF he (by linarith) (by linarith)
    · obtain ⟨δ, hδ, h⟩ := sideInArc_nhds hin
      refine ⟨δ, hδ, fun _ s hs0 hs1 hst => ?_, fun h => absurd h htp.ne'⟩
      refine harc.2.2.2.2.2.2 e (t - s) he (by linarith) (by linarith) ?_
      have : (e : ℝ) + (t - s) = (e : ℝ) + t - s := by ring
      rw [this]; exact (h s hs0 hs1).1
  · rcases hl1 with hF | hin
    · exact beforeFaces_of_empty harc hF he
    · rw [add_zero] at hin
      exact beforeFaces_of_inArc harc he hin

end FaceR

section Box

variable {C : Chain} {P : Polygon} {N : NF}

/-- **A walk vertex on the box is not a cut.** -/
theorem frc_box_noncut (hP : C.P.Simple) (hN : IsNF (chainModel C) (Qof P) N) {e : ℕ}
    (he : e < 6) : ¬ (chainModel C).IsCut (N.F (chainModel C) (Qof P)) (e : ℝ) := by
  intro hc
  have hne : (N.F (chainModel C) (Qof P)).Nonempty := by
    obtain ⟨c, hc', -⟩ := hc; exact ⟨c, hc'⟩
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  obtain ⟨U, hU, b, hab⟩ := (arcCover _ _ _ hGM hN.1).2 _ hc
  obtain ⟨i, hi, his, -⟩ := NFLoc.listed_of_isArc hN hU hab
  obtain ⟨hs, -⟩ := Restore.arc_abs_lt hP hN hne hi
  obtain ⟨pps, -⟩ := (regOf_spec hN).2.2.2.2.2.2 _ hi
  obtain ⟨hedge, -⟩ := (key_eq_nat_iff pps e).1 his
  have hpar : (chainModel C).param (Qof P) (N.arc i).s = 0 := by
    have hk : (chainModel C).key (Qof P) (N.arc i).s =
        (N.arc i).s.edge + (chainModel C).param (Qof P) (N.arc i).s := rfl
    rw [his, hedge] at hk; linarith
  have hv : (chainModel C).pos (Qof P) (N.arc i).s = (chainModel C).W.vtx e := by
    show sidePt (chainModel C).W (N.arc i).s.edge ((chainModel C).param (Qof P) (N.arc i).s) = _
    rw [hpar, hedge, Chazelle.Chain.sidePt_zero]
  rw [hv] at hs
  have hr := C.radius_pos
  rcases ShootCut.walk_vtx_box (C := C) (q := e) (by omega) with h | h <;> rw [h] at hs
  · rw [abs_of_pos hr] at hs; exact lt_irrefl _ hs
  · rw [abs_neg, abs_of_pos hr] at hs; exact lt_irrefl _ hs

end Box

end Sweep

end

end Chazelle.Core
