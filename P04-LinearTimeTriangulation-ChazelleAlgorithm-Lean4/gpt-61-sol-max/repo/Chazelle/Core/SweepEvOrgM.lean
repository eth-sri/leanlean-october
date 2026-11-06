module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvMap3
public import Chazelle.Core.SweepIoLocal

/-!
# The sweep (WP-D), stages 2–3: the ends of the chords of `N₂` (mathematics)

The detection origins of stage 3 and the wall ends of stage 2 are the ends of the chords of the
normal form `N₂` (`endOrigin`), read at the walk positions `lpos`, `rpos` of the chord records.

* `endPos`, `endOrigin_eq`: the end `j % 2` of chord `j / 2` is the point of its record position;
* `pos_mem_set_iff`, `pos_vertex`, `pos_ne_vertex`: a (normalised) position of a chain model lies
  on the chain iff it is a tour position (or the last copy of the top); at height code `0` it is
  the vertex `sideIdx (e - 6)`; inside a tour edge it is no vertex.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sidePt)
open WalkEmbed

namespace Sweep

section Ends

section
variable (N : NF) (k s : ℕ)
include N k s
/-- The walk position of the end `s` of chord `k` (the left end for `s = 0`). -/
def endPos : WPos := if s = 0 then (N.chord k).lpos else (N.chord k).rpos

/-- The far end of the end `s` of chord `k`. -/
def farEnd : WPos := if s = 0 then (N.chord k).rpos else (N.chord k).lpos


end

/-- **The ends of a chord record are the ends of its chord.** -/
theorem rec_ends {C : Chain} {Q : Polygon} {N : NF} (hN : IsNF (chainModel C) Q N) {k : ℕ}
    (hk : k < N.nChords) :
    ∃ y a b : ℝ, a < b ∧ (N.chord k).toSet (chainModel C) Q = Visibility.hseg y a b ∧
      (chainModel C).pos Q (N.chord k).lpos = (a, y) ∧ (chainModel C).pos Q (N.chord k).rpos = (b, y) ∧
      (Q.vtx (N.chord k).h).2 = y := by
  have hmem : (N.chord k).toSet (chainModel C) Q ∈ N.F (chainModel C) Q := by
    refine ⟨N.chord k, ?_, rfl⟩
    unfold NF.chord
    rw [NFLoc.getD_of_lt _ hk]
    grind
  obtain ⟨y, a, b, hH, -, heq, -, -⟩ := Merge.augChords_spec (show _ ∈ Merge.augChords C from hN.1.2.1 hmem)
  obtain ⟨h1, h2, h3⟩ := rec_pos_ends (hN.2.2.1 k hk) heq hH.lt
  ram_grind

section
variable (J : Merge.Junction) {Q : Polygon} {N : NF} (hN : IsNF (chainModel J.right) Q N) {j : ℕ} (hj : j < 2 * N.nChords)
include hN hj
theorem endOrigin_eq :
    endOrigin J Q N j = (chainModel J.right).pos Q (endPos N (j / 2) (j % 2)) ∧
      (endDir j = 1 ↔ j % 2 = 0) := by
  obtain ⟨y, a, b, hab, heq, hl, hr, -⟩ := rec_ends hN (show j / 2 < N.nChords by omega)
  unfold endOrigin endDir endPos
  rw [heq]
  by_cases h : j % 2 = 0
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, Merge.lend_hseg hab.le, hl]; simp_all
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, Merge.rend_hseg hab.le, hr]
    ram_grind

/-- The far end of an end is the other end of the chord. -/
theorem farOrigin_eq :
    (if j % 2 = 0 then Merge.rend ((N.chord (j / 2)).toSet (chainModel J.right) Q)
      else Merge.lend ((N.chord (j / 2)).toSet (chainModel J.right) Q)) =
      (chainModel J.right).pos Q (farEnd N (j / 2) (j % 2)) := by
  obtain ⟨y, a, b, hab, heq, hl, hr, -⟩ := rec_ends hN (show j / 2 < N.nChords by omega)
  unfold farEnd
  rw [heq]
  by_cases h : j % 2 = 0
  · rw [ite_eq_left h, ite_eq_left h, Merge.rend_hseg hab.le, hr]
  · rw [ite_eq_right h, ite_eq_right h, Merge.lend_hseg hab.le, hl]


end

end Ends

section Classify

variable (C : Chain)

/-- **A position of a chain model lies on the chain** iff it is a tour position, or the last copy of
the top (normalised height code `0`). -/
theorem pos_mem_set_iff (_hP : C.P.Simple) {Q : Polygon} {x : WPos}
    (hx : x.edge < (chainModel C).W.n) (h0 : 0 ≤ (chainModel C).param Q x)
    (h1 : (chainModel C).param Q x < 1) (hnorm : x.hgt = 0 ↔ (chainModel C).param Q x = 0) :
    (chainModel C).pos Q x ∈ C.set ↔
      (6 ≤ x.edge ∧ x.edge ≤ 2 * C.m + 5) ∨ (x.edge = 2 * C.m + 6 ∧ x.hgt = 0) := by
  have hn := cm_n C
  show sidePt (chainModel C).W x.edge ((chainModel C).param Q x) ∈ C.set ↔ _
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  rw [hW] at hx ⊢
  constructor
  · intro hm
    rcases C.sideWalk_pos_cases C.sideBeta hx h0 with hb | ⟨i, hi, he, hit⟩
    · exact absurd hm (C.sideWalk_box_pt C.sideBeta hb h0 h1).1
    ram_grind
  · rintro (⟨h6, h5⟩ | ⟨he, h0'⟩)
    · have := C.sideWalk_tour_pt_mem C.sideBeta (i := x.edge - 6) (t := (chainModel C).param Q x)
        (by omega) (fun h => absurd h (by omega)) h0 h1
      simp_all
    · have := C.sideWalk_tour_pt_mem C.sideBeta (i := 2 * C.m) (t := (chainModel C).param Q x)
        le_rfl (fun _ => hnorm.1 h0') h0 h1
      simp_all

/-- **A tour vertex**: at height code `0` the position `e` is the vertex `sideIdx (e - 6)`. -/
theorem pos_vertex {Q : Polygon} {x : WPos} (h6 : 6 ≤ x.edge) (he : x.edge ≤ 2 * C.m + 6)
    (h0 : x.hgt = 0) :
    (chainModel C).pos Q x = C.vertex (C.sideIdx C.sideBeta (x.edge - 6)) := by
  obtain ⟨e, hgt⟩ := x
  simp only at h6 he h0
  subst h0
  show sidePt (chainModel C).W e ((chainModel C).param Q ⟨e, 0⟩) = _
  rw [show (chainModel C).param Q ⟨e, 0⟩ = 0 from rfl, Chazelle.Chain.sidePt_zero, cm_W,
    show e = (e - 6) + 6 by omega, C.sideWalk_vtx_tour _ (by omega)]
  aesop

/-- **Inside a tour edge** no position is a vertex of the chain. -/
theorem pos_ne_vertex (hP : C.P.Simple) {Q : Polygon} {x : WPos} (h6 : 6 ≤ x.edge)
    (he : x.edge ≤ 2 * C.m + 5) (h0 : 0 < (chainModel C).param Q x)
    (h1 : (chainModel C).param Q x < 1) (k : ℕ) : (chainModel C).pos Q x ≠ C.vertex k := by
  obtain ⟨e, hgt⟩ := x
  simp only at h6 he
  show sidePt (chainModel C).W e ((chainModel C).param Q ⟨e, hgt⟩) ≠ _
  rw [cm_W]
  obtain ⟨k', -, s, hs, hpt, -⟩ := C.sideTour_open C.sideBeta (i := e - 6) (by omega)
    (t := (chainModel C).param Q ⟨e, hgt⟩) ⟨h0, h1⟩
  rw [show e - 6 + 6 = e by omega] at hpt
  rw [hpt]
  exact C.sideOpen_ne_vertex hP hs

end Classify

end Sweep

end

end Chazelle.Core
