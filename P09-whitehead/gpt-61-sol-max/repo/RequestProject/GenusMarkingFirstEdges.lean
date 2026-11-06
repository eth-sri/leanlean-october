import Mathlib.Tactic

import RequestProject.GenusBoundaryCoordinates

/-! Distinguished first-edge detection for the actual geometric marking loops. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Cell
variable (q : ℕ) [NeZero q]

abbrev MarkingSurfaceCell := SCell (gvc q) (gec q) (gc q)
abbrev MarkingSurfaceEdge := (orderCx (NeSpx (cmpRel (MarkingSurfaceCell q)))).E

def markingBaseCell : MarkingSurfaceCell q := .vtx none
variable (i : Fin q × Bool)
def markingMidCell  : MarkingSurfaceCell q := .vtx (some i)
variable (b : Bool)
def markingBedCell   : MarkingSurfaceCell q :=
  .bed (i.1, i.2, b)

theorem markingBaseLe   :
    markingBaseCell q ≤ markingBedCell q i b := by
  cases b with
  | false =>
    simpa [cV, cE, gvc_markedBoundaryPos_false, gec_markedBoundaryPos,
      markingBaseCell, markingBedCell, toS] using
      cV_le_cE (gc q) (markedBoundaryPos q i false)
  | true =>
    simpa [cV, cE, gvc_markedBoundaryPos_end, gec_markedBoundaryPos,
      markingBaseCell, markingBedCell, toS] using
      cV1_le_cE (gc q) (markedBoundaryPos q i true)

theorem markingMidLe   :
    markingMidCell q i ≤ markingBedCell q i b := by
  cases b with
  | false =>
    simpa [markedBoundaryPos_succ, cV, cE, gvc_markedBoundaryPos_true,
      gec_markedBoundaryPos, markingMidCell, markingBedCell, toS] using
      cV1_le_cE (gc q) (markedBoundaryPos q i false)
  | true =>
    simpa [cV, cE, gvc_markedBoundaryPos_true, gec_markedBoundaryPos,
      markingMidCell, markingBedCell, toS] using
      cV_le_cE (gc q) (markedBoundaryPos q i true)

def markingBaseFlag   : MarkingSurfaceEdge q :=
  ⟨(spx1 (markingBaseCell q), spx2 (markingBaseLe q i b)),
    spx1_le_spx2_left (markingBaseLe q i b)⟩

def markingBedBaseFlag   : MarkingSurfaceEdge q :=
  ⟨(spx1 (markingBedCell q i b), spx2 (markingBaseLe q i b)),
    spx1_le_spx2_right (markingBaseLe q i b)⟩

def markingMidFlag   : MarkingSurfaceEdge q :=
  ⟨(spx1 (markingMidCell q i), spx2 (markingMidLe q i b)),
    spx1_le_spx2_left (markingMidLe q i b)⟩

def markingBedMidFlag   : MarkingSurfaceEdge q :=
  ⟨(spx1 (markingBedCell q i b), spx2 (markingMidLe q i b)),
    spx1_le_spx2_right (markingMidLe q i b)⟩

/-- The edge detecting the marking `i`, traversed positively at its start. -/
def markingFirstEdge   := markingBaseFlag q i false

def markingTail   :=
  [(markingBedBaseFlag q i false, false),
    (markingBedMidFlag q i false, true),
    (markingMidFlag q i false, false),
    (markingMidFlag q i true, true),
    (markingBedMidFlag q i true, false),
    (markingBedBaseFlag q i true, true),
    (markingBaseFlag q i true, false)]

/-- This is an equality of the original geometric paths, before passing to
path chains or projecting any cover sheets. -/
theorem gSig_first_edge  :
    gSig q (i.1.val, i.2) = (markingFirstEdge q i, true) :: markingTail q i := by
  rw [gSig_boundary_path]
  simp only [bdEdge, markedBoundaryPos_succ, cV, cE, gvc_markedBoundaryPos_false, gvc_markedBoundaryPos_true, gvc_markedBoundaryPos_end, gec_markedBoundaryPos]
  rfl

variable (i j : Fin q × Bool)
theorem markingBaseFlag_eq_iff  (b c : Bool) :
    markingBaseFlag q i b = markingBaseFlag q j c ↔ i = j ∧ b = c := by
  constructor
  · intro h
    have ht := congrArg (fun e : MarkingSurfaceEdge q => e.1.2.1) h
    change ({markingBaseCell q, markingBedCell q i b} : Finset (MarkingSurfaceCell q)) =
      {markingBaseCell q, markingBedCell q j c} at ht
    have hm : markingBedCell q i b ∈
        ({markingBaseCell q, markingBedCell q j c} : Finset (MarkingSurfaceCell q)) := by
      rw [← ht]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · cases hm
    · have he  := Cell.bed.inj hm
      exact ⟨congrArg (fun x : Fin q × Bool × Bool => (x.1, x.2.1)) he,
        congrArg (fun x : Fin q × Bool × Bool => x.2.2) he⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem markingFirstEdge_injective : Function.Injective (markingFirstEdge q) := by
  intro i j h
  exact ((markingBaseFlag_eq_iff q i j false false).mp h).1

theorem markingFirstEdge_ne_base_true  :
    markingFirstEdge q i ≠ markingBaseFlag q j true := by
  intro h
  have hf := ((markingBaseFlag_eq_iff q i j false true).mp h).2
  cases hf

theorem markingFirstEdge_ne_mid  (b : Bool) :
    markingFirstEdge q i ≠ markingMidFlag q j b := by
  intro h
  have hs := congrArg (fun e : MarkingSurfaceEdge q => e.1.1.1) h
  
  have he := Finset.singleton_inj.mp hs
  cases he

theorem markingFirstEdge_ne_bed_base  (b : Bool) :
    markingFirstEdge q i ≠ markingBedBaseFlag q j b := by
  intro h
  have hs := congrArg (fun e : MarkingSurfaceEdge q => e.1.1.1) h
  
  have he := Finset.singleton_inj.mp hs
  cases he

theorem markingFirstEdge_ne_bed_mid  (b : Bool) :
    markingFirstEdge q i ≠ markingBedMidFlag q j b := by
  intro h
  have hs := congrArg (fun e : MarkingSurfaceEdge q => e.1.1.1) h
  
  have he := Finset.singleton_inj.mp hs
  cases he

/-- No marking's tail uses any distinguished edge, in either orientation. -/
theorem markingTail_avoids_firstEdge 
    (a : MarkingSurfaceEdge q × Bool) (ha : a ∈ markingTail q j) :
    a.1 ≠ markingFirstEdge q i := by
  aesop (add simp [markingTail, markingFirstEdge_ne_bed_base, markingFirstEdge_ne_bed_mid, markingFirstEdge_ne_mid, markingFirstEdge_ne_base_true])

end FiniteChains.Davis.Genus
