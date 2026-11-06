import RequestProject.GenusBoundaryCoordinates
import RequestProject.Tac


/-! Distinguished first-edge detection for the actual geometric marking loops. -/
bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb Cell
variable (q : ℕ) [NeZero q]

abbrev MarkingSurfaceCell := SCell (gvc q) (gec q) (gc q)
abbrev MarkingSurfaceEdge := (orderCx (NeSpx (cmpRel (MarkingSurfaceCell q)))).E

def markingBaseCell : MarkingSurfaceCell q := .vtx none
def markingMidCell (i : Fin q × Bool) : MarkingSurfaceCell q := .vtx (some i)
def markingBedCell (i : Fin q × Bool) (b : Bool) : MarkingSurfaceCell q :=
  .bed (i.1, i.2, b)

theorem markingBaseLe i b :
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

theorem markingMidLe i b :
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

def markingBaseFlag (i : Fin q × Bool) (b : Bool) : MarkingSurfaceEdge q :=
  ⟨(spx1 (markingBaseCell q), spx2 (markingBaseLe q i b)),
    spx1_le_spx2_left (markingBaseLe q i b)⟩

def markingBedBaseFlag (i : Fin q × Bool) (b : Bool) : MarkingSurfaceEdge q :=
  ⟨(spx1 (markingBedCell q i b), spx2 (markingBaseLe q i b)),
    by tauto⟩

def markingMidFlag (i : Fin q × Bool) (b : Bool) : MarkingSurfaceEdge q :=
  ⟨(spx1 (markingMidCell q i), spx2 (markingMidLe q i b)),
    spx1_le_spx2_left (markingMidLe q i b)⟩

def markingBedMidFlag (i : Fin q × Bool) (b : Bool) : MarkingSurfaceEdge q :=
  ⟨(spx1 (markingBedCell q i b), spx2 (markingMidLe q i b)),
    by tauto⟩

/-- The edge detecting the marking `i`, traversed positively at its start. -/
def markingFirstEdge (i : Fin q × Bool) := markingBaseFlag q i false

def markingTail (i : Fin q × Bool) :=
  [(markingBedBaseFlag q i false, false),
    (markingBedMidFlag q i false, true),
    (markingMidFlag q i false, false),
    (markingMidFlag q i true, true),
    (markingBedMidFlag q i true, false),
    (markingBedBaseFlag q i true, true),
    (markingBaseFlag q i true, false)]

/-- This is an equality of the original geometric paths, before passing to
path chains or projecting any cover sheets. -/
theorem gSig_first_edge i :
    gSig q (i.1.val, i.2) = (markingFirstEdge q i, true) :: markingTail q i := by
  rw [gSig_boundary_path]
  simp only [bdEdge, edgeHop, edgeHopRev, hop, List.cons_append, List.nil_append,
    ordPos, ordNeg, markedBoundaryPos_succ, cV, cE,
    gvc_markedBoundaryPos_false, gvc_markedBoundaryPos_true,
    gvc_markedBoundaryPos_end, gec_markedBoundaryPos]
  rfl

theorem markingBaseFlag_eq_iff i j b c :
    markingBaseFlag q i b = markingBaseFlag q j c ↔ i = j ∧ b = c := by
  constructor
  · intro h
    have ht := congrArg (·.1.2.1) h
    change ({markingBaseCell q, markingBedCell q i b}) =
      {markingBaseCell q, markingBedCell q j c} at ht
    have hm : markingBedCell q i b ∈
        ({markingBaseCell q, markingBedCell q j c} : Finset (MarkingSurfaceCell q)) := by
      grind
    simp [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · cases hm
    · have he := Cell.bed.inj hm
      grind
  simp_all

theorem markingFirstEdge_injective : Function.Injective (markingFirstEdge q) := by
  intro i j h
  exact ((markingBaseFlag_eq_iff q i j false false).mp h).1

theorem markingFirstEdge_ne_base_true i j :
    markingFirstEdge q i ≠ markingBaseFlag q j true := by
  intro h
  have hf := ((markingBaseFlag_eq_iff q i j false true).mp h).2
  cases hf

theorem markingFirstEdge_ne_mid i j b :
    markingFirstEdge q i ≠ markingMidFlag q j b := by
  intro h
  have hs := congrArg (·.1.1.1) h
  have he := Finset.singleton_inj.mp hs
  cases he

theorem markingFirstEdge_ne_bed_base i j b :
    markingFirstEdge q i ≠ markingBedBaseFlag q j b := by
  intro h
  have hs := congrArg (·.1.1.1) h
  have he := Finset.singleton_inj.mp hs
  cases he

theorem markingFirstEdge_ne_bed_mid i j b :
    markingFirstEdge q i ≠ markingBedMidFlag q j b := by
  intro h
  have hs := congrArg (·.1.1.1) h
  have he := Finset.singleton_inj.mp hs
  cases he

/-- No marking's tail uses any distinguished edge, in either orientation. -/
theorem markingTail_avoids_firstEdge i j
    a (ha : a ∈ markingTail q j) :
    a.1 ≠ markingFirstEdge q i := by
  simp [markingTail, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (markingFirstEdge_ne_bed_base q i j false).symm
  · exact (markingFirstEdge_ne_bed_mid q i j false).symm
  · exact (markingFirstEdge_ne_mid q i j false).symm
  · exact (markingFirstEdge_ne_mid q i j true).symm
  · exact (markingFirstEdge_ne_bed_mid q i j true).symm
  · exact (markingFirstEdge_ne_bed_base q i j true).symm
  · exact (markingFirstEdge_ne_base_true q i j).symm
