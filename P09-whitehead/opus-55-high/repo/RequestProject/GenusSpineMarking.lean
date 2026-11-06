import RequestProject.GenusSpineCells
import RequestProject.GenusLoops
import RequestProject.Tac
noncomputable section


/-! Canonical surface-generator paths in the actual surviving finite spine. -/

bwd

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def spineCutSingleton (x : GenusVertex q) :=
  genusSpineCutCell q (spx1 x) (by simp)

def spineCutPair {x y : GenusVertex q} (h : x ≤ y) :=
  genusSpineCutCell q (spx2 h) (by
    simpa using Finset.card_insert_le x ({y} : Finset (GenusVertex q)))

theorem spineCutSingleton_le_pair_left (h : x ≤ y) :
    spineCutSingleton q x ≤ spineCutPair q h := spx1_le_spx2_left h

theorem spineCutSingleton_le_pair_right (h : x ≤ y) :
    spineCutSingleton q y ≤ spineCutPair q h := spx1_le_spx2_right h

/-- Cross the surviving cut edge, normalizing away any degenerate germs. -/
def spineEdgeHop {x y : GenusVertex q} (h : x ≤ y) :
    List ((genusSpineCx q).E × Bool) :=
  normalizeOrdPath [ordPos (spineCutSingleton_le_pair_left q h),
    ordNeg (spineCutSingleton_le_pair_right q h)]

theorem isPath_spineEdgeHop (h : x ≤ y) :
    IsPathX (genusSpineCx q) (spineEdgeHop q h)
      (spineCutSingleton q x) (spineCutSingleton q y) := by
  apply normalizeOrdPath_isPath
  tauto

/-- The actual spine crossing reads the same marked path in the older block model. -/
theorem spineEdgeHop_toOld_htpy (h : x ≤ y) :
    Htpy (orderCx (QOld (cmpRel (GenusVertex q)))) (posQCube (spx1 x)) (posQCube (spx1 y))
      (mapPath (genusSpineToOld q) (spineEdgeHop q h))
      (mapPath (surfCx (cmpRel (GenusVertex q))) (edgeHop h)) := by
  let p :=
    [ordPos (spineCutSingleton_le_pair_left q h), ordNeg (spineCutSingleton_le_pair_right q h)]
  have hp : IsPathX (orderCx (GenusSpineCell q)) p
      (spineCutSingleton q x) (spineCutSingleton q y) := by tauto
  let g := orderCxMap _ (genusSpineCellToOld_monotone q)
  have hh := mapPath_htpy g (normalizeOrdPath_htpy hp)
  convert hh using 1 <;> simp [p, g, genusSpineToOld, spineEdgeHop, mapPath, Hom.comp,
    spineCutSingleton, spineCutPair, genusSpineCellToOld, genusSpineCutCell,
    truncatedCellRetraction, surfCx, edgeHop, hop, orderCxMap, spx1, spx2, Function.comp_def, ordPos, ordNeg]

/-- A polygon boundary edge, in the genuine simplicial spine. -/
def spineBdEdge (p : Fin (8 * q)) :=
  spineEdgeHop q (cV_le_cE _ p) ++
    revPath (spineEdgeHop q (cV1_le_cE _ p))

theorem isPath_spineBdEdge p :
    IsPathX (genusSpineCx q) (spineBdEdge q p)
      (spineCutSingleton q (cV (gc q) p)) (spineCutSingleton q (cV (gc q) (p + 1))) :=
  (isPath_spineEdgeHop q _).append (isPath_revPath (isPath_spineEdgeHop q _))

theorem marking_mapPath_rev (f : Hom X Y)
    p : mapPath f (revPath p) = revPath (mapPath f p) := by
  simp [mapPath, revPath, revGerm, List.map_map, Function.comp_def, List.map_reverse]

theorem spineBdEdge_toOld_htpy p :
    Htpy (orderCx (QOld (cmpRel (GenusVertex q))))
      (posQCube (spx1 (cV (gc q) p))) (posQCube (spx1 (cV (gc q) (p + 1))))
      (mapPath (genusSpineToOld q) (spineBdEdge q p))
      (mapPath (surfCx (cmpRel (GenusVertex q))) (bdEdge (gc q) p)) := by
  have h1 := spineEdgeHop_toOld_htpy q (cV_le_cE (gc q) p)
  have h2 := spineEdgeHop_toOld_htpy q (cV1_le_cE (gc q) p)
  have hp1 := h1.symm.isPath (by tauto)
  have hp2 := h2.symm.isPath (by tauto)
  have hh := Htpy.append_congr hp1 (isPath_revPath hp2) h1 (htpy_revPath hp2 h2)
  simp_all [spineBdEdge, bdEdge, mapPath_append, ← revPath_edgeHop, marking_mapPath_rev]

def spineSidePath (m : ℕ) :=
  spineBdEdge q (cyc _ m) ++ spineBdEdge q (cyc _ (m + 1))

theorem spineSidePath_toOld_htpy m :
    Htpy (orderCx (QOld (cmpRel (GenusVertex q))))
      (posQCube (spx1 (cV (gc q) (cyc (8 * q) m))))
      (posQCube (spx1 (cV (gc q) (cyc (8 * q) (m + 1 + 1)))))
      (mapPath (genusSpineToOld q) (spineSidePath q m))
      (mapPath (surfCx (cmpRel (GenusVertex q))) (gPath q m)) := by
  have h1 := spineBdEdge_toOld_htpy q (cyc (8 * q) m)
  have h2 := spineBdEdge_toOld_htpy q (cyc (8 * q) (m + 1))
  rw [← cyc_succ] at h1 h2
  have hp1 := h1.symm.isPath (by
    have hp := isPath_mapPath (surfCx _) (isPath_bdEdge (gc q) (cyc (8 * q) m))
    rwa [← cyc_succ] at hp)
  have hp2 := h2.symm.isPath (by
    have hp := isPath_mapPath (surfCx _) (isPath_bdEdge (gc q) (cyc (8 * q) (m + 1)))
    rwa [← cyc_succ] at hp)
  simpa [spineSidePath, gPath, pPath, mapPath_append] using
    Htpy.append_congr hp1 hp2 h1 h2

def spineBase : (genusSpineCx q).V :=
  spineCutSingleton q (cV _ (cyc _ 0))

theorem isPath_spineSidePath (hm : m % 2 = 0) :
    IsPathX (genusSpineCx q) (spineSidePath q m)
      (spineBase q) (spineBase q) := by
  have h1 := isPath_spineBdEdge q (cyc (8 * q) m)
  rw [← cyc_succ] at h1
  have h2 := isPath_spineBdEdge q (cyc (8 * q) (m + 1))
  rw [← cyc_succ] at h2
  have h3 := h1.append h2
  rwa [cV_even q hm, cV_even q (k := m + 1 + 1) (by omega)] at h3

/-- The canonical `2q` marked loops, constructed on surviving cells. -/
def spineMarkedLoop (x : Fin q × Bool) : Loop (genusSpineCx q) (spineBase q) :=
  ⟨spineSidePath q (8 * x.1.val + if x.2 then 2 else 0),
    isPath_spineSidePath q (by grind)⟩

theorem spineMarkedLoop_toOld_htpy x :
    Htpy (orderCx (QOld (cmpRel (GenusVertex q)))) (posQCube (gBase q)) (posQCube (gBase q))
      (mapPath (genusSpineToOld q) (spineMarkedLoop q x).1)
      (mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (x.1.val, x.2))) := by
  let m := 8 * x.1.val + if x.2 then 2 else 0
  have hm : m % 2 = 0 := by grind
  have hh := spineSidePath_toOld_htpy q m
  simp_all [cV_even q hm, cV_even q (k := m + 1 + 1) (by omega), spineMarkedLoop, gSig, Nat.mod_eq_of_lt x.1.isLt, gBase, m]

/-- The actual spine marking maps to precisely the previously verified block marking. -/
theorem spineMarkedLoop_toOld_class x :
    pi1Map (genusSpineToOld q) (spineBase q) (Pi1.mk (spineMarkedLoop q x)) =
      Pi1.mk ⟨mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (x.1.val, x.2)),
        isPath_mapPath (surfCx _) (isPath_gSig q (x.1.val, x.2))⟩ := Quotient.sound (spineMarkedLoop_toOld_htpy q x)
