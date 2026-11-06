import Mathlib.Tactic

import RequestProject.GenusSpineCells
import RequestProject.GenusLoops

/-! Canonical surface-generator paths in the actual surviving finite spine. -/

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

def spineCutSingleton (x : GenusVertex q)  :=
  genusSpineCutCell q (spx1 x) (by simp )

variable {x y : GenusVertex q}
def spineCutPair  (h : x ≤ y)  :=
  genusSpineCutCell q (spx2 h) (by
    grind [FiniteChains.Davis.spx2_val])

theorem spineCutSingleton_le_pair_left  (h : x ≤ y) :
    spineCutSingleton q x ≤ spineCutPair q h := spx1_le_spx2_left h

theorem spineCutSingleton_le_pair_right  (h : x ≤ y) :
    spineCutSingleton q y ≤ spineCutPair q h := spx1_le_spx2_right h

/-- Cross the surviving cut edge, normalizing away any degenerate germs. -/
noncomputable def spineEdgeHop  (h : x ≤ y)  :=
  normalizeOrdPath [ordPos (spineCutSingleton_le_pair_left q h),
    ordNeg (spineCutSingleton_le_pair_right q h)]

theorem isPath_spineEdgeHop  (h : x ≤ y) :
    IsPath (genusSpineCx q).src (genusSpineCx q).tgt (spineEdgeHop q h)
      (spineCutSingleton q x) (spineCutSingleton q y) := by
  apply normalizeOrdPath_isPath
  exact ⟨rfl, rfl, rfl⟩

/-- The actual spine crossing reads the same marked path in the older block model. -/
theorem spineEdgeHop_toOld_htpy  (h : x ≤ y) :
    Htpy (orderCx (QOld (cmpRel (GenusVertex q)))) (posQCube (spx1 x)) (posQCube (spx1 y))
      (mapPath (genusSpineToOld q) (spineEdgeHop q h))
      (mapPath (surfCx (cmpRel (GenusVertex q))) (edgeHop h)) := by
  let p  :=
    [ordPos (spineCutSingleton_le_pair_left q h), ordNeg (spineCutSingleton_le_pair_right q h)]
  have hp : IsPath (orderCx (GenusSpineCell q)).src (orderCx (GenusSpineCell q)).tgt p
      (spineCutSingleton q x) (spineCutSingleton q y) := ⟨rfl, rfl, rfl⟩
  let g := orderCxMap (genusSpineCellToOld q) (genusSpineCellToOld_monotone q)
  have hh := mapPath_htpy g (normalizeOrdPath_htpy hp)
  convert hh using 1 <;> simp [p, g, genusSpineToOld, spineEdgeHop, mapPath, Hom.comp,
    spineCutSingleton, spineCutPair, genusSpineCellToOld, genusSpineCutCell,
    truncatedCellRetraction, surfCx, edgeHop, hop, orderCxMap, spx1, spx2, Function.comp_def, ordPos, ordNeg]

variable (p : Fin (8 * q))
/-- A polygon boundary edge, in the genuine simplicial spine. -/
noncomputable def spineBdEdge   :=
  spineEdgeHop q (cV_le_cE (gc q) p) ++
    revPath (spineEdgeHop q (cV1_le_cE (gc q) p))

theorem isPath_spineBdEdge  :
    IsPath (genusSpineCx q).src (genusSpineCx q).tgt (spineBdEdge q p)
      (spineCutSingleton q (cV (gc q) p)) (spineCutSingleton q (cV (gc q) (p + 1))) :=
  (isPath_spineEdgeHop q _).append (isPath_revPath (isPath_spineEdgeHop q _))

theorem marking_mapPath_rev {X Y : Complex2} (f : Hom X Y)
    (p : List (X.E × Bool)) : mapPath f (revPath p) = revPath (mapPath f p) := by simp_all [mapPath, revPath, revGerm]

theorem spineBdEdge_toOld_htpy  :
    Htpy (orderCx (QOld (cmpRel (GenusVertex q))))
      (posQCube (spx1 (cV (gc q) p))) (posQCube (spx1 (cV (gc q) (p + 1))))
      (mapPath (genusSpineToOld q) (spineBdEdge q p))
      (mapPath (surfCx (cmpRel (GenusVertex q))) (bdEdge (gc q) p)) := by
  have h1 := spineEdgeHop_toOld_htpy q (cV_le_cE (gc q) p)
  have h2 := spineEdgeHop_toOld_htpy q (cV1_le_cE (gc q) p)
  have hp1 := h1.symm.isPath (isPath_mapPath (surfCx _) (isPath_edgeHop (cV_le_cE (gc q) p)))
  have hp2 := h2.symm.isPath (isPath_mapPath (surfCx _) (isPath_edgeHop (cV1_le_cE (gc q) p)))
  have hh := Htpy.append_congr hp1 (isPath_revPath hp2) h1 (htpy_revPath hp2 h2)
  simpa [spineBdEdge, bdEdge, mapPath_append, ← revPath_edgeHop, marking_mapPath_rev] using hh

noncomputable def spineSidePath (m : ℕ)  :=
  spineBdEdge q (cyc (8 * q) m) ++ spineBdEdge q (cyc (8 * q) (m + 1))

theorem spineSidePath_toOld_htpy (m : ℕ) :
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
    rw [← cyc_succ] at hp
    exact hp)
  have hp2 := h2.symm.isPath (by
    have hp := isPath_mapPath (surfCx _) (isPath_bdEdge (gc q) (cyc (8 * q) (m + 1)))
    rw [← cyc_succ] at hp
    exact hp)
  simpa [spineSidePath, gPath, pPath, mapPath_append] using
    Htpy.append_congr hp1 hp2 h1 h2

def spineBase : (genusSpineCx q).V :=
  spineCutSingleton q (cV (gc q) (cyc (8 * q) 0))

theorem isPath_spineSidePath {m : ℕ} (hm : m % 2 = 0) :
    IsPath (genusSpineCx q).src (genusSpineCx q).tgt (spineSidePath q m)
      (spineBase q) (spineBase q) := by
  have h1 := isPath_spineBdEdge q (cyc (8 * q) m)
  rw [← cyc_succ] at h1
  have h2 := isPath_spineBdEdge q (cyc (8 * q) (m + 1))
  rw [← cyc_succ] at h2
  have h3 := h1.append h2
  rw [cV_even q hm, cV_even q (k := m + 1 + 1) (by omega)] at h3
  exact h3

variable (x : Fin q × Bool)
/-- The canonical `2q` marked loops, constructed on surviving cells. -/
noncomputable def spineMarkedLoop  : Loop (genusSpineCx q) (spineBase q) :=
  ⟨spineSidePath q (8 * x.1.val + if x.2 then 2 else 0),
    isPath_spineSidePath q (by cases x.2 <;> dsimp <;> omega)⟩

theorem spineMarkedLoop_toOld_htpy  :
    Htpy (orderCx (QOld (cmpRel (GenusVertex q)))) (posQCube (gBase q)) (posQCube (gBase q))
      (mapPath (genusSpineToOld q) (spineMarkedLoop q x).1)
      (mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (x.1.val, x.2))) := by
  let m := 8 * x.1.val + if x.2 then 2 else 0
  have hm : m % 2 = 0 := gIdx_even (x.1.val, x.2)
  have hh := spineSidePath_toOld_htpy q m
  rw [cV_even q hm, cV_even q (k := m + 1 + 1) (by omega)] at hh
  simpa [spineMarkedLoop, gSig, Nat.mod_eq_of_lt x.1.isLt, gBase, m] using hh

/-- The actual spine marking maps to precisely the previously verified block marking. -/
theorem spineMarkedLoop_toOld_class  :
    pi1Map (genusSpineToOld q) (spineBase q) (Pi1.mk (spineMarkedLoop q x)) =
      Pi1.mk ⟨mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (x.1.val, x.2)),
        isPath_mapPath (surfCx _) (isPath_gSig q (x.1.val, x.2))⟩ := Quotient.sound (spineMarkedLoop_toOld_htpy q x)

end FiniteChains.Davis.Genus
