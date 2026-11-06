import Mathlib.Tactic

import RequestProject.SurfacePoset

/-!
# The cells of the surface poset, their incidences and the paths of the subdivision

This file names the cells of the poset of `RequestProject/SurfacePoset.lean` inside the poset
itself, records the incidences between them (which faces lie in which cell) and assembles the
edge paths of the barycentric subdivision that are used to fill the polygon:

* `bdEdge p` — the boundary edge at the position `p`, crossed from the vertex at `p` to the
  vertex at `p+1`;
* `delta p` — from the collar vertex at `p` to the boundary vertex at `p`;
* `gam p` — along the collar, from `p` to `p+1`;
* `gg p` — the diagonal, from the boundary vertex at `p` to the collar vertex at `p+1`;
* `alph p` — from the centre to the collar vertex at `p`, and `ray p` from the centre to the
  boundary vertex at `p`.

Each of them is a path of `orderCx (NeSpx (cmpRel (SCell vc ec hc)))`, i.e. of the barycentric
subdivision of the triangulation, and for each of the three families of triangles the
corresponding loop stays inside the star of one triangle.
-/

namespace FiniteChains.Davis


open RACG Mirror Comb Cell


section

variable {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι}

variable (hc : Compat vc ec)
/-- The barycentric subdivision of the triangulation of the surface, as a two-complex: the order
complex of the poset of nonempty chains of cells. -/
abbrev sdCx   :=
  orderCx (NeSpx (cmpRel (SCell vc ec hc)))

/-! ### The cells -/

variable (p : Fin M)
/-- The boundary vertex at the position `p`. -/
def cV    := toS vc ec hc (vtx (vc p))

/-- The boundary edge at the position `p`. -/
def cE    := toS vc ec hc (bed (ec p))

/-- The collar vertex at the position `p`. -/
def cW    := toS vc ec hc (cvx p)

/-- The collar edge at the position `p`. -/
def cF    := toS vc ec hc (ced p)

/-- The edge from the boundary vertex at `p` to the collar vertex at `p`. -/
def cD    := toS vc ec hc (dia p)

/-- The edge from the boundary vertex at `p` to the collar vertex at `p+1`. -/
def cG    := toS vc ec hc (gdi p)

/-- The outer triangle at the position `p`. -/
def cT1    := toS vc ec hc (tr1 p)

/-- The inner triangle of the collar at the position `p`. -/
def cT2    := toS vc ec hc (tr2 p)

/-- The centre of the polygon. -/
def cC   := toS vc ec hc ctr

/-- The radius at the position `p`. -/
def cR    := toS vc ec hc (rad p)

/-- The triangle of the fan at the position `p`. -/
def cI    := toS vc ec hc (inn p)

variable (hc : Compat vc ec)

/-! ### The incidences -/

section
omit [DecidableEq κ] [DecidableEq ι]
variable (p : Fin M)
theorem cV_le_cE  : cV hc p ≤ cE hc p :=
  le_of_plt hc (show plt vc ec (vtx (vc p)) (bed (ec p)) from ⟨p, rfl, Or.inl rfl⟩)

theorem cV1_le_cE  : cV hc (p + 1) ≤ cE hc p :=
  le_of_plt hc (show plt vc ec (vtx (vc (p + 1))) (bed (ec p)) from ⟨p, rfl, Or.inr rfl⟩)

theorem cV_le_cD  : cV hc p ≤ cD hc p :=
  le_of_plt hc (show plt vc ec (vtx (vc p)) (dia p) from rfl)

theorem cW_le_cD  : cW hc p ≤ cD hc p :=
  le_of_plt hc (show plt vc ec (cvx p) (dia p) from rfl)

theorem cV_le_cG  : cV hc p ≤ cG hc p :=
  le_of_plt hc (show plt vc ec (vtx (vc p)) (gdi p) from rfl)

theorem cW1_le_cG  : cW hc (p + 1) ≤ cG hc p :=
  le_of_plt hc (show plt vc ec (cvx (p + 1)) (gdi p) from rfl)

theorem cW_le_cF  : cW hc p ≤ cF hc p :=
  le_of_plt hc (show plt vc ec (cvx p) (ced p) from Or.inl rfl)

theorem cW1_le_cF  : cW hc (p + 1) ≤ cF hc p :=
  le_of_plt hc (show plt vc ec (cvx (p + 1)) (ced p) from Or.inr rfl)

theorem cC_le_cR  : cC hc ≤ cR hc p :=
  le_of_plt hc (show plt vc ec ctr (rad p) from trivial)

theorem cW_le_cR  : cW hc p ≤ cR hc p :=
  le_of_plt hc (show plt vc ec (cvx p) (rad p) from rfl)

/-! ### The faces of the three triangles -/

theorem cE_le_cT1  : cE hc p ≤ cT1 hc p :=
  le_of_plt hc (show plt vc ec (bed (ec p)) (tr1 p) from rfl)

theorem cD1_le_cT1  : cD hc (p + 1) ≤ cT1 hc p :=
  le_of_plt hc (show plt vc ec (dia (p + 1)) (tr1 p) from rfl)

theorem cG_le_cT1  : cG hc p ≤ cT1 hc p :=
  le_of_plt hc (show plt vc ec (gdi p) (tr1 p) from rfl)

theorem cV_le_cT1  : cV hc p ≤ cT1 hc p :=
  le_of_plt hc (show plt vc ec (vtx (vc p)) (tr1 p) from Or.inl rfl)

theorem cV1_le_cT1  : cV hc (p + 1) ≤ cT1 hc p :=
  le_of_plt hc (show plt vc ec (vtx (vc (p + 1))) (tr1 p) from Or.inr rfl)

theorem cW1_le_cT1  : cW hc (p + 1) ≤ cT1 hc p :=
  le_of_plt hc (show plt vc ec (cvx (p + 1)) (tr1 p) from rfl)

theorem cD_le_cT2  : cD hc p ≤ cT2 hc p :=
  le_of_plt hc (show plt vc ec (dia p) (tr2 p) from rfl)

theorem cF_le_cT2  : cF hc p ≤ cT2 hc p :=
  le_of_plt hc (show plt vc ec (ced p) (tr2 p) from rfl)

theorem cG_le_cT2  : cG hc p ≤ cT2 hc p :=
  le_of_plt hc (show plt vc ec (gdi p) (tr2 p) from rfl)

theorem cV_le_cT2  : cV hc p ≤ cT2 hc p :=
  le_of_plt hc (show plt vc ec (vtx (vc p)) (tr2 p) from rfl)

theorem cW_le_cT2  : cW hc p ≤ cT2 hc p :=
  le_of_plt hc (show plt vc ec (cvx p) (tr2 p) from Or.inl rfl)

theorem cW1_le_cT2  : cW hc (p + 1) ≤ cT2 hc p :=
  le_of_plt hc (show plt vc ec (cvx (p + 1)) (tr2 p) from Or.inr rfl)

theorem cR_le_cI  : cR hc p ≤ cI hc p :=
  le_of_plt hc (show plt vc ec (rad p) (inn p) from Or.inl rfl)

theorem cR1_le_cI  : cR hc (p + 1) ≤ cI hc p :=
  le_of_plt hc (show plt vc ec (rad (p + 1)) (inn p) from Or.inr rfl)

theorem cF_le_cI  : cF hc p ≤ cI hc p :=
  le_of_plt hc (show plt vc ec (ced p) (inn p) from rfl)

theorem cC_le_cI  : cC hc ≤ cI hc p :=
  le_of_plt hc (show plt vc ec ctr (inn p) from trivial)

theorem cW_le_cI  : cW hc p ≤ cI hc p :=
  le_of_plt hc (show plt vc ec (cvx p) (inn p) from Or.inl rfl)

theorem cW1_le_cI  : cW hc (p + 1) ≤ cI hc p :=
  le_of_plt hc (show plt vc ec (cvx (p + 1)) (inn p) from Or.inr rfl)
end

/-! ### The paths -/

variable (p : Fin M)
/-- The boundary edge at `p`, crossed from the vertex at `p` to the vertex at `p+1`. -/
def bdEdge   :=
  edgeHop (cV_le_cE hc p) ++ edgeHopRev (cV1_le_cE hc p)

/-- From the collar vertex at `p` to the boundary vertex at `p`. -/
def delta   :=
  edgeHop (cW_le_cD hc p) ++ edgeHopRev (cV_le_cD hc p)

/-- Along the collar, from `p` to `p+1`. -/
def gam   :=
  edgeHop (cW_le_cF hc p) ++ edgeHopRev (cW1_le_cF hc p)

/-- The diagonal, from the boundary vertex at `p` to the collar vertex at `p+1`. -/
def gg   :=
  edgeHop (cV_le_cG hc p) ++ edgeHopRev (cW1_le_cG hc p)

/-- From the centre to the collar vertex at `p`. -/
def alph   :=
  edgeHop (cC_le_cR hc p) ++ edgeHopRev (cW_le_cR hc p)

/-- From the centre to the boundary vertex at `p`. -/
def ray   :=
  alph hc p ++ delta hc p

theorem isPath_bdEdge  :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (bdEdge hc p)
      (spx1 (cV hc p)) (spx1 (cV hc (p + 1))) :=
  (isPath_edgeHop _).append (isPath_edgeHopRev _)

theorem isPath_delta  :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (delta hc p)
      (spx1 (cW hc p)) (spx1 (cV hc p)) :=
  (isPath_edgeHop _).append (isPath_edgeHopRev _)

theorem isPath_gam  :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (gam hc p)
      (spx1 (cW hc p)) (spx1 (cW hc (p + 1))) :=
  (isPath_edgeHop _).append (isPath_edgeHopRev _)

theorem isPath_gg  :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (gg hc p)
      (spx1 (cV hc p)) (spx1 (cW hc (p + 1))) :=
  (isPath_edgeHop _).append (isPath_edgeHopRev _)

theorem isPath_alph  :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (alph hc p)
      (spx1 (cC hc)) (spx1 (cW hc p)) :=
  (isPath_edgeHop _).append (isPath_edgeHopRev _)

theorem isPath_ray  :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (ray hc p)
      (spx1 (cC hc)) (spx1 (cV hc p)) :=
  (isPath_alph hc p).append (isPath_delta hc p)

/-! ### The paths inside the stars of the three triangles -/

theorem pathIn_bdEdge_T1  :
    PathIn (StarCh (cT1 hc p)) (bdEdge hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cV_le_cT1 hc p) (cE_le_cT1 hc p))
    (pathIn_edgeHopRev _ (cV1_le_cT1 hc p) (cE_le_cT1 hc p))

theorem pathIn_gg_T1  : PathIn (StarCh (cT1 hc p)) (gg hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cV_le_cT1 hc p) (cG_le_cT1 hc p))
    (pathIn_edgeHopRev _ (cW1_le_cT1 hc p) (cG_le_cT1 hc p))

theorem pathIn_delta1_T1  : PathIn (StarCh (cT1 hc p)) (delta hc (p + 1)) :=
  pathIn_append' (pathIn_edgeHop _ (cW1_le_cT1 hc p) (cD1_le_cT1 hc p))
    (pathIn_edgeHopRev _ (cV1_le_cT1 hc p) (cD1_le_cT1 hc p))

theorem pathIn_delta_T2  : PathIn (StarCh (cT2 hc p)) (delta hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cW_le_cT2 hc p) (cD_le_cT2 hc p))
    (pathIn_edgeHopRev _ (cV_le_cT2 hc p) (cD_le_cT2 hc p))

theorem pathIn_gam_T2  : PathIn (StarCh (cT2 hc p)) (gam hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cW_le_cT2 hc p) (cF_le_cT2 hc p))
    (pathIn_edgeHopRev _ (cW1_le_cT2 hc p) (cF_le_cT2 hc p))

theorem pathIn_gg_T2  : PathIn (StarCh (cT2 hc p)) (gg hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cV_le_cT2 hc p) (cG_le_cT2 hc p))
    (pathIn_edgeHopRev _ (cW1_le_cT2 hc p) (cG_le_cT2 hc p))

theorem pathIn_alph_I  : PathIn (StarCh (cI hc p)) (alph hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cC_le_cI hc p) (cR_le_cI hc p))
    (pathIn_edgeHopRev _ (cW_le_cI hc p) (cR_le_cI hc p))

theorem pathIn_alph1_I  : PathIn (StarCh (cI hc p)) (alph hc (p + 1)) :=
  pathIn_append' (pathIn_edgeHop _ (cC_le_cI hc p) (cR1_le_cI hc p))
    (pathIn_edgeHopRev _ (cW1_le_cI hc p) (cR1_le_cI hc p))

theorem pathIn_gam_I  : PathIn (StarCh (cI hc p)) (gam hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cW_le_cI hc p) (cF_le_cI hc p))
    (pathIn_edgeHopRev _ (cW1_le_cI hc p) (cF_le_cI hc p))

end

end FiniteChains.Davis

