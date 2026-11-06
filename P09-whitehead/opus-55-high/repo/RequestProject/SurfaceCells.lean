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

universe u

section Cells

variable {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι}

/-- The barycentric subdivision of the triangulation of the surface, as a two-complex: the order
complex of the poset of nonempty chains of cells. -/
abbrev sdCx (hc : Compat vc ec) :=
  orderCx (NeSpx (cmpRel (SCell vc ec hc)))

/-! ### The cells -/

/-- The boundary vertex at the position `p`. -/
def cV (hc : Compat vc ec) (p : Fin M) := toS vc ec hc (vtx (vc p))

/-- The boundary edge at the position `p`. -/
def cE (hc : Compat vc ec) (p : Fin M) := toS vc ec hc (bed (ec p))

/-- The collar vertex at the position `p`. -/
def cW (hc : Compat vc ec) (p : Fin M) := toS vc ec hc (cvx p)

/-- The collar edge at the position `p`. -/
def cF (hc : Compat vc ec) (p : Fin M) := toS vc ec hc (ced p)

/-- The edge from the boundary vertex at `p` to the collar vertex at `p`. -/
def cD (hc : Compat vc ec) (p : Fin M) := toS vc ec hc (dia p)

/-- The edge from the boundary vertex at `p` to the collar vertex at `p+1`. -/
def cG (hc : Compat vc ec) (p : Fin M) := toS vc ec hc (gdi p)

/-- The outer triangle at the position `p`. -/
def cT1 (hc : Compat vc ec) (p : Fin M) := toS vc ec hc (tr1 p)

/-- The inner triangle of the collar at the position `p`. -/
def cT2 (hc : Compat vc ec) (p : Fin M) := toS vc ec hc (tr2 p)

/-- The centre of the polygon. -/
def cC (hc : Compat vc ec) := toS vc ec hc ctr

/-- The radius at the position `p`. -/
def cR (hc : Compat vc ec) (p : Fin M) := toS vc ec hc (rad p)

/-- The triangle of the fan at the position `p`. -/
def cI (hc : Compat vc ec) (p : Fin M) := toS vc ec hc (inn p)

variable (hc : Compat vc ec)

/-! ### The incidences -/

omit [DecidableEq κ] [DecidableEq ι] in
theorem cV_le_cE (p : Fin M) : cV hc p ≤ cE hc p :=
  le_of_plt hc (show plt vc ec (vtx (vc p)) (bed (ec p)) from ⟨p, rfl, Or.inl rfl⟩)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cV1_le_cE (p : Fin M) : cV hc (p + 1) ≤ cE hc p :=
  le_of_plt hc (show plt vc ec (vtx (vc (p + 1))) (bed (ec p)) from ⟨p, rfl, Or.inr rfl⟩)

omit [DecidableEq κ] [DecidableEq ι] in
theorem cV_le_cD (p : Fin M) : cV hc p ≤ cD hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW_le_cD (p : Fin M) : cW hc p ≤ cD hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cV_le_cG (p : Fin M) : cV hc p ≤ cG hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW1_le_cG (p : Fin M) : cW hc (p + 1) ≤ cG hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW_le_cF (p : Fin M) : cW hc p ≤ cF hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW1_le_cF (p : Fin M) : cW hc (p + 1) ≤ cF hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cC_le_cR (p : Fin M) : cC hc ≤ cR hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW_le_cR (p : Fin M) : cW hc p ≤ cR hc p :=
  by tauto

/-! ### The faces of the three triangles -/

omit [DecidableEq κ] [DecidableEq ι] in
theorem cE_le_cT1 (p : Fin M) : cE hc p ≤ cT1 hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cD1_le_cT1 (p : Fin M) : cD hc (p + 1) ≤ cT1 hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cG_le_cT1 (p : Fin M) : cG hc p ≤ cT1 hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cV_le_cT1 (p : Fin M) : cV hc p ≤ cT1 hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cV1_le_cT1 (p : Fin M) : cV hc (p + 1) ≤ cT1 hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW1_le_cT1 (p : Fin M) : cW hc (p + 1) ≤ cT1 hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cD_le_cT2 (p : Fin M) : cD hc p ≤ cT2 hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cF_le_cT2 (p : Fin M) : cF hc p ≤ cT2 hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cG_le_cT2 (p : Fin M) : cG hc p ≤ cT2 hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cV_le_cT2 (p : Fin M) : cV hc p ≤ cT2 hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW_le_cT2 (p : Fin M) : cW hc p ≤ cT2 hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW1_le_cT2 (p : Fin M) : cW hc (p + 1) ≤ cT2 hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cR_le_cI (p : Fin M) : cR hc p ≤ cI hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cR1_le_cI (p : Fin M) : cR hc (p + 1) ≤ cI hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cF_le_cI (p : Fin M) : cF hc p ≤ cI hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cC_le_cI (p : Fin M) : cC hc ≤ cI hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW_le_cI (p : Fin M) : cW hc p ≤ cI hc p :=
  by tauto

omit [DecidableEq κ] [DecidableEq ι] in
theorem cW1_le_cI (p : Fin M) : cW hc (p + 1) ≤ cI hc p :=
  by tauto

/-! ### The paths -/

/-- The boundary edge at `p`, crossed from the vertex at `p` to the vertex at `p+1`. -/
def bdEdge (p : Fin M) :=
  edgeHop (cV_le_cE hc p) ++ edgeHopRev (cV1_le_cE hc p)

/-- From the collar vertex at `p` to the boundary vertex at `p`. -/
def delta (p : Fin M) :=
  edgeHop (cW_le_cD hc p) ++ edgeHopRev (cV_le_cD hc p)

/-- Along the collar, from `p` to `p+1`. -/
def gam (p : Fin M) :=
  edgeHop (cW_le_cF hc p) ++ edgeHopRev (cW1_le_cF hc p)

/-- The diagonal, from the boundary vertex at `p` to the collar vertex at `p+1`. -/
def gg (p : Fin M) :=
  edgeHop (cV_le_cG hc p) ++ edgeHopRev (cW1_le_cG hc p)

/-- From the centre to the collar vertex at `p`. -/
def alph (p : Fin M) :=
  edgeHop (cC_le_cR hc p) ++ edgeHopRev (cW_le_cR hc p)

/-- From the centre to the boundary vertex at `p`. -/
def ray (p : Fin M) :=
  alph hc p ++ delta hc p

theorem isPath_bdEdge p :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (bdEdge hc p)
      (spx1 (cV hc p)) (spx1 (cV hc (p + 1))) :=
  by trivial

theorem isPath_delta p :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (delta hc p)
      (spx1 (cW hc p)) (spx1 (cV hc p)) :=
  by trivial

theorem isPath_gam p :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (gam hc p)
      (spx1 (cW hc p)) (spx1 (cW hc (p + 1))) :=
  by trivial

theorem isPath_gg p :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (gg hc p)
      (spx1 (cV hc p)) (spx1 (cW hc (p + 1))) :=
  by trivial

theorem isPath_alph p :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (alph hc p)
      (spx1 (cC hc)) (spx1 (cW hc p)) :=
  by trivial

theorem isPath_ray p :
    IsPath (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).src
      (orderCx (NeSpx (cmpRel (SCell vc ec hc)))).tgt (ray hc p)
      (spx1 (cC hc)) (spx1 (cV hc p)) :=
  by trivial

/-! ### The paths inside the stars of the three triangles -/

theorem pathIn_bdEdge_T1 p :
    PathIn (StarCh (cT1 hc p)) (bdEdge hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cV_le_cT1 hc p) (cE_le_cT1 hc p))
    (pathIn_edgeHopRev _ (cV1_le_cT1 hc p) (cE_le_cT1 hc p))

theorem pathIn_gg_T1 p : PathIn (StarCh (cT1 hc p)) (gg hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cV_le_cT1 hc p) (cG_le_cT1 hc p))
    (pathIn_edgeHopRev _ (cW1_le_cT1 hc p) (cG_le_cT1 hc p))

theorem pathIn_delta1_T1 p : PathIn (StarCh (cT1 hc p)) (delta hc (p + 1)) :=
  pathIn_append' (pathIn_edgeHop _ (cW1_le_cT1 hc p) (cD1_le_cT1 hc p))
    (pathIn_edgeHopRev _ (cV1_le_cT1 hc p) (cD1_le_cT1 hc p))

theorem pathIn_delta_T2 p : PathIn (StarCh (cT2 hc p)) (delta hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cW_le_cT2 hc p) (cD_le_cT2 hc p))
    (pathIn_edgeHopRev _ (cV_le_cT2 hc p) (cD_le_cT2 hc p))

theorem pathIn_gam_T2 p : PathIn (StarCh (cT2 hc p)) (gam hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cW_le_cT2 hc p) (cF_le_cT2 hc p))
    (pathIn_edgeHopRev _ (cW1_le_cT2 hc p) (cF_le_cT2 hc p))

theorem pathIn_gg_T2 p : PathIn (StarCh (cT2 hc p)) (gg hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cV_le_cT2 hc p) (cG_le_cT2 hc p))
    (pathIn_edgeHopRev _ (cW1_le_cT2 hc p) (cG_le_cT2 hc p))

theorem pathIn_alph_I p : PathIn (StarCh (cI hc p)) (alph hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cC_le_cI hc p) (cR_le_cI hc p))
    (pathIn_edgeHopRev _ (cW_le_cI hc p) (cR_le_cI hc p))

theorem pathIn_alph1_I p : PathIn (StarCh (cI hc p)) (alph hc (p + 1)) :=
  pathIn_append' (pathIn_edgeHop _ (cC_le_cI hc p) (cR1_le_cI hc p))
    (pathIn_edgeHopRev _ (cW1_le_cI hc p) (cR1_le_cI hc p))

theorem pathIn_gam_I p : PathIn (StarCh (cI hc p)) (gam hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cW_le_cI hc p) (cF_le_cI hc p))
    (pathIn_edgeHopRev _ (cW1_le_cI hc p) (cF_le_cI hc p))
