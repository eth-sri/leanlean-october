module

public import RequestProject.SurfacePoset

@[expose] public section

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


variable {κ ι : Type u} {M : ℕ} [NeZero M]
  {vc : Fin M → κ} {ec : Fin M → ι}

abbrev sdCx (hc : Compat vc ec) : Complex2.{u} :=
  orderCx (NeSpx (cmpRel (SCell vc ec hc)))

def cV (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (vtx (vc p))
def cE (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (bed (ec p))
def cW (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (cvx p)
def cF (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (ced p)
def cD (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (dia p)
def cG (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (gdi p)
def cT1 (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (tr1 p)
def cT2 (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (tr2 p)
def cC (hc : Compat vc ec) : SCell vc ec hc := toS vc ec hc ctr
def cR (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (rad p)
def cI (hc : Compat vc ec) (p : Fin M) : SCell vc ec hc := toS vc ec hc (inn p)

variable (hc : Compat vc ec)

theorem cV_le_cE (p : Fin M) : cV hc p ≤ cE hc p := le_of_plt hc ⟨p, rfl, Or.inl rfl⟩
theorem cV1_le_cE (p : Fin M) : cV hc (p + 1) ≤ cE hc p := le_of_plt hc ⟨p, rfl, Or.inr rfl⟩
theorem cV_le_cD (p : Fin M) : cV hc p ≤ cD hc p := le_of_plt hc rfl
theorem cW_le_cD (p : Fin M) : cW hc p ≤ cD hc p := le_of_plt hc rfl
theorem cV_le_cG (p : Fin M) : cV hc p ≤ cG hc p := le_of_plt hc rfl
theorem cW1_le_cG (p : Fin M) : cW hc (p + 1) ≤ cG hc p := le_of_plt hc rfl
theorem cW_le_cF (p : Fin M) : cW hc p ≤ cF hc p := le_of_plt hc (Or.inl rfl)
theorem cW1_le_cF (p : Fin M) : cW hc (p + 1) ≤ cF hc p := le_of_plt hc (Or.inr rfl)
theorem cC_le_cR (p : Fin M) : cC hc ≤ cR hc p := le_of_plt hc trivial
theorem cW_le_cR (p : Fin M) : cW hc p ≤ cR hc p := le_of_plt hc rfl
theorem cE_le_cT1 (p : Fin M) : cE hc p ≤ cT1 hc p := le_of_plt hc rfl
theorem cD1_le_cT1 (p : Fin M) : cD hc (p + 1) ≤ cT1 hc p := le_of_plt hc rfl
theorem cG_le_cT1 (p : Fin M) : cG hc p ≤ cT1 hc p := le_of_plt hc rfl
theorem cV_le_cT1 (p : Fin M) : cV hc p ≤ cT1 hc p := le_of_plt hc (Or.inl rfl)
theorem cV1_le_cT1 (p : Fin M) : cV hc (p + 1) ≤ cT1 hc p := le_of_plt hc (Or.inr rfl)
theorem cW1_le_cT1 (p : Fin M) : cW hc (p + 1) ≤ cT1 hc p := le_of_plt hc rfl
theorem cD_le_cT2 (p : Fin M) : cD hc p ≤ cT2 hc p := le_of_plt hc rfl
theorem cF_le_cT2 (p : Fin M) : cF hc p ≤ cT2 hc p := le_of_plt hc rfl
theorem cG_le_cT2 (p : Fin M) : cG hc p ≤ cT2 hc p := le_of_plt hc rfl
theorem cV_le_cT2 (p : Fin M) : cV hc p ≤ cT2 hc p := le_of_plt hc rfl
theorem cW_le_cT2 (p : Fin M) : cW hc p ≤ cT2 hc p := le_of_plt hc (Or.inl rfl)
theorem cW1_le_cT2 (p : Fin M) : cW hc (p + 1) ≤ cT2 hc p := le_of_plt hc (Or.inr rfl)
theorem cR_le_cI (p : Fin M) : cR hc p ≤ cI hc p := le_of_plt hc (Or.inl rfl)
theorem cR1_le_cI (p : Fin M) : cR hc (p + 1) ≤ cI hc p := le_of_plt hc (Or.inr rfl)
theorem cF_le_cI (p : Fin M) : cF hc p ≤ cI hc p := le_of_plt hc rfl
theorem cC_le_cI (p : Fin M) : cC hc ≤ cI hc p := le_of_plt hc trivial
theorem cW_le_cI (p : Fin M) : cW hc p ≤ cI hc p := le_of_plt hc (Or.inl rfl)
theorem cW1_le_cI (p : Fin M) : cW hc (p + 1) ≤ cI hc p := le_of_plt hc (Or.inr rfl)

variable [DecidableEq κ] [DecidableEq ι]

def bdEdge (p : Fin M) := edgeHop (cV_le_cE hc p) ++ edgeHopRev (cV1_le_cE hc p)
def delta (p : Fin M) := edgeHop (cW_le_cD hc p) ++ edgeHopRev (cV_le_cD hc p)
def gam (p : Fin M) := edgeHop (cW_le_cF hc p) ++ edgeHopRev (cW1_le_cF hc p)
def gg (p : Fin M) := edgeHop (cV_le_cG hc p) ++ edgeHopRev (cW1_le_cG hc p)
def alph (p : Fin M) := edgeHop (cC_le_cR hc p) ++ edgeHopRev (cW_le_cR hc p)
def ray (p : Fin M) := alph hc p ++ delta hc p

theorem isPath_bdEdge (p : Fin M) :
    IsPath (sdCx hc).src (sdCx hc).tgt (bdEdge hc p) (spx1 (cV hc p)) (spx1 (cV hc (p + 1))) :=
  (isPath_edgeHop _).append (isPath_edgeHopRev _)

theorem isPath_delta (p : Fin M) :
    IsPath (sdCx hc).src (sdCx hc).tgt (delta hc p) (spx1 (cW hc p)) (spx1 (cV hc p)) :=
  (isPath_edgeHop _).append (isPath_edgeHopRev _)

theorem isPath_gam (p : Fin M) :
    IsPath (sdCx hc).src (sdCx hc).tgt (gam hc p) (spx1 (cW hc p)) (spx1 (cW hc (p + 1))) :=
  (isPath_edgeHop _).append (isPath_edgeHopRev _)

theorem isPath_gg (p : Fin M) :
    IsPath (sdCx hc).src (sdCx hc).tgt (gg hc p) (spx1 (cV hc p)) (spx1 (cW hc (p + 1))) :=
  (isPath_edgeHop _).append (isPath_edgeHopRev _)

theorem isPath_alph (p : Fin M) :
    IsPath (sdCx hc).src (sdCx hc).tgt (alph hc p) (spx1 (cC hc)) (spx1 (cW hc p)) :=
  (isPath_edgeHop _).append (isPath_edgeHopRev _)

theorem isPath_ray (p : Fin M) :
    IsPath (sdCx hc).src (sdCx hc).tgt (ray hc p) (spx1 (cC hc)) (spx1 (cV hc p)) :=
  (isPath_alph hc p).append (isPath_delta hc p)

theorem pathIn_bdEdge_T1 (p : Fin M) : PathIn (StarCh (cT1 hc p)) (bdEdge hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cV_le_cT1 hc p) (cE_le_cT1 hc p))
    (pathIn_edgeHopRev _ (cV1_le_cT1 hc p) (cE_le_cT1 hc p))

theorem pathIn_gg_T1 (p : Fin M) : PathIn (StarCh (cT1 hc p)) (gg hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cV_le_cT1 hc p) (cG_le_cT1 hc p))
    (pathIn_edgeHopRev _ (cW1_le_cT1 hc p) (cG_le_cT1 hc p))

theorem pathIn_delta1_T1 (p : Fin M) : PathIn (StarCh (cT1 hc p)) (delta hc (p + 1)) :=
  pathIn_append' (pathIn_edgeHop _ (cW1_le_cT1 hc p) (cD1_le_cT1 hc p))
    (pathIn_edgeHopRev _ (cV1_le_cT1 hc p) (cD1_le_cT1 hc p))

theorem pathIn_delta_T2 (p : Fin M) : PathIn (StarCh (cT2 hc p)) (delta hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cW_le_cT2 hc p) (cD_le_cT2 hc p))
    (pathIn_edgeHopRev _ (cV_le_cT2 hc p) (cD_le_cT2 hc p))

theorem pathIn_gam_T2 (p : Fin M) : PathIn (StarCh (cT2 hc p)) (gam hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cW_le_cT2 hc p) (cF_le_cT2 hc p))
    (pathIn_edgeHopRev _ (cW1_le_cT2 hc p) (cF_le_cT2 hc p))

theorem pathIn_gg_T2 (p : Fin M) : PathIn (StarCh (cT2 hc p)) (gg hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cV_le_cT2 hc p) (cG_le_cT2 hc p))
    (pathIn_edgeHopRev _ (cW1_le_cT2 hc p) (cG_le_cT2 hc p))

theorem pathIn_alph_I (p : Fin M) : PathIn (StarCh (cI hc p)) (alph hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cC_le_cI hc p) (cR_le_cI hc p))
    (pathIn_edgeHopRev _ (cW_le_cI hc p) (cR_le_cI hc p))

theorem pathIn_alph1_I (p : Fin M) : PathIn (StarCh (cI hc p)) (alph hc (p + 1)) :=
  pathIn_append' (pathIn_edgeHop _ (cC_le_cI hc p) (cR1_le_cI hc p))
    (pathIn_edgeHopRev _ (cW1_le_cI hc p) (cR1_le_cI hc p))

theorem pathIn_gam_I (p : Fin M) : PathIn (StarCh (cI hc p)) (gam hc p) :=
  pathIn_append' (pathIn_edgeHop _ (cW_le_cI hc p) (cF_le_cI hc p))
    (pathIn_edgeHopRev _ (cW1_le_cI hc p) (cF_le_cI hc p))
