module

public import RequestProject.SurfaceDual
public import RequestProject.GenusSurface

@[expose] public section

/-!
# Lemma 3.2 (ii) for the block of genus `q`

`RequestProject/GenusSurface.lean` shows that the face poset of the `4q`-gon with its sides glued
according to the surface word is a closed surface, and `RequestProject/SurfaceDual.lean` proves
the two global conditions — a side joining any two distinct vertices of a triangle, and
connectedness of the triangles through shared edges — which give connectedness of the dual graph
of the triangulation.

This file puts them together for the block of the article:

* `FiniteChains.Davis.Genus.genus_dual_connected` — the dual graph of the triangulation of the
  surface of genus `q` is connected;
* `FiniteChains.Davis.Genus.genus_spine_collapse` — **all three-cubes of the truncated cube
  complex over that triangulation collapse away**, so the block of genus `q` has a
  two-dimensional spine.  This is the geometric input of Lemma 3.2 (ii) for the actual block,
  with no hypothesis left beyond `q ≠ 0`.
-/

namespace FiniteChains.Davis.Genus

open Cell ASC Relation

variable (q : ℕ) [NeZero q]

/-- **Lemma 3.2 (ii) for the block of genus `q`.**  All three-cubes of the truncated cube complex
over the triangulation of the closed surface of genus `q` are removed by elementary collapses,
leaving a two-dimensional spine. -/
theorem genus_spine_collapse :
    ∃ l : List (Cube (SCell (gvc q) (gec q) (gc q))),
      Collapse.IsCollapse (spineInc (orderComplex (SCell (gvc q) (gec q) (gc q)))) l
        (topCubes (orderComplex (SCell (gvc q) (gec q) (gc q)))) :=
  exists_spine_collapse_SCell (gc q) (genus_polygonData q)
