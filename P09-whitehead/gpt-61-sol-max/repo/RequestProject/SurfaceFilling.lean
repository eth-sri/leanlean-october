import Mathlib.Tactic

import RequestProject.SurfaceCells

/-!
# The polygon is filled: the boundary loop of the surface bounds

The boundary of the polygon of `RequestProject/SurfacePoset.lean` is a loop of the barycentric
subdivision of the triangulation, based at the vertex of the position `0`.  This file proves
that this loop is **null-homotopic**, by filling the polygon one triangle at a time:

* `htpy_bdEdge` — crossing the boundary edge at `p` is homotopic to going through the collar
  vertex at `p+1`; the homotopy is the outer triangle `tr1 p`;
* `htpy_gg` — the diagonal is homotopic to the path through the collar; the homotopy is the
  inner triangle of the collar `tr2 p`;
* `htpy_alph` — the ray to the collar vertex at `p` followed by the collar edge is homotopic to
  the ray to the collar vertex at `p+1`; the homotopy is the triangle `inn p` of the fan;
* `htpy_ray_step` — consequently the ray to the boundary vertex at `p` followed by the boundary
  edge at `p` is homotopic to the ray to the boundary vertex at `p+1`;
* `htpy_bdPath` and `htpy_bdLoop_nil` — hence the whole boundary loop is null-homotopic.

Each of the three elementary homotopies is an instance of one and the same fact: a loop which
stays inside the closed star of a single cell bounds (`FiniteChains.Davis.htpy_nil_of_star`).
-/

namespace FiniteChains.Davis


open RACG Mirror Comb Cell


section

variable {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)

/-! ### The three elementary homotopies -/

variable (p : Fin M)
/-- **Crossing the boundary edge at `p`** is homotopic to going to the collar vertex at `p+1`
along the diagonal and coming back to the boundary: the homotopy is the triangle `tr1 p`. -/
abbrev htpy_bdEdge   :=
  FiniteChains.Davis.htpy_of_loop_nil (FiniteChains.Davis.isPath_bdEdge hc p)
    (FiniteChains.Comb.IsPath.append (FiniteChains.Davis.isPath_gg hc p) (FiniteChains.Davis.isPath_delta hc (p + 1)))
    (FiniteChains.Davis.htpy_nil_of_star (FiniteChains.Davis.cT1 hc p)
      (FiniteChains.Davis.starCh_spx1 (FiniteChains.Davis.cV_le_cT1 hc p))
      (FiniteChains.Comb.IsPath.append (FiniteChains.Davis.isPath_bdEdge hc p)
        (FiniteChains.Comb.isPath_revPath
          (FiniteChains.Comb.IsPath.append (FiniteChains.Davis.isPath_gg hc p)
            (FiniteChains.Davis.isPath_delta hc (p + 1)))))
      (FiniteChains.Davis.pathIn_append' (FiniteChains.Davis.pathIn_bdEdge_T1 hc p)
        (FiniteChains.Comb.pathIn_revPath
          (FiniteChains.Davis.pathIn_append' (FiniteChains.Davis.pathIn_gg_T1 hc p)
            (FiniteChains.Davis.pathIn_delta1_T1 hc p)))))

/-- **The diagonal is homotopic to the path through the collar**: the homotopy is the triangle
`tr2 p`. -/
abbrev htpy_gg   :=
  FiniteChains.Davis.htpy_of_loop_nil
    (FiniteChains.Comb.IsPath.append (FiniteChains.Comb.isPath_revPath (FiniteChains.Davis.isPath_delta hc p))
      (FiniteChains.Davis.isPath_gam hc p))
    (FiniteChains.Davis.isPath_gg hc p)
    (FiniteChains.Davis.htpy_nil_of_star (FiniteChains.Davis.cT2 hc p)
      (FiniteChains.Davis.starCh_spx1 (FiniteChains.Davis.cV_le_cT2 hc p))
      (FiniteChains.Comb.IsPath.append
        (FiniteChains.Comb.IsPath.append (FiniteChains.Comb.isPath_revPath (FiniteChains.Davis.isPath_delta hc p))
          (FiniteChains.Davis.isPath_gam hc p))
        (FiniteChains.Comb.isPath_revPath (FiniteChains.Davis.isPath_gg hc p)))
      (FiniteChains.Davis.pathIn_append'
        (FiniteChains.Davis.pathIn_append' (FiniteChains.Comb.pathIn_revPath (FiniteChains.Davis.pathIn_delta_T2 hc p))
          (FiniteChains.Davis.pathIn_gam_T2 hc p))
        (FiniteChains.Comb.pathIn_revPath (FiniteChains.Davis.pathIn_gg_T2 hc p))))

/-- **The fan contracts the collar**: the ray to the collar vertex at `p` followed by the collar
edge is homotopic to the ray to the collar vertex at `p+1`; the homotopy is the triangle
`inn p`. -/
abbrev htpy_alph   :=
  FiniteChains.Davis.htpy_of_loop_nil
    (FiniteChains.Comb.IsPath.append (FiniteChains.Davis.isPath_alph hc p) (FiniteChains.Davis.isPath_gam hc p))
    (FiniteChains.Davis.isPath_alph hc (p + 1))
    (FiniteChains.Davis.htpy_nil_of_star (FiniteChains.Davis.cI hc p)
      (FiniteChains.Davis.starCh_spx1 (FiniteChains.Davis.cC_le_cI hc p))
      (FiniteChains.Comb.IsPath.append
        (FiniteChains.Comb.IsPath.append (FiniteChains.Davis.isPath_alph hc p) (FiniteChains.Davis.isPath_gam hc p))
        (FiniteChains.Comb.isPath_revPath (FiniteChains.Davis.isPath_alph hc (p + 1))))
      (FiniteChains.Davis.pathIn_append'
        (FiniteChains.Davis.pathIn_append' (FiniteChains.Davis.pathIn_alph_I hc p) (FiniteChains.Davis.pathIn_gam_I hc p))
        (FiniteChains.Comb.pathIn_revPath (FiniteChains.Davis.pathIn_alph1_I hc p))))

/-! ### The rays sweep the polygon -/

/-- **One step of the sweep**: the ray to the boundary vertex at `p`, followed by the boundary
edge at `p`, is homotopic to the ray to the boundary vertex at `p+1`. -/
theorem htpy_ray_step  :
    Htpy (sdCx hc) (spx1 (cC hc)) (spx1 (cV hc (p + 1)))
      (ray hc p ++ bdEdge hc p) (ray hc (p + 1)) := by
  have hA := htpy_bdEdge hc p
  have hB := htpy_gg hc p
  have hC := htpy_alph hc p
  -- the collar edge replaces the diagonal
  have hD : Htpy (sdCx hc) (spx1 (cW hc p)) (spx1 (cW hc (p + 1)))
      (delta hc p ++ gg hc p) (gam hc p) := by
    have h1  :=
      htpy_append_left (isPath_delta hc p) (isPath_gg hc p) hB.symm
    have h3  :=
      htpy_append_right ((isPath_delta hc p).append (isPath_revPath (isPath_delta hc p)))
        (isPath_gam hc p) (htpy_append_revPath (isPath_delta hc p))
    refine h1.trans ?_
    simpa [List.append_assoc] using h3
  have e1 : Htpy (sdCx hc) (spx1 (cC hc)) (spx1 (cV hc (p + 1)))
      (ray hc p ++ bdEdge hc p)
      (alph hc p ++ (delta hc p ++ (gg hc p ++ delta hc (p + 1)))) := by
    solve_by_elim [FiniteChains.Davis.htpy_append_left, FiniteChains.Davis.isPath_ray, FiniteChains.Davis.isPath_bdEdge]
  have e2 : Htpy (sdCx hc) (spx1 (cC hc)) (spx1 (cV hc (p + 1)))
      (alph hc p ++ (delta hc p ++ (gg hc p ++ delta hc (p + 1))))
      (alph hc p ++ (gam hc p ++ delta hc (p + 1))) := by
    have inner  :=
      htpy_append_right ((isPath_delta hc p).append (isPath_gg hc p))
        (isPath_delta hc (p + 1)) hD
    simpa [List.append_assoc] using
      htpy_append_left (isPath_alph hc p)
        (((isPath_delta hc p).append (isPath_gg hc p)).append (isPath_delta hc (p + 1))) inner
  have e3 : Htpy (sdCx hc) (spx1 (cC hc)) (spx1 (cV hc (p + 1)))
      (alph hc p ++ (gam hc p ++ delta hc (p + 1))) (ray hc (p + 1)) := by
    simpa [ray, List.append_assoc] using
      htpy_append_right ((isPath_alph hc p).append (isPath_gam hc p))
        (isPath_delta hc (p + 1)) hC
  exact e1.trans (e2.trans e3)

/-! ### The boundary loop -/

/-- The position `n` of the boundary, read cyclically. -/
def cyc (M : ℕ) [NeZero M] (n : ℕ) : Fin M := ⟨n % M, Nat.mod_lt _ (NeZero.pos M)⟩

variable (n : ℕ)
theorem cyc_succ  : cyc M (n + 1) = cyc M n + 1 := by
  solve_by_elim [Fin.ext, Nat.add_mod]

theorem cyc_self : cyc M M = cyc M 0 := by
  solve_by_elim [Fin.ext, Nat.mod_self]

/-- **The boundary path**: the first `n` edges of the boundary of the polygon. -/
def bdPath : ℕ → List ((sdCx hc).E × Bool)
  | 0 => []
  | n + 1 => bdPath n ++ bdEdge hc (cyc M n)

theorem isPath_bdPath  :
    IsPath (sdCx hc).src (sdCx hc).tgt (bdPath hc n)
      (spx1 (cV hc (cyc M 0))) (spx1 (cV hc (cyc M n))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h := ih.append (isPath_bdEdge hc (cyc M n))
      rw [← cyc_succ] at h
      exact h

/-- **The boundary path is swept by the rays.** -/
theorem htpy_bdPath  :
    Htpy (sdCx hc) (spx1 (cV hc (cyc M 0))) (spx1 (cV hc (cyc M n)))
      (bdPath hc n) (revPath (ray hc (cyc M 0)) ++ ray hc (cyc M n)) := by
  induction n with
  | zero => exact (htpy_revPath_append (isPath_ray hc (cyc M 0))).symm
  | succ n ih =>
      have h1  :=
        htpy_append_right (isPath_bdPath hc n) (isPath_bdEdge hc (cyc M n)) ih
      have h2  :=
        htpy_append_left (isPath_revPath (isPath_ray hc (cyc M 0)))
          ((isPath_ray hc (cyc M n)).append (isPath_bdEdge hc (cyc M n)))
          (htpy_ray_step hc (cyc M n))
      have h3 : Htpy (sdCx hc) (spx1 (cV hc (cyc M 0))) (spx1 (cV hc (cyc M n + 1)))
          (bdPath hc (n + 1)) (revPath (ray hc (cyc M 0)) ++ ray hc (cyc M n + 1)) := by
        classical solve_by_elim (transparency := .default) (maxDepth := 10) [FiniteChains.Comb.Htpy.trans, FiniteChains.Comb.Htpy, sdCx, spx1, cV, cyc, bdPath, revPath, ray, bdEdge]
      rw [cyc_succ]
      exact h3

/-- **The boundary of the polygon bounds**: the loop which goes once around the boundary of the
polygon, based at the vertex of the position `0`, is null-homotopic in the barycentric
subdivision of the triangulation of the surface. -/
theorem htpy_bdLoop_nil :
    Htpy (sdCx hc) (spx1 (cV hc (cyc M 0))) (spx1 (cV hc (cyc M 0))) (bdPath hc M) [] := by
  have h := htpy_bdPath hc M
  rw [cyc_self] at h
  exact h.trans (htpy_revPath_append (isPath_ray hc (cyc M 0)))

end

end FiniteChains.Davis

