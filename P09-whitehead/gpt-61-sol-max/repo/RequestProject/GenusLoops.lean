import Mathlib.Tactic

import RequestProject.GenusData
import RequestProject.SurfaceRev

/-!
# The boundary of the polygon of genus `q`: the surface relator is filled

The polygon of `RequestProject/GenusData.lean` is the `4q`-gon whose sides are glued in pairs
according to the surface word `∏_{h<q} a_h b_h a_h⁻¹ b_h⁻¹`.  Its boundary loop is
null-homotopic in the subdivision of the triangulation of the closed surface of genus `q`
(`FiniteChains.Davis.htpy_bdLoop_nil`).  This file cuts that loop into the `4q` sides, checks
that the two sides of a pair are inverse to one another as edge paths, and concludes:

* `FiniteChains.Davis.gSig` — the loop of the distinguished generator `(h, i)` of the block:
  the side number `4h + i` of the polygon, a loop at the base vertex `FiniteChains.Davis.gBase`;
* `FiniteChains.Davis.genus_hfilling` — **the product of the commutators of the classes of these
  loops is trivial** in the fundamental group of the surface.

This is the hypothesis `hfilling` of `FiniteChains.Davis.injective_substHomF_of_surfaceW`,
obtained here from the actual filling of the genuine closed surface.
-/

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis


open RACG Mirror Comb PresModel Cell

namespace Genus

variable (q : ℕ) [NeZero q]

/-- The face poset of the closed surface of genus `q`. -/
abbrev gc :=
  FiniteChains.Davis.genus_compat

/-- The base vertex: the single corner of the polygon. -/
def gBase  :=
  spx1 (cV (gc q) (cyc (8 * q) 0))

/-! ### Elementary computations with the identifications -/

theorem cyc_mod_two (k : ℕ) : (cyc (8 * q) k).val % 2 = k % 2 :=
  Nat.mod_mod_of_dvd k ⟨4 * q, by ring⟩

variable {k : ℕ}
theorem cyc_val_of_lt  (hk : k < 8 * q) : (cyc (8 * q) k).val = k :=
  Nat.mod_eq_of_lt hk

variable (hk : k % 2 = 0)
include hk in
/-- Every corner of the polygon is the same vertex of the surface. -/
theorem gvc_even   : gvc q (cyc (8 * q) k) = none := by simp_all [cyc_mod_two, gvc]

theorem gvc_congr_lt {k k' : ℕ} (hk : k < 8 * q) (hk' : k' < 8 * q) (ho : k % 2 = 1)
    (ho' : k' % 2 = 1) (h1 : k / 2 / 4 = k' / 2 / 4)
    (h2 : (k / 2 % 4 % 2 = 1) ↔ (k' / 2 % 4 % 2 = 1)) :
    gvc q (cyc (8 * q) k) = gvc q (cyc (8 * q) k') := by
  grind [cyc_val_of_lt, gvc]

theorem gec_congr_lt {k k' : ℕ} (hk : k < 8 * q) (hk' : k' < 8 * q)
    (h1 : k / 2 / 4 = k' / 2 / 4)
    (h2 : (k / 2 % 4 % 2 = 1) ↔ (k' / 2 % 4 % 2 = 1))
    (h3 : xor (decide (k % 2 = 1)) (decide (2 ≤ k / 2 % 4))
      = xor (decide (k' % 2 = 1)) (decide (2 ≤ k' / 2 % 4))) :
    gec q (cyc (8 * q) k) = gec q (cyc (8 * q) k') := by
  grind [cyc_val_of_lt, gec]

include hk in
/-- All the corners of the polygon are one and the same cell. -/
theorem cV_even   :
    cV (gc q) (cyc (8 * q) k) = cV (gc q) (cyc (8 * q) 0) :=
  congrArg (fun x => toS (gvc q) (gec q) (gc q) (vtx x))
    ((gvc_even q hk).trans (gvc_even q (k := 0) rfl).symm)

/-! ### The sides of the polygon, and the pairing -/

/-- The side of the polygon starting at the position `m`. -/
abbrev gPath (m : ℕ)  := pPath (gc q) m

theorem isPath_gPath {m : ℕ} (hm : m % 2 = 0) :
    IsPath (sdCx (gc q)).src (sdCx (gc q)).tgt (gPath q m) (gBase q) (gBase q) := by
  have h1 := isPath_bdEdge (gc q) (cyc (8 * q) m)
  rw [← cyc_succ] at h1
  have h2 := isPath_bdEdge (gc q) (cyc (8 * q) (m + 1))
  rw [← cyc_succ] at h2
  have h3 := h1.append h2
  rw [cV_even q hm, cV_even q (k := m + 1 + 1) (by omega)] at h3
  exact h3

variable (n : ℕ)
theorem isPath_bdPath8  :
    IsPath (sdCx (gc q)).src (sdCx (gc q)).tgt (bdPath (gc q) (8 * n)) (gBase q) (gBase q) := by
  have h := isPath_bdPath (gc q) (8 * n)
  rw [cV_even q (k := 8 * n) (by omega)] at h
  exact h

variable {h : ℕ}
  (hh : h < q)
include hh in
/-- The two sides of a pair are inverse edge paths: the first half. -/
theorem bdEdge_rev_a   :
    bdEdge (gc q) (cyc (8 * q) (8 * h + 4))
      = revPath (bdEdge (gc q) (cyc (8 * q) (8 * h + 1))) := by
  refine bdEdge_rev (gc q) ?_ ?_ ?_
  · refine gec_congr_lt q (by omega) (by omega) (by omega) (by omega) ?_
    have e1 : (8 * h + 4) % 2 = 0 := by omega
    have e2 : (8 * h + 4) / 2 % 4 = 2 := by omega
    have e3 : (8 * h + 1) % 2 = 1 := by omega
    have e4 : (8 * h + 1) / 2 % 4 = 0 := by omega
    rw [e1, e2, e3, e4]
    decide
  · grind [FiniteChains.Davis.cyc_succ, FiniteChains.Davis.Genus.gvc_even]
  · rw [← cyc_succ]
    exact gvc_congr_lt q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

include hh in
/-- The two sides of a pair are inverse edge paths: the second half. -/
theorem bdEdge_rev_b   :
    bdEdge (gc q) (cyc (8 * q) (8 * h + 5))
      = revPath (bdEdge (gc q) (cyc (8 * q) (8 * h))) := by
  refine bdEdge_rev (gc q) ?_ ?_ ?_
  · refine gec_congr_lt q (by omega) (by omega) (by omega) (by omega) ?_
    have e1 : (8 * h + 5) % 2 = 1 := by omega
    have e2 : (8 * h + 5) / 2 % 4 = 2 := by omega
    have e3 : (8 * h) % 2 = 0 := by omega
    have e4 : (8 * h) / 2 % 4 = 0 := by omega
    rw [e1, e2, e3, e4]
    decide
  · rw [← cyc_succ]
    exact gvc_congr_lt q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [← cyc_succ]
    exact (gvc_even q (k := 8 * h + 5 + 1) (by omega)).trans (gvc_even q (k := 8 * h) (by omega)).symm

include hh in
/-- The two sides of the second pair are inverse edge paths: the first half. -/
theorem bdEdge_rev_c   :
    bdEdge (gc q) (cyc (8 * q) (8 * h + 6))
      = revPath (bdEdge (gc q) (cyc (8 * q) (8 * h + 3))) := by
  refine bdEdge_rev (gc q) ?_ ?_ ?_
  · refine gec_congr_lt q (by omega) (by omega) (by omega) (by omega) ?_
    have e1 : (8 * h + 6) % 2 = 0 := by omega
    have e2 : (8 * h + 6) / 2 % 4 = 3 := by omega
    have e3 : (8 * h + 3) % 2 = 1 := by omega
    have e4 : (8 * h + 3) / 2 % 4 = 1 := by omega
    rw [e1, e2, e3, e4]
    decide
  · grind [FiniteChains.Davis.cyc_succ, FiniteChains.Davis.Genus.gvc_even]
  · rw [← cyc_succ]
    exact gvc_congr_lt q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

include hh in
/-- The two sides of the second pair are inverse edge paths: the second half. -/
theorem bdEdge_rev_d   :
    bdEdge (gc q) (cyc (8 * q) (8 * h + 7))
      = revPath (bdEdge (gc q) (cyc (8 * q) (8 * h + 2))) := by
  refine bdEdge_rev (gc q) ?_ ?_ ?_
  · refine gec_congr_lt q (by omega) (by omega) (by omega) (by omega) ?_
    have e1 : (8 * h + 7) % 2 = 1 := by omega
    have e2 : (8 * h + 7) / 2 % 4 = 3 := by omega
    have e3 : (8 * h + 2) % 2 = 0 := by omega
    have e4 : (8 * h + 2) / 2 % 4 = 1 := by omega
    rw [e1, e2, e3, e4]
    decide
  · rw [← cyc_succ]
    exact gvc_congr_lt q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [← cyc_succ]
    exact (gvc_even q (k := 8 * h + 7 + 1) (by omega)).trans
      (gvc_even q (k := 8 * h + 2) (by omega)).symm

include hh in
/-- **The side `4h+2` of the polygon is the side `4h` reversed.** -/
theorem gPath_rev_a   :
    gPath q (8 * h + 4) = revPath (gPath q (8 * h)) := by
  simp_all [pPath, revPath, bdEdge_rev_a, bdEdge_rev_b]

include hh in
/-- **The side `4h+3` of the polygon is the side `4h+1` reversed.** -/
theorem gPath_rev_b   :
    gPath q (8 * h + 6) = revPath (gPath q (8 * h + 2)) := by
  simp_all [pPath, revPath, bdEdge_rev_c, bdEdge_rev_d]

/-! ### The classes of the sides in the fundamental group -/

/-- The class of the side of the polygon starting at an even position. -/
def gcl {m : ℕ} (hm : m % 2 = 0)  :=
  Pi1.mk ⟨gPath q m, isPath_gPath q hm⟩

/-- The class of the first `8n` sides of the polygon. -/
def bcl   :=
  Pi1.mk ⟨bdPath (gc q) (8 * n), isPath_bdPath8 q n⟩





variable (x : ℕ × Bool)
/-- The generators of the block: the side `4h` (for `i = false`) and the side `4h+1`
(for `i = true`) of the polygon. -/
theorem gIdx_even  : (8 * x.1 + (if x.2 then 2 else 0)) % 2 = 0 := by
  grind

def gGen   :=
  gcl q (m := 8 * x.1 + (if x.2 then 2 else 0)) (gIdx_even x)

/-- The sides of the block of the genus `h`, concatenated. -/
abbrev gBlock   :=
  ((gPath q (8 * n) ++ gPath q (8 * n + 2)) ++ gPath q (8 * n + 4)) ++ gPath q (8 * n + 6)

theorem bdPath_block  :
    bdPath (gc q) (8 * (n + 1)) = bdPath (gc q) (8 * n) ++ gBlock q n := by
  classical grind [FiniteChains.Davis.bdPath_add_two, List.append_assoc]

theorem bcl_succ  (hn : n < q) :
    bcl q (n + 1) = bcl q n * (gGen q (n, false) * gGen q (n, true)
      * (gGen q (n, false))⁻¹ * (gGen q (n, true))⁻¹) := by
  aesop (add simp [gPath_rev_a, gPath_rev_b, bcl, bdPath_block])

/-- **The class of the first `n` blocks of the boundary is the product of the first `n`
commutators.** -/
theorem bcl_eq_commWord {n : ℕ} (hn : n ≤ q) :
    bcl q n = commWord (gGen q) (genPairs n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hlt : n < q := by omega
      have hpairs : genPairs (n + 1) = genPairs n ++ [((n, false), (n, true))] := by
        simp [genPairs, List.range_succ]
      rw [bcl_succ q n hlt, ih (by omega), hpairs, commWord_append, commWord_cons, commWord_nil,
        mul_one]

/-! ### The filling -/

/-- **The loop of the distinguished generator `(h, i)` of the block**: the side `4h + i` of the
polygon, traversed once. -/
def gSig   :=
  gPath q (8 * (x.1 % q) + (if x.2 then 2 else 0))

theorem gSig_eq  :
    gSig q x = gPath q (8 * (x.1 % q) + (if x.2 then 2 else 0)) := rfl

omit [NeZero q] in
abbrev gSig_even   :=
  FiniteChains.Davis.Genus.gIdx_even (x.1 % q, x.2)

theorem isPath_gSig  :
    IsPath (sdCx (gc q)).src (sdCx (gc q)).tgt (gSig q x) (gBase q) (gBase q) :=
  isPath_gPath q (gSig_even q x)

theorem cls_gSig {x : ℕ × Bool} (hx : x.1 < q) :
    Pi1.mk (⟨gSig q x, isPath_gSig q x⟩ : Loop (sdCx (gc q)) (gBase q)) = gGen q x :=
  pi1_mk_congr _ _ (by rw [gSig_eq, Nat.mod_eq_of_lt hx])

/-- **The surface relator is filled**: the product of the commutators of the classes of the
loops of the distinguished generators is trivial in the fundamental group of the surface of
genus `q`. -/
theorem genus_hfilling :
    commWord (fun x => Pi1.mk (⟨gSig q x, isPath_gSig q x⟩ : Loop (sdCx (gc q)) (gBase q)))
      (genPairs q) = 1 := by
  have hstep : ∀ p ∈ genPairs q,
      Pi1.mk (⟨gSig q p.1, isPath_gSig q p.1⟩ : Loop (sdCx (gc q)) (gBase q)) = gGen q p.1 ∧
      Pi1.mk (⟨gSig q p.2, isPath_gSig q p.2⟩ : Loop (sdCx (gc q)) (gBase q)) = gGen q p.2 := by
    simp_all [genPairs, cls_gSig]
  rw [commWord_congr_on hstep, ← bcl_eq_commWord q (le_refl q), bcl]
  exact pi1_mk_eq_one _ (htpy_bdLoop_nil (gc q))

end FiniteChains.Davis.Genus



