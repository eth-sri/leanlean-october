import Mathlib.Tactic

import RequestProject.SurfaceFilling
import RequestProject.BlockSurfaceFilling

/-!
# Reversed sides of the polygon, and the classes of its boundary loops

The boundary of the polygon of `RequestProject/SurfacePoset.lean` is cut into the two-edge
crossings `bdEdge`.  This file collects the two elementary facts about them which are needed to
recognise the boundary word of a closed surface inside the fundamental group of the
subdivision:

* `FiniteChains.Davis.bdEdge_rev` — if two positions of the polygon carry the same edge of the
  surface with opposite orientations, then the crossing at one of them is the reverse of the
  crossing at the other; this is what "the sides are glued in pairs with reversed orientation"
  means at the level of paths;
* `FiniteChains.Davis.pPath`, `FiniteChains.Davis.bdPath_add_two` — the boundary path cut into
  blocks of two positions, i.e. into whole sides of the polygon.

It also records the elementary computation rules for the classes of loops in the fundamental
group (`FiniteChains.Davis.pi1_mk_append`, `pi1_mk_rev`, `pi1_mk_eq_one`) and the fact that a
product of commutators only depends on the values of its function on the pairs which occur
(`FiniteChains.Davis.commWord_congr_on`).
-/

namespace FiniteChains.Davis


open RACG Mirror Comb Cell


/-! ### Classes of loops -/

section

variable {X : Complex2.{u}} {a : X.V}





theorem pi1_mk_congr {p p' : List (X.E × Bool)} (hp : IsPath X.src X.tgt p a a)
    (hp' : IsPath X.src X.tgt p' a a) (e : p = p') :
    Pi1.mk (⟨p, hp⟩ : Loop X a) = Pi1.mk ⟨p', hp'⟩ := by
  subst e; rfl

theorem pi1_mk_eq_one {p : List (X.E × Bool)} (hp : IsPath X.src X.tgt p a a)
    (h : Htpy X a a p []) : Pi1.mk (⟨p, hp⟩ : Loop X a) = 1 :=
  Quotient.sound h

end

/-- A product of commutators only depends on the values of its function at the elements of the
pairs which occur in the list. -/
theorem commWord_congr_on {ι : Type*} {G : Type*} [Group G] {f g : ι → G}
    {ps : List (ι × ι)} (h : ∀ p ∈ ps, f p.1 = g p.1 ∧ f p.2 = g p.2) :
    commWord f ps = commWord g ps := by
  classical
  induction ps <;> simp_all [List.mem_cons_self, FiniteChains.Davis.commWord_cons, List.mem_cons_of_mem]

/-! ### Congruences for the crossings -/











section

variable {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)

/-- **A side glued to another one with reversed orientation gives the reversed crossing.** -/
theorem bdEdge_rev {p p' : Fin M} (he : ec p' = ec p) (hv : vc p' = vc (p + 1))
    (hv' : vc (p' + 1) = vc p) : bdEdge hc p' = revPath (bdEdge hc p) := by
  aesop (add simp [cE, cV, bdEdge])

/-! ### The boundary path cut into sides -/

variable (m : ℕ)
/-- The crossing of the two positions `m` and `m+1`, i.e. of a whole side of the polygon. -/
def pPath   :=
  bdEdge hc (cyc M m) ++ bdEdge hc (cyc M (m + 1))

theorem pPath_eq  :
    pPath hc m = bdEdge hc (cyc M m) ++ bdEdge hc (cyc M (m + 1)) := rfl

theorem bdPath_succ  : bdPath hc (m + 1) = bdPath hc m ++ bdEdge hc (cyc M m) := rfl

theorem bdPath_add_two  : bdPath hc (m + 2) = bdPath hc m ++ pPath hc m := by simp_all [bdPath_succ, pPath_eq]

end

end FiniteChains.Davis

