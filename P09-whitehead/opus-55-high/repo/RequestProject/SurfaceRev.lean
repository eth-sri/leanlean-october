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

universe u

/-! ### Classes of loops -/

section Pi1Calc

variable {X : Complex2.{u}} {a : X.V}

theorem pi1_mk_append hp
    hq hpq :
    Pi1.mk (⟨p ++ q, hpq⟩ : Loop X a) = Pi1.mk ⟨p, hp⟩ * Pi1.mk ⟨q, hq⟩ := rfl

theorem pi1_mk_rev hp
    hr :
    Pi1.mk (⟨revPath p, hr⟩ : Loop X a) = (Pi1.mk ⟨p, hp⟩)⁻¹ := rfl

theorem pi1_mk_congr hp
    hp' (e : p = p') :
    Pi1.mk (⟨p, hp⟩ : Loop X a) = Pi1.mk ⟨p', hp'⟩ := by
  simp_all

theorem pi1_mk_eq_one hp
    (h : Htpy X a a p []) : Pi1.mk (⟨p, hp⟩ : Loop X a) = 1 :=
  Quotient.sound h

end Pi1Calc

/-- A product of commutators only depends on the values of its function at the elements of the
pairs which occur in the list. -/
theorem commWord_congr_on {ι : Type*} {G} [Group G] {f g : ι → G}
    {ps} (h : ∀ p ∈ ps, f p.1 = g p.1 ∧ f p.2 = g p.2) :
    commWord f ps = commWord g ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      cases' h p (List.mem_cons_self ..) with h1 h2
      rw [commWord_cons, commWord_cons, h1, h2, ih (by grind)]

/-! ### Congruences for the crossings -/

section Congr

variable {P : Type u} [PartialOrder P] [DecidableEq P]



end Congr

section Rev

variable {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)

/-- **A side glued to another one with reversed orientation gives the reversed crossing.** -/
theorem bdEdge_rev {p p'} (he : ec p' = ec p) (hv : vc p' = vc (p + 1))
    (hv' : vc (p' + 1) = vc p) : bdEdge hc p' = revPath (bdEdge hc p) := by
  have hE : cE hc p' = cE hc p := congrArg (fun k => toS vc ec hc (bed k)) he
  have hV : cV hc p' = cV hc (p + 1) := congrArg (fun k => toS vc ec hc (vtx k)) hv
  have hV' : cV hc (p' + 1) = cV hc p := congrArg (fun k => toS vc ec hc (vtx k)) hv'
  simp_all [bdEdge, revPath_append, revPath_edgeHop, revPath_edgeHopRev]

/-! ### The boundary path cut into sides -/

/-- The crossing of the two positions `m` and `m+1`, i.e. of a whole side of the polygon. -/
def pPath (m : ℕ) : List ((sdCx hc).E × Bool) :=
  bdEdge hc (cyc M m) ++ bdEdge hc (cyc M (m + 1))

theorem pPath_eq m :
    pPath hc m = bdEdge hc (cyc M m) ++ bdEdge hc (cyc M (m + 1)) := rfl

theorem bdPath_succ m : bdPath hc (m + 1) = bdPath hc m ++ bdEdge hc (cyc M m) := rfl

theorem bdPath_add_two m : bdPath hc (m + 2) = bdPath hc m ++ pPath hc m := by
  grind [bdPath_succ, pPath_eq, List.append_assoc]
