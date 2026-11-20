/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleDualCarrier
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

/-- A finite dual potential with the wired exterior normalized to zero. -/
abbrev RectangleExteriorPotential (a : LatticeVertex) (w h : ℕ) :=
  {φ : RectangleDualVertex a w h → ℝ //
    ∀ z, z.1 ∈ rectangleDualBoundary a w h → φ z = 0}

def rectangleExtendedPotential {a : LatticeVertex} {w h : ℕ}
    (φ : RectangleExteriorPotential a w h) (z : LatticeVertex) : ℝ :=
  if hz : z ∈ rectangleDualExpanded a w h then φ.1 ⟨z, hz⟩ else 0

@[simp] theorem rectangleExtendedPotential_of_mem {a : LatticeVertex} {w h : ℕ}
    (φ : RectangleExteriorPotential a w h) {z : LatticeVertex}
    (hz : z ∈ rectangleDualExpanded a w h) :
    rectangleExtendedPotential φ z = φ.1 ⟨z, hz⟩ := by
  simp [rectangleExtendedPotential, hz]

/-- Primal curl of a dual potential: above-minus-below horizontally and
left-minus-right vertically. -/
def rectangleCurlFlow {a : LatticeVertex} {w h : ℕ}
    (φ : RectangleExteriorPotential a w h) (b : LatticeBond) : ℝ :=
  match b.axis with
  | .horizontal => rectangleExtendedPotential φ (b.faceBase true) -
      rectangleExtendedPotential φ (b.faceBase false)
  | .vertical => rectangleExtendedPotential φ (b.faceBase false) -
      rectangleExtendedPotential φ (b.faceBase true)

variable {a : LatticeVertex} {w h : ℕ} (φ : RectangleExteriorPotential a w h)

lemma extended_zero {z : LatticeVertex} (hz : z ∉ rectangleDualInterior a w h) : rectangleExtendedPotential φ z = 0 := by
  unfold rectangleExtendedPotential; split <;> rename_i he
  · exact φ.property _ (Finset.mem_filter.mpr ⟨he,hz⟩)
  · rfl

lemma curl_zero_outside {b : LatticeBond} (hb : ¬ (b.source ∈ latticeRectangle a w h ∧ b.target ∈ latticeRectangle a w h)) :
    rectangleCurlFlow φ b = 0 := by
  have hz (s : Bool) : b.faceBase s ∉ rectangleDualInterior a w h := by
    rintro hin; have := (Finset.mem_filter.mp hin).2; apply hb
    rcases b with ⟨⟨x,y⟩,ax⟩; cases ax <;> cases s <;>
      simp_all [LatticeBond.faceBase,LatticeBond.source,LatticeBond.target,mem_latticeRectangle] <;> omega
  unfold rectangleCurlFlow; cases b.axis <;> simp [extended_zero φ (hz _)]

end PottsDiscontinuity.FK
