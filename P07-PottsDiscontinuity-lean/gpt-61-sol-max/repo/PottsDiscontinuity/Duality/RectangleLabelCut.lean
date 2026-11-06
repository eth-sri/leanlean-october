/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import PottsDiscontinuity.Duality.RectangleDualPotential

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial


noncomputable section

/-- The two endpoint labels of an original rectangle edge, in the actual
square-lattice bond coordinates. -/
def rectangleLabelCutEndpointStates (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (e : rectanglePrimalEdgeCarrier a w h)  :=
  let b := rectanglePrimalEdgeBond a w h e
  (σ ⟨b.source, rectanglePrimalEdgeBond_endpoints_mem_public a w h e |>.1⟩,
    σ ⟨b.target, rectanglePrimalEdgeBond_endpoints_mem_public a w h e |>.2⟩)

/-- Original rectangle edges on which the two actual endpoint labels differ. -/
def rectangleLabelCutEdgeCarrier (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) : Finset (rectanglePrimalEdgeCarrier a w h) := by
  classical
  exact Finset.univ.filter fun e =>
    (rectangleLabelCutEndpointStates a w h σ e).1 !=
      (rectangleLabelCutEndpointStates a w h σ e).2

@[simp] theorem mem_rectangleLabelCutEdgeCarrier (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (e : rectanglePrimalEdgeCarrier a w h) :
    e ∈ rectangleLabelCutEdgeCarrier a w h σ ↔
      (rectangleLabelCutEndpointStates a w h σ e).1 !=
        (rectangleLabelCutEndpointStates a w h σ e).2 := by
  simp [rectangleLabelCutEdgeCarrier]

/-- Regard the complementary primal configuration as the closed cut edges, so
the exact finite FK dual complement opens precisely those crossing edges. -/
def rectangleLabelCutDualConfiguration (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool)  :=
  rectangleDualConfiguration a w h
    (Finset.univ \ rectangleLabelCutEdgeCarrier a w h σ)

abbrev rectangleLabelCutDualGraph (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) :=
  openGraph (rectangleDualGraph a w h) (rectangleLabelCutDualConfiguration a w h σ)

/-- An actual dual edge is open in the cut configuration exactly when its
retained original primal edge has differently labelled endpoints. -/
theorem rectangleLabelCutDual_adj_iff (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (u v : RectangleDualVertex a w h) :
    (rectangleLabelCutDualGraph a w h σ).Adj u v ↔
      ∃ e : RectangleDualEdgeCarrier a w h,
        e.primalEdge ∈ rectangleLabelCutEdgeCarrier a w h σ ∧
          s(u, v) = rectangleDualCarrierPair a w h e := by
  
  rw [openGraph_adj]
  constructor
  · rintro ⟨g, hg, hgv⟩
    let e := (rectangleDualGraphEdgeEquiv a w h).symm g
    have hge : rectangleDualGraphEdgeEquiv a w h e = g := Equiv.apply_symm_apply _ _
    
    
    have hpair :  rectangleDualGraphEdgeEquiv a w h e  =
        rectangleDualCarrierPair a w h e := rfl
    refine ⟨e, (by
                  have hmem := (mem_rectangleDualConfiguration a w h
                    (Finset.univ \ rectangleLabelCutEdgeCarrier a w h σ) e).mp (by
                                                                                  rw [hge]
                                                                                  exact hg)
                  simpa using hmem), ?_⟩
    simp_all
  · rintro ⟨e, hcut, hpair⟩
    
    
    refine ⟨rectangleDualGraphEdgeEquiv a w h e,  by
                                                    apply (mem_rectangleDualConfiguration a w h
                                                      (Finset.univ \ rectangleLabelCutEdgeCarrier a w h σ) e).mpr
                                                    simpa using hcut , ?_⟩
    
    exact hpair.symm

/-- The four edge disagreements around a square have even total parity. -/
theorem fourBoolCut_even (b₀ b₁ b₂ b₃ : Bool) :
    Even ((if b₀ != b₁ then 1 else 0) + (if b₁ != b₃ then 1 else 0) +
      (if b₃ != b₂ then 1 else 0) +  if b₂ != b₀ then 1 else 0 ) := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> norm_num

/-- Along a finite row of Bool labels, the number of flips is odd exactly
when the endpoint labels differ. -/
theorem rectangleBoolFlipCount_odd_iff (f : ℕ → Bool) (n : ℕ) :
    Odd (∑ i ∈ Finset.range n, if f i != f (i + 1) then 1 else 0) ↔
      f 0 != f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.odd_add, ih]
    cases f 0 <;> cases f n <;> cases f (n + 1) <;> norm_num

def rectangleClampedBottomLabel (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (i : ℕ) : Bool :=
  σ ⟨(a.1 + ((min i w : ℕ) : ℤ), a.2), by
    rw [mem_latticeRectangle]
    constructor <;> constructor <;> omega⟩

/-- The actual bottom row, extended constantly past its right endpoint, has
an odd number of flips when its two side endpoint labels differ. -/
theorem rectangleBottomRow_flipCount_odd (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool)
    (hends : σ ⟨(a.1, a.2), by rw [mem_latticeRectangle]
                               simp_all⟩ !=
      σ ⟨(a.1 + (w : ℤ), a.2), by rw [mem_latticeRectangle]
                                  simp_all⟩) :
    Odd (∑ i ∈ Finset.range w,
      if rectangleClampedBottomLabel a w h σ i !=
        rectangleClampedBottomLabel a w h σ (i + 1) then 1 else 0) :=  (rectangleBoolFlipCount_odd_iff
                                                                         (rectangleClampedBottomLabel a w h σ) w).2 (by
                                                                           simpa [rectangleClampedBottomLabel] using hends) 

def rectangleCutEdgeOfBond (a : LatticeVertex) (w h : ℕ)
    (b : LatticeBond) (hs : b.source ∈ latticeRectangle a w h)
    (ht : b.target ∈ latticeRectangle a w h)  :=
  rectanglePrimalBondToEdge a w h ⟨b, hs, ht⟩

theorem rectanglePrimalEdgeBond_of_rectangleCutEdgeOfBond
    (a : LatticeVertex) (w h : ℕ) (b : LatticeBond)
    (hs : b.source ∈ latticeRectangle a w h) (ht : b.target ∈ latticeRectangle a w h) :
    rectanglePrimalEdgeBond a w h (rectangleCutEdgeOfBond a w h b hs ht) = b := congrArg Subtype.val
                                                                            ((rectanglePrimalEdgeBondEquiv a w h).right_inv ⟨b, hs, ht⟩)

end

end PottsDiscontinuity.FK
