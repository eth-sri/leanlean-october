/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import PottsDiscontinuity.Duality.FiniteGraphBoundaryParity
public import PottsDiscontinuity.Duality.ReachabilityLabels
public import PottsDiscontinuity.Duality.RectangleDualBoundaryParity
public import PottsDiscontinuity.Duality.RectangleDualCutParity
public import PottsDiscontinuity.Duality.RectangleEvents

@[expose] public section

namespace PottsDiscontinuity.FK


open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial
open scoped BigOperators

noncomputable section

local instance crossingDualFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectangleDualVertex a w h) := Fintype.ofFinite _

local instance crossingDualAdjDecidable (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) :
    DecidableRel (rectangleLabelCutDualGraph a w h σ).Adj := Classical.decRel _


theorem rectangleDual_mem_expanded_iff (a : LatticeVertex) (w h : ℕ)
    (z : LatticeVertex) :
    z ∈ rectangleDualExpanded a w h ↔
      a.1 - 1 ≤ z.1 ∧ z.1 ≤ a.1 + (w : ℤ) ∧
      a.2 - 1 ≤ z.2 ∧ z.2 ≤ a.2 + (h : ℤ) := by
  rw [rectangleDualExpanded, mem_latticeRectangle]
  omega

section
variable (a : LatticeVertex) (w h : ℕ) (z : RectangleDualVertex a w h) (hx : a.1 ≤ z.1.1) (hxw : z.1.1 < a.1 + (w : ℤ))
include hx hxw
theorem bottomPort_mem_of_coords (hy : z.1.2 = a.2 - 1) :
    z ∈ rectangleDualBottomPorts a w h := by
  let i := (z.1.1 - a.1).toNat
  have hval : (rectangleDualBottomPortVertex a w h i).1 = z.1 := by
    grind [rectangleDualBottomPortVertex]
  have heq : rectangleDualBottomPortVertex a w h i = z := by
    simp_all
  rw [← heq]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩

theorem topPort_mem_of_coords (hy : z.1.2 = a.2 + (h : ℤ)) :
    z ∈ rectangleDualTopPorts a w h := by
  let i := (z.1.1 - a.1).toNat
  have hval : (rectangleDualTopPortVertex a w h i).1 = z.1 := by
    grind [rectangleDualTopPortVertex]
  have heq : rectangleDualTopPortVertex a w h i = z := by
    simp_all
  rw [← heq]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
end

theorem exists_reachable_between_of_odd_ncard_neighbor_sum
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (B T : Finset V) (hdisj : Disjoint B T)
    (heven : ∀ v, v ∉ B → v ∉ T → Even ((G.neighborSet v).ncard))
    (hodd : Odd (∑ v ∈ B, (G.neighborSet v).ncard)) :
    ∃ b ∈ B, ∃ t ∈ T, G.Reachable b t := by
  have heven' : ∀ v, v ∉ B ∪ T → Even (G.degree v) := by
    simp_all
  have hodd' : Odd (∑ v ∈ B, G.degree v) := by
    simp_all
  exact exists_reachable_between_of_odd_degree_sum G B T hdisj heven' hodd'

section
variable (a : LatticeVertex) (w h : ℕ) (σ : RectangleVertex a w h → Bool) (hleft : ∀ v : RectangleVertex a w h, v.1.1 = a.1 → σ v = true) (hright : ∀ v : RectangleVertex a w h, v.1.1 = a.1 + (w : ℤ) → σ v = false)
include hleft hright
theorem rectangleLabelCutDual_outside_ports_degree_even
    (v : RectangleDualVertex a w h)
    (hvB : v ∉ rectangleDualBottomPorts a w h)
    (hvT : v ∉ rectangleDualTopPorts a w h) :
    Even (((rectangleLabelCutDualGraph a w h σ).neighborSet v).ncard) := by
  rcases v with ⟨⟨x,y⟩, hvv⟩
  rcases (rectangleDual_mem_expanded_iff a w h (x,y)).mp hvv with ⟨hxl, hxr, hyl, hyr⟩
  by_cases hxleft : x = a.1 - 1
  · have hz := (rectangleDualLeftColumn_isolated a w h σ hleft ⟨(x,y),hvv⟩ hxleft).degree_eq_zero
    rw [← SimpleGraph.ncard_neighborSet] at hz
    grind
  · by_cases hxright : x = a.1 + (w : ℤ)
    · have hz := (rectangleDualRightColumn_isolated a w h σ hright ⟨(x,y),hvv⟩ hxright).degree_eq_zero
      simp_all
      grind
    · have hx : a.1 ≤ x := by omega
      have hxw : x < a.1 + (w : ℤ) := by omega
      by_cases hybottom : y = a.2 - 1
      · have hmem := bottomPort_mem_of_coords a w h ⟨(x,y),hvv⟩ hx hxw hybottom
        grind
      · by_cases hytop : y = a.2 + (h : ℤ)
        · have hmem := topPort_mem_of_coords a w h ⟨(x,y),hvv⟩ hx hxw hytop
          grind
        · have hpar := rectangleLabelCutDual_interior_degree_even a w h σ x y hx hxw (by omega) (by omega)
          rw [← SimpleGraph.ncard_neighborSet] at hpar
          tauto

theorem rectangleLabelCutDual_bottom_ports_ncard_odd
     :
    Odd (∑ v ∈ rectangleDualBottomPorts a w h,
      ((rectangleLabelCutDualGraph a w h σ).neighborSet v).ncard) := by
  let vl : RectangleVertex a w h := ⟨(a.1, a.2), by rw [mem_latticeRectangle]; omega⟩
  let vr : RectangleVertex a w h := ⟨(a.1 + (w : ℤ), a.2), by rw [mem_latticeRectangle]; omega⟩
  have hends : σ vl != σ vr := by grind
  have hoddDegree := rectangleDualBottomPortsDegreeSum_odd a w h σ
    (by omega)
  simp_rw [← SimpleGraph.ncard_neighborSet] at hoddDegree
  omega

theorem rectangleLabelCutDual_bottom_top_reachable
     :
    ∃ b ∈ rectangleDualBottomPorts a w h,
      ∃ t ∈ rectangleDualTopPorts a w h,
        (rectangleLabelCutDualGraph a w h σ).Reachable b t := by
  have heven : ∀ v, v ∉ rectangleDualBottomPorts a w h →
      v ∉ rectangleDualTopPorts a w h →
      Even (((rectangleLabelCutDualGraph a w h σ).neighborSet v).ncard) := by
    grind [rectangleLabelCutDual_outside_ports_degree_even]
  exact @exists_reachable_between_of_odd_ncard_neighbor_sum
    (RectangleDualVertex a w h) (crossingDualFintype a w h)
    (rectangleLabelCutDualGraph a w h σ) (Classical.decEq _)
    (crossingDualAdjDecidable a w h σ)
    (rectangleDualBottomPorts a w h) (rectangleDualTopPorts a w h)
    (rectangleDualBottomTopPorts_disjoint a w h) heven (rectangleLabelCutDual_bottom_ports_ncard_odd a w h σ hleft hright)
end


section
variable (a : LatticeVertex) (w h : ℕ)
def rectanglePrimalLeftVertices  : Finset (RectangleVertex a w h) :=
  Finset.univ.filter fun v => v.1.1 = a.1

def rectanglePrimalRightVertices  : Finset (RectangleVertex a w h) :=
  Finset.univ.filter fun v => v.1.1 = a.1 + (w : ℤ)
end

section
variable (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
theorem rectangle_labelCutEdge_closed_of_actualReachability
    (L : Finset (RectangleVertex a w h))
    (e : rectanglePrimalEdgeCarrier a w h)
    (he : e ∈ rectangleLabelCutEdgeCarrier a w h (actualReachabilityLabel
      (rectangleGraph a w h) A L)) : e ∉ A := by
  have hstates := (mem_rectangleLabelCutEdgeCarrier a w h
    (actualReachabilityLabel (rectangleGraph a w h) A L) e).mp he
  let b := rectanglePrimalEdgeBond a w h e
  let p := e.1.out
  have hrepr : s(p.1,p.2) = e.1 := Quot.out_eq _
  have hG : s(p.1,p.2) ∈ (rectangleGraph a w h).edgeSet := by aesop
  intro hA
  have hpq : (⟨s(p.1,p.2),hG⟩ : (rectangleGraph a w h).edgeSet) ∈ A := by
    aesop
  have hlabels := actualEdge_mem_configuration_implies_labels_eq
    (rectangleGraph a w h) A L hG hpq
  have hbpair : b.toSym2 = s(p.1.val,p.2.val) := by
    rw [rectanglePrimalEdgeBond_toSym2_public, ← hrepr]
    rfl
  rcases Sym2.eq_iff.mp hbpair with ⟨hs,ht⟩ | ⟨hs,ht⟩ <;> grind [actualReachabilityLabel, rectangleGraph, rectangleLabelCutEndpointStates]

theorem rectangleLabelCutDualConfiguration_subset_actualDual
    (hclosed : ∀ e ∈ rectangleLabelCutEdgeCarrier a w h
      (actualReachabilityLabel (rectangleGraph a w h) A
        (rectanglePrimalLeftVertices a w h)), e ∉ A) :
    rectangleLabelCutDualConfiguration a w h
      (actualReachabilityLabel (rectangleGraph a w h) A
        (rectanglePrimalLeftVertices a w h)) ⊆
      rectangleDualConfiguration a w h A := by
  apply Finset.map_subset_map.mpr
  intro d hd
  have hdclosed : d.primalEdge ∈ rectangleLabelCutEdgeCarrier a w h
      (actualReachabilityLabel (rectangleGraph a w h) A
        (rectanglePrimalLeftVertices a w h)) := by
    have hnot := (mem_rectangleDualComplementEquiv a w h
      (Finset.univ \ rectangleLabelCutEdgeCarrier a w h
        (actualReachabilityLabel (rectangleGraph a w h) A
          (rectanglePrimalLeftVertices a w h))) d).mp hd
    grind
  exact (mem_rectangleDualComplementEquiv a w h A d).mpr (hclosed d.primalEdge hdclosed)


theorem rectangleDualBottomTop_of_no_primal_horizontal_crossing
    (hnoCross : A ∉ rectangleHorizontalCrossingEvent a w h) :
    ∃ b ∈ rectangleDualBottomPorts a w h,
      ∃ t ∈ rectangleDualTopPorts a w h,
        ActualConnected (rectangleDualGraph a w h)
          (rectangleDualConfiguration a w h A) b t := by
  let L := rectanglePrimalLeftVertices a w h
  let R := rectanglePrimalRightVertices a w h
  have hno : ∀ u, u ∈ L → ∀ v, v ∈ R →
      ¬ ActualConnected (rectangleGraph a w h) A u v := by
    intro u hu v hv huv
    apply hnoCross
    refine ⟨u, v, ?_, ?_, huv⟩
    · apply Finset.mem_filter.mpr
      exact ⟨u.property, (Finset.mem_filter.mp hu).2⟩
    · apply Finset.mem_filter.mpr
      exact ⟨v.property, (Finset.mem_filter.mp hv).2⟩
  have hleft : ∀ v : RectangleVertex a w h, v.1.1 = a.1 →
      actualReachabilityLabel (rectangleGraph a w h) A L v = true := by
    intro v hx
    apply actualReachabilityLabel_eq_true_of_mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have hright : ∀ v : RectangleVertex a w h,
      v.1.1 = a.1 + (w : ℤ) →
      actualReachabilityLabel (rectangleGraph a w h) A L v = false := by
    intro v hx
    apply actualReachabilityLabel_eq_false_of_no_seed_path
      (rectangleGraph a w h) A L R hno
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  obtain ⟨b, hb, t, ht, hcut⟩ :=
    rectangleLabelCutDual_bottom_top_reachable a w h
      (actualReachabilityLabel (rectangleGraph a w h) A L) hleft hright
  have hclosed : ∀ e ∈ rectangleLabelCutEdgeCarrier a w h
      (actualReachabilityLabel (rectangleGraph a w h) A L), e ∉ A := by
    grind [rectangle_labelCutEdge_closed_of_actualReachability]
  have hactual :=
    actualConnected_mono (rectangleLabelCutDualConfiguration_subset_actualDual a w h A hclosed) hcut
  grind
end

end
end PottsDiscontinuity.FK
