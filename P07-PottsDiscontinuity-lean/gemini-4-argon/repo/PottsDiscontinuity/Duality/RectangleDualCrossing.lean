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


private theorem bottomPort_mem_of_coords (a : LatticeVertex) (w h : ℕ)
    (z : RectangleDualVertex a w h)
    (hx : a.1 ≤ z.1.1) (hxw : z.1.1 < a.1 + (w : ℤ))
    (hy : z.1.2 = a.2 - 1) :
    z ∈ rectangleDualBottomPorts a w h := by
  let i := (z.1.1 - a.1).toNat
  have hi : i < w := by omega
  have heq : rectangleDualBottomPortVertex a w h i = z :=
    Subtype.ext (Prod.ext (by simp [rectangleDualBottomPortVertex, i, Nat.min_eq_left hi.le]; omega)
      (by simp [rectangleDualBottomPortVertex, hy]))
  exact heq ▸ Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

private theorem topPort_mem_of_coords (a : LatticeVertex) (w h : ℕ)
    (z : RectangleDualVertex a w h)
    (hx : a.1 ≤ z.1.1) (hxw : z.1.1 < a.1 + (w : ℤ))
    (hy : z.1.2 = a.2 + (h : ℤ)) :
    z ∈ rectangleDualTopPorts a w h := by
  let i := (z.1.1 - a.1).toNat
  have hi : i < w := by omega
  have heq : rectangleDualTopPortVertex a w h i = z :=
    Subtype.ext (Prod.ext (by simp [rectangleDualTopPortVertex, i, Nat.min_eq_left hi.le]; omega)
      (by simp [rectangleDualTopPortVertex, hy]))
  exact heq ▸ Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

theorem exists_reachable_between_of_odd_ncard_neighbor_sum
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (B T : Finset V) (hdisj : Disjoint B T)
    (heven : ∀ v, v ∉ B → v ∉ T → Even ((G.neighborSet v).ncard))
    (hodd : Odd (∑ v ∈ B, (G.neighborSet v).ncard)) :
    ∃ b ∈ B, ∃ t ∈ T, G.Reachable b t :=
  exists_reachable_between_of_odd_degree_sum G B T hdisj
    (fun v hv => by
      simpa only [← SimpleGraph.ncard_neighborSet] using
        heven v (fun hb => hv (Finset.mem_union_left T hb)) (fun ht => hv (Finset.mem_union_right B ht)))
    (by simpa only [SimpleGraph.ncard_neighborSet] using hodd)

theorem rectangleLabelCutDual_outside_ports_degree_even
    (a : LatticeVertex) (w h : ℕ) (σ : RectangleVertex a w h → Bool)
    (hleft : ∀ v : RectangleVertex a w h, v.1.1 = a.1 → σ v = true)
    (hright : ∀ v : RectangleVertex a w h,
      v.1.1 = a.1 + (w : ℤ) → σ v = false)
    (v : RectangleDualVertex a w h)
    (hvB : v ∉ rectangleDualBottomPorts a w h)
    (hvT : v ∉ rectangleDualTopPorts a w h) :
    Even (((rectangleLabelCutDualGraph a w h σ).neighborSet v).ncard) := by
  rcases v with ⟨⟨x, y⟩, hvv⟩
  rcases (mem_rectangleDualExpanded_iff a w h (x, y)).mp hvv with ⟨hxl, hxr, hyl, hyr⟩
  by_cases hxleft : x = a.1 - 1
  · rw [SimpleGraph.ncard_neighborSet,
      (rectangleDualLeftColumn_isolated a w h σ hleft ⟨(x, y), hvv⟩ hxleft).degree_eq_zero]
    exact ⟨0, rfl⟩
  · by_cases hxright : x = a.1 + (w : ℤ)
    · rw [SimpleGraph.ncard_neighborSet,
        (rectangleDualRightColumn_isolated a w h σ hright ⟨(x, y), hvv⟩ hxright).degree_eq_zero]
      exact ⟨0, rfl⟩
    · by_cases hybottom : y = a.2 - 1
      · exact (hvB (bottomPort_mem_of_coords a w h ⟨(x, y), hvv⟩ (by dsimp; omega) (by dsimp; omega) hybottom)).elim
      · by_cases hytop : y = a.2 + (h : ℤ)
        · exact (hvT (topPort_mem_of_coords a w h ⟨(x, y), hvv⟩ (by dsimp; omega) (by dsimp; omega) hytop)).elim
        · have hpar := rectangleLabelCutDual_interior_degree_even a w h σ x y
            (by omega) (by omega) (by omega) (by omega)
          rwa [← SimpleGraph.ncard_neighborSet] at hpar

theorem rectangleLabelCutDual_bottom_ports_ncard_odd
    (a : LatticeVertex) (w h : ℕ) (σ : RectangleVertex a w h → Bool)
    (hleft : ∀ v : RectangleVertex a w h, v.1.1 = a.1 → σ v = true)
    (hright : ∀ v : RectangleVertex a w h,
      v.1.1 = a.1 + (w : ℤ) → σ v = false) :
    Odd (∑ v ∈ rectangleDualBottomPorts a w h,
      ((rectangleLabelCutDualGraph a w h σ).neighborSet v).ncard) := by
  have hoddDegree := rectangleDualBottomPortsDegreeSum_odd a w h σ (by
    rw [hleft _ rfl, hright _ rfl]; rfl)
  simpa only [← SimpleGraph.ncard_neighborSet] using hoddDegree

theorem rectangleLabelCutDual_bottom_top_reachable
    (a : LatticeVertex) (w h : ℕ) (σ : RectangleVertex a w h → Bool)
    (hleft : ∀ v : RectangleVertex a w h, v.1.1 = a.1 → σ v = true)
    (hright : ∀ v : RectangleVertex a w h,
      v.1.1 = a.1 + (w : ℤ) → σ v = false) :
    ∃ b ∈ rectangleDualBottomPorts a w h,
      ∃ t ∈ rectangleDualTopPorts a w h,
        (rectangleLabelCutDualGraph a w h σ).Reachable b t :=
  @exists_reachable_between_of_odd_ncard_neighbor_sum
    (RectangleDualVertex a w h) (crossingDualFintype a w h)
    (rectangleLabelCutDualGraph a w h σ) (Classical.decEq _)
    (crossingDualAdjDecidable a w h σ)
    (rectangleDualBottomPorts a w h) (rectangleDualTopPorts a w h)
    (rectangleDualBottomTopPorts_disjoint a w h)
    (rectangleLabelCutDual_outside_ports_degree_even a w h σ hleft hright)
    (rectangleLabelCutDual_bottom_ports_ncard_odd a w h σ hleft hright)

def rectanglePrimalLeftVertices (a : LatticeVertex) (w h : ℕ) : Finset (RectangleVertex a w h) :=
  Finset.univ.filter fun v => v.1.1 = a.1

def rectanglePrimalRightVertices (a : LatticeVertex) (w h : ℕ) : Finset (RectangleVertex a w h) :=
  Finset.univ.filter fun v => v.1.1 = a.1 + (w : ℤ)

theorem rectangle_labelCutEdge_closed_of_actualReachability
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (L : Finset (RectangleVertex a w h))
    (e : rectanglePrimalEdgeCarrier a w h)
    (he : e ∈ rectangleLabelCutEdgeCarrier a w h (actualReachabilityLabel
      (rectangleGraph a w h) A L)) : e ∉ A := by
  have hstates := (mem_rectangleLabelCutEdgeCarrier a w h
    (actualReachabilityLabel (rectangleGraph a w h) A L) e).mp he
  let b := rectanglePrimalEdgeBond a w h e
  let p := e.1.out
  have hrepr : s(p.1, p.2) = e.1 := Quot.out_eq _
  have hG : s(p.1, p.2) ∈ (rectangleGraph a w h).edgeSet := hrepr ▸ e.2
  intro hA
  have hlabels := actualEdge_mem_configuration_implies_labels_eq
    (rectangleGraph a w h) A L hG
    (by rwa [show (⟨s(p.1, p.2), hG⟩ : (rectangleGraph a w h).edgeSet) = e from Subtype.ext hrepr])
  have hbpair : b.toSym2 = s(p.1.val, p.2.val) := by
    dsimp [b]; rw [rectanglePrimalEdgeBond_toSym2_public, ← hrepr]; rfl
  rcases Sym2.eq_iff.mp hbpair with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
    simp [rectangleLabelCutEndpointStates, b, hs, ht, hlabels] at hstates

theorem rectangleLabelCutDualConfiguration_subset_actualDual
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (σ : RectangleVertex a w h → Bool)
    (hclosed : ∀ e ∈ rectangleLabelCutEdgeCarrier a w h σ, e ∉ A) :
    rectangleLabelCutDualConfiguration a w h σ ⊆
      rectangleDualConfiguration a w h A := by
  classical
  refine Finset.map_subset_map.mpr fun d hd => (mem_rectangleDualComplementEquiv a w h A d).mpr (hclosed _ ?_)
  have hnot := (mem_rectangleDualComplementEquiv a w h
    (Finset.univ \ rectangleLabelCutEdgeCarrier a w h σ) d).mp hd
  simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using hnot

theorem rectangleDualBottomTop_of_no_primal_horizontal_crossing
    (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h))
    (hnoCross : A ∉ rectangleHorizontalCrossingEvent a w h) :
    ∃ b ∈ rectangleDualBottomPorts a w h,
      ∃ t ∈ rectangleDualTopPorts a w h,
        ActualConnected (rectangleDualGraph a w h)
          (rectangleDualConfiguration a w h A) b t := by
  let L := rectanglePrimalLeftVertices a w h
  let R := rectanglePrimalRightVertices a w h
  obtain ⟨b, hb, t, ht, hcut⟩ := rectangleLabelCutDual_bottom_top_reachable a w h
    (actualReachabilityLabel (rectangleGraph a w h) A L)
    (fun v hx => actualReachabilityLabel_eq_true_of_mem _ _ _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩))
    (fun v hx => actualReachabilityLabel_eq_false_of_no_seed_path (rectangleGraph a w h) A L R
      (fun u hu v hv huv => hnoCross ⟨u, v,
        Finset.mem_filter.mpr ⟨u.property, (Finset.mem_filter.mp hu).2⟩,
        Finset.mem_filter.mpr ⟨v.property, (Finset.mem_filter.mp hv).2⟩, huv⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩))
  exact ⟨b, hb, t, ht, actualConnected_mono
    (rectangleLabelCutDualConfiguration_subset_actualDual a w h A _
      (rectangle_labelCutEdge_closed_of_actualReachability a w h A L)) hcut⟩

end
end PottsDiscontinuity.FK
