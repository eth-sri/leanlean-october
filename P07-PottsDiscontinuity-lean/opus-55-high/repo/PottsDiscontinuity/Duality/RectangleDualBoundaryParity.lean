/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import PottsDiscontinuity.Duality.RectangleLabelCutIncidence

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial
open scoped BigOperators

noncomputable section

section
variable (a : LatticeVertex) (w h : ℕ)
/-- The dual port just below the original bottom edge indexed by its horizontal
bond coordinate. `i` is clamped only so the auxiliary vertex is total; in the
port finset we use `i < w`. -/
def rectangleDualBottomPortVertex (i : ℕ) :
    RectangleDualVertex a w h := by
  have hmin : Nat.min i w ≤ w := by simp
  refine ⟨(a.1 + ((Nat.min i w : ℕ) : ℤ), a.2 - 1), ?_⟩
  rw [rectangleDualExpanded, mem_latticeRectangle]
  omega

/-- The corresponding dual port just above the original top edge. -/
def rectangleDualTopPortVertex (i : ℕ) :
    RectangleDualVertex a w h := by
  have hmin : Nat.min i w ≤ w := by simp
  refine ⟨(a.1 + ((Nat.min i w : ℕ) : ℤ), a.2 + (h : ℤ)), ?_⟩
  rw [rectangleDualExpanded, mem_latticeRectangle]
  omega

def rectangleDualBottomPorts  :
    Finset (RectangleDualVertex a w h) :=
  (Finset.range w).image (rectangleDualBottomPortVertex a w h)

def rectangleDualTopPorts  :
    Finset (RectangleDualVertex a w h) :=
  (Finset.range w).image (rectangleDualTopPortVertex a w h)

theorem rectangleDualBottomTopPorts_disjoint  :
    Disjoint (rectangleDualBottomPorts a w h) (rectangleDualTopPorts a w h) := by
  rw [Finset.disjoint_left]
  intro v hb ht
  rcases Finset.mem_image.mp hb with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp ht with ⟨j, hj, heq⟩
  grind [rectangleDualBottomPortVertex, rectangleDualTopPortVertex]

theorem rectangleDualBottomPort_val_of_lt (i : ℕ) (hi : i < w) :
    (rectangleDualBottomPortVertex a w h i).1 = (a.1 + (i : ℤ), a.2 - 1) := by
  change (a.1 + ((Nat.min i w : ℕ) : ℤ), a.2 - 1) = _
  grind

theorem rectangleClampedBottomLabel_val (σ : RectangleVertex a w h → Bool) (i : ℕ) (hi : i ≤ w) :
    rectangleClampedBottomLabel a w h σ i =
      σ ⟨(a.1 + (i : ℤ), a.2), by rw [mem_latticeRectangle]; omega⟩ := by
  simp_all [rectangleClampedBottomLabel]

def rectangleDualBottomUpVertex (i : ℕ) :
    RectangleDualVertex a w h := by
  have hmin : Nat.min i w ≤ w := by simp
  refine ⟨(a.1 + ((Nat.min i w : ℕ) : ℤ), a.2), ?_⟩
  rw [rectangleDualExpanded, mem_latticeRectangle]
  omega

theorem rectangleDualBottomUpVertex_val_of_lt (i : ℕ) (hi : i < w) :
    (rectangleDualBottomUpVertex a w h i).1 = (a.1 + (i : ℤ), a.2) := by
  change (a.1 + ((Nat.min i w : ℕ) : ℤ), a.2) = _
  grind
end

section
variable (a : LatticeVertex) (w h : ℕ) (σ : RectangleVertex a w h → Bool) (i : ℕ) (hi : i < w) (z : RectangleDualVertex a w h)
include hi
theorem rectangleDualBottomAdj_implies_up (hadj : (rectangleLabelCutDualGraph a w h σ).Adj
      (rectangleDualBottomPortVertex a w h i) z) :
    z = rectangleDualBottomUpVertex a w h i := by
  obtain ⟨b, hs, ht, hdiff, huv⟩ :=
    (rectangleLabelCutDual_adj_iff_bond a w h σ
      (rectangleDualBottomPortVertex a w h i) z).mp hadj
  rcases b with ⟨⟨x,y⟩, axis⟩
  rw [mem_latticeRectangle] at hs ht
  have hport := rectangleDualBottomPort_val_of_lt a w h i hi
  cases axis
  · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs ht
    rw [hport] at huv
    simp at huv
    rcases huv with ⟨⟨hpx,hpy⟩,hz⟩ | ⟨⟨hpx,hpy⟩,hz⟩
    · apply Subtype.ext
      calc
        (z : LatticeVertex) = (x,y) := hz
        _ = (a.1 + (i : ℤ), a.2) := Prod.ext (by omega) (by omega)
        _ = (rectangleDualBottomUpVertex a w h i : LatticeVertex) :=
          (rectangleDualBottomUpVertex_val_of_lt a w h i hi).symm
    omega
  grind [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target]

theorem rectangleDualBottomAdj_iff_up_and_flip  :
    (rectangleLabelCutDualGraph a w h σ).Adj
      (rectangleDualBottomPortVertex a w h i) z ↔
      z = rectangleDualBottomUpVertex a w h i ∧
        rectangleClampedBottomLabel a w h σ i !=
          rectangleClampedBottomLabel a w h σ (i + 1) := by
  constructor
  · intro hadj
    have hz := rectangleDualBottomAdj_implies_up a w h σ i hi z hadj
    subst z
    obtain ⟨b, hs, ht, hdiff, huv⟩ :=
      (rectangleLabelCutDual_adj_iff_bond a w h σ
        (rectangleDualBottomPortVertex a w h i)
        (rectangleDualBottomUpVertex a w h i)).mp hadj
    rcases b with ⟨⟨x,y⟩, axis⟩
    have ht0 := ht
    rw [mem_latticeRectangle] at hs ht
    have hport := rectangleDualBottomPort_val_of_lt a w h i hi
    cases axis
    · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs ht
      rcases huv with hcase | hcase
      · have hpx := congrArg Prod.fst hcase.1
        have hpy := congrArg Prod.snd hcase.1
        rw [hport] at hpx hpy
        have hfirst := rectangleClampedBottomLabel_val a w h σ i (Nat.le_of_lt hi)
        have htargetPoint : (⟨(a.1 + ((i + 1 : ℕ) : ℤ), a.2), by
            rw [mem_latticeRectangle]; omega⟩ : RectangleVertex a w h) =
            ⟨(x + 1,y), ht0⟩ := by
          apply Subtype.ext
          apply Prod.ext
          · push_cast
            omega
          linarith
        simp_all [rectangleClampedBottomLabel, LatticeBond.source, LatticeBond.target] 
      simp_all
    · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs ht
      grind
  · rintro ⟨rfl, hflip⟩
    let b : LatticeBond := ⟨(a.1 + (i : ℤ), a.2), .horizontal⟩
    have hs : b.source ∈ latticeRectangle a w h := by
      rw [mem_latticeRectangle]
      grind [LatticeBond.source]
    have ht : b.target ∈ latticeRectangle a w h := by
      rw [mem_latticeRectangle]
      grind [LatticeBond.target]
    have hdiff : σ ⟨b.source, hs⟩ != σ ⟨b.target, ht⟩ := by
      have hfirst := rectangleClampedBottomLabel_val a w h σ i (Nat.le_of_lt hi)
      have hsecond := rectangleClampedBottomLabel_val a w h σ (i + 1) (Nat.succ_le_of_lt hi)
      have htargetcoord : (a.1 + ((i + 1 : ℕ) : ℤ), a.2) =
          (a.1 + (i : ℤ) + 1, a.2) := by
        grind
      aesop 
    have hadj := (rectangleLabelCutDual_adj_iff_bond a w h σ
      (rectangleDualBottomPortVertex a w h i) (rectangleDualBottomUpVertex a w h i)).2
      ⟨b, hs, ht, hdiff, ?_⟩
    · omega
    grind [rectangleDualBottomPort_val_of_lt, LatticeBond.faceBase, rectangleDualBottomUpVertex_val_of_lt]
end

end

local instance rectangleDualVertexFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectangleDualVertex a w h) :=
  Fintype.ofFinset (rectangleDualExpanded a w h) (fun _ => Iff.rfl)

noncomputable local instance rectangleLabelCutNeighborFintype (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (v : RectangleDualVertex a w h) :
    Fintype ((rectangleLabelCutDualGraph a w h σ).neighborSet v) := by
  classical
  exact Fintype.ofFinset
    ((Finset.univ : Finset (RectangleDualVertex a w h)).filter
      fun z => (rectangleLabelCutDualGraph a w h σ).Adj v z)
    (by grind [SimpleGraph.neighborSet])

section
variable (a : LatticeVertex) (w h : ℕ) (σ : RectangleVertex a w h → Bool)
theorem rectangleDualBottomPort_degree (i : ℕ) (hi : i < w) :
    (rectangleLabelCutDualGraph a w h σ).degree (rectangleDualBottomPortVertex a w h i) =
      if rectangleClampedBottomLabel a w h σ i !=
          rectangleClampedBottomLabel a w h σ (i + 1) then 1 else 0 := by
  let G := rectangleLabelCutDualGraph a w h σ
  let u := rectangleDualBottomPortVertex a w h i
  let v := rectangleDualBottomUpVertex a w h i
  let L := rectangleClampedBottomLabel a w h σ i
  let R := rectangleClampedBottomLabel a w h σ (i + 1)
  have huv : ∀ z, G.Adj u z ↔
      z = v ∧ (L != R) = true := by
    grind [rectangleDualBottomAdj_iff_up_and_flip]
  rw [← G.card_neighborFinset_eq_degree]
  have hset : G.neighborFinset u = if h : L = R then ∅ else {v} := by
    ext z
    simp
    grind
  rw [hset]
  by_cases h : L = R <;> simp [L, R, h]

theorem rectangleDualLeftColumn_isolated (hleft : ∀ v : RectangleVertex a w h, v.1.1 = a.1 → σ v = true)
    (z : RectangleDualVertex a w h) (hz : z.1.1 = a.1 - 1) :
    (rectangleLabelCutDualGraph a w h σ).IsIsolated z := by
  intro y hadj
  obtain ⟨b, hs0, ht0, hdiff, huv⟩ :=
    (rectangleLabelCutDual_adj_iff_bond a w h σ z y).mp hadj
  rcases b with ⟨⟨x,y0⟩,axis⟩
  rw [mem_latticeRectangle] at hs0 ht0
  cases axis
  · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs0 ht0
    grind
  · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs0 ht0
    rcases huv with hcase | hcase
    · grind [LatticeBond.source, LatticeBond.target]
    grind

theorem rectangleDualRightColumn_isolated (hright : ∀ v : RectangleVertex a w h,
      v.1.1 = a.1 + (w : ℤ) → σ v = false)
    (z : RectangleDualVertex a w h) (hz : z.1.1 = a.1 + (w : ℤ)) :
    (rectangleLabelCutDualGraph a w h σ).IsIsolated z := by
  intro y hadj
  obtain ⟨b, hs0, ht0, hdiff, huv⟩ :=
    (rectangleLabelCutDual_adj_iff_bond a w h σ z y).mp hadj
  rcases b with ⟨⟨x,y0⟩,axis⟩
  rw [mem_latticeRectangle] at hs0 ht0
  cases axis
  · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs0 ht0
    grind
  · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs0 ht0
    rcases huv with hcase | hcase
    · grind
    · grind [LatticeBond.source, LatticeBond.target]

theorem rectangleDualBottomPortDegreeSum_odd (hends : σ ⟨(a.1, a.2), by rw [mem_latticeRectangle]; omega⟩ !=
      σ ⟨(a.1 + (w : ℤ), a.2), by rw [mem_latticeRectangle]; omega⟩) :
    Odd (∑ i ∈ Finset.range w,
      (rectangleLabelCutDualGraph a w h σ).degree
        (rectangleDualBottomPortVertex a w h i)) := by
  have hsum : (∑ i ∈ Finset.range w,
      (rectangleLabelCutDualGraph a w h σ).degree
        (rectangleDualBottomPortVertex a w h i)) =
      ∑ i ∈ Finset.range w,
        if rectangleClampedBottomLabel a w h σ i !=
            rectangleClampedBottomLabel a w h σ (i + 1) then 1 else 0 := by
    apply Finset.sum_congr rfl
    grind [rectangleDualBottomPort_degree]
  rw [hsum]
  exact rectangleBottomRow_flipCount_odd a w h σ hends
end

section
variable (a : LatticeVertex) (w h : ℕ)
theorem rectangleDualBottomPortVertex_injOn_range  :
    Set.InjOn (rectangleDualBottomPortVertex a w h) (Finset.range w : Set ℕ) := by
  intro i hi j hj heq
  grind [rectangleDualBottomPort_val_of_lt]

theorem rectangleDualBottomPortsDegreeSum_odd (σ : RectangleVertex a w h → Bool)
    (hends : σ ⟨(a.1, a.2), by rw [mem_latticeRectangle]; omega⟩ !=
      σ ⟨(a.1 + (w : ℤ), a.2), by rw [mem_latticeRectangle]; omega⟩) :
    Odd (∑ v ∈ rectangleDualBottomPorts a w h,
      (rectangleLabelCutDualGraph a w h σ).degree v) := by
  have himage : (∑ v ∈ rectangleDualBottomPorts a w h,
      (rectangleLabelCutDualGraph a w h σ).degree v) =
      ∑ i ∈ Finset.range w,
        (rectangleLabelCutDualGraph a w h σ).degree
          (rectangleDualBottomPortVertex a w h i) := by
    simpa only [rectangleDualBottomPorts] using
      (Finset.sum_image
        (f := fun v : RectangleDualVertex a w h =>
          (rectangleLabelCutDualGraph a w h σ).degree v)
       
       
        (rectangleDualBottomPortVertex_injOn_range a w h))
  rw [himage]
  exact rectangleDualBottomPortDegreeSum_odd a w h σ hends
end

end PottsDiscontinuity.FK
