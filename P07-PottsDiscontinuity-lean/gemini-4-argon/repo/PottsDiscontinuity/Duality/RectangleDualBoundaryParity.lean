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

/-- The dual port just below the original bottom edge indexed by its horizontal
bond coordinate. `i` is clamped only so the auxiliary vertex is total; in the
port finset we use `i < w`. -/
def rectangleDualBottomPortVertex (a : LatticeVertex) (w h : ℕ) (i : ℕ) :
    RectangleDualVertex a w h := by
  have hmin : Nat.min i w ≤ w := Nat.min_le_right i w
  refine ⟨(a.1 + ((Nat.min i w : ℕ) : ℤ), a.2 - 1), ?_⟩
  rw [rectangleDualExpanded, mem_latticeRectangle]
  constructor
  · constructor <;> omega
  · constructor <;> omega

/-- The corresponding dual port just above the original top edge. -/
def rectangleDualTopPortVertex (a : LatticeVertex) (w h : ℕ) (i : ℕ) :
    RectangleDualVertex a w h := by
  have hmin : Nat.min i w ≤ w := Nat.min_le_right i w
  refine ⟨(a.1 + ((Nat.min i w : ℕ) : ℤ), a.2 + (h : ℤ)), ?_⟩
  rw [rectangleDualExpanded, mem_latticeRectangle]
  constructor
  · constructor <;> omega
  · constructor <;> omega

def rectangleDualBottomPorts (a : LatticeVertex) (w h : ℕ) :
    Finset (RectangleDualVertex a w h) :=
  (Finset.range w).image (rectangleDualBottomPortVertex a w h)

def rectangleDualTopPorts (a : LatticeVertex) (w h : ℕ) :
    Finset (RectangleDualVertex a w h) :=
  (Finset.range w).image (rectangleDualTopPortVertex a w h)

theorem rectangleDualBottomTopPorts_disjoint (a : LatticeVertex) (w h : ℕ) :
    Disjoint (rectangleDualBottomPorts a w h) (rectangleDualTopPorts a w h) := by
  rw [Finset.disjoint_left]
  intro v hb ht
  rcases Finset.mem_image.mp hb with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp ht with ⟨j, hj, heq⟩
  have hy := congrArg (fun z : RectangleDualVertex a w h => z.1.2) heq
  simp only [rectangleDualBottomPortVertex, rectangleDualTopPortVertex] at hy
  have hiw := Finset.mem_range.mp hi
  have hjw := Finset.mem_range.mp hj
  omega

lemma rectangleDualBottomPort_val_of_lt (a : LatticeVertex) (w h : ℕ)
    (i : ℕ) (hi : i < w) :
    (rectangleDualBottomPortVertex a w h i).1 = (a.1 + (i : ℤ), a.2 - 1) := by
  change (a.1 + ((Nat.min i w : ℕ) : ℤ), a.2 - 1) = _
  simp only [Nat.min_eq_left (Nat.le_of_lt hi)]

lemma rectangleClampedBottomLabel_val (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (i : ℕ) (hi : i ≤ w) :
    rectangleClampedBottomLabel a w h σ i =
      σ ⟨(a.1 + (i : ℤ), a.2), by rw [mem_latticeRectangle]; constructor <;>
        constructor <;> omega⟩ := by
  simp [rectangleClampedBottomLabel, Nat.min_eq_left hi]

def rectangleDualBottomUpVertex (a : LatticeVertex) (w h : ℕ) (i : ℕ) :
    RectangleDualVertex a w h := by
  have hmin : Nat.min i w ≤ w := Nat.min_le_right i w
  refine ⟨(a.1 + ((Nat.min i w : ℕ) : ℤ), a.2), ?_⟩
  rw [rectangleDualExpanded, mem_latticeRectangle]
  constructor
  · constructor <;> omega
  · constructor <;> omega

lemma rectangleDualBottomUpVertex_val_of_lt (a : LatticeVertex) (w h : ℕ)
    (i : ℕ) (hi : i < w) :
    (rectangleDualBottomUpVertex a w h i).1 = (a.1 + (i : ℤ), a.2) := by
  change (a.1 + ((Nat.min i w : ℕ) : ℤ), a.2) = _
  simp only [Nat.min_eq_left (Nat.le_of_lt hi)]

lemma rectangleDualBottomAdj_iff_up_and_flip (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (i : ℕ) (hi : i < w)
    (z : RectangleDualVertex a w h) :
    (rectangleLabelCutDualGraph a w h σ).Adj
      (rectangleDualBottomPortVertex a w h i) z ↔
      z = rectangleDualBottomUpVertex a w h i ∧
        rectangleClampedBottomLabel a w h σ i !=
          rectangleClampedBottomLabel a w h σ (i + 1) := by
  constructor
  · intro hadj
    obtain ⟨⟨⟨x, y⟩, axis⟩, hs0, ht0, hdiff, huv⟩ :=
      (rectangleLabelCutDual_adj_iff_bond a w h σ _ z).mp hadj
    have hs := (mem_latticeRectangle _ _ _ _).mp hs0
    have ht := (mem_latticeRectangle _ _ _ _).mp ht0
    have hport := rectangleDualBottomPort_val_of_lt a w h i hi
    cases axis
    · simp only [LatticeBond.faceBase, hport, Prod.mk.injEq] at huv
      rcases huv with ⟨⟨rfl, hpy⟩, hz⟩ | ⟨⟨_, hpy⟩, _⟩
      · have hy : y = a.2 := by omega
        subst hy
        refine ⟨Subtype.ext (hz.trans (rectangleDualBottomUpVertex_val_of_lt a w h i hi).symm), ?_⟩
        rw [rectangleClampedBottomLabel_val a w h σ i hi.le,
          rectangleClampedBottomLabel_val a w h σ (i + 1) hi]
        convert hdiff using 3 <;> apply Subtype.ext <;> ext <;>
          simp [LatticeBond.source, LatticeBond.target] <;> omega
      · dsimp [LatticeBond.source] at hs; omega
    · simp only [LatticeBond.faceBase, hport, Prod.mk.injEq] at huv
      dsimp [LatticeBond.source] at hs; omega
  · rintro ⟨rfl, hflip⟩
    let b : LatticeBond := ⟨(a.1 + (i : ℤ), a.2), .horizontal⟩
    have hs : b.source ∈ latticeRectangle a w h := by
      rw [mem_latticeRectangle]; simp [b, LatticeBond.source]; omega
    have ht : b.target ∈ latticeRectangle a w h := by
      rw [mem_latticeRectangle]; simp [b, LatticeBond.target]; omega
    refine (rectangleLabelCutDual_adj_iff_bond a w h σ _ _).2 ⟨b, hs, ht, ?_, Or.inl ⟨?_, ?_⟩⟩
    · rw [rectangleClampedBottomLabel_val a w h σ i hi.le,
        rectangleClampedBottomLabel_val a w h σ (i + 1) hi] at hflip
      convert hflip using 3 <;> apply Subtype.ext <;> ext <;>
        simp [b, LatticeBond.source, LatticeBond.target] <;> omega
    · simp [rectangleDualBottomPort_val_of_lt a w h i hi, b, LatticeBond.faceBase]
    · simp [rectangleDualBottomUpVertex_val_of_lt a w h i hi, b, LatticeBond.faceBase]

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
    (by intro z; simp [SimpleGraph.neighborSet])

theorem rectangleDualBottomPort_degree (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (i : ℕ) (hi : i < w) :
    (rectangleLabelCutDualGraph a w h σ).degree (rectangleDualBottomPortVertex a w h i) =
      if rectangleClampedBottomLabel a w h σ i !=
          rectangleClampedBottomLabel a w h σ (i + 1) then 1 else 0 := by
  classical
  rw [← (rectangleLabelCutDualGraph a w h σ).card_neighborFinset_eq_degree,
    show (rectangleLabelCutDualGraph a w h σ).neighborFinset
        (rectangleDualBottomPortVertex a w h i) =
      if rectangleClampedBottomLabel a w h σ i !=
          rectangleClampedBottomLabel a w h σ (i + 1) then
        {rectangleDualBottomUpVertex a w h i} else ∅ by
    ext z
    simp only [SimpleGraph.mem_neighborFinset,
      rectangleDualBottomAdj_iff_up_and_flip a w h σ i hi z]
    split_ifs with h <;> simp [h]]
  split_ifs <;> simp

theorem rectangleDualLeftColumn_isolated (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool)
    (hleft : ∀ v : RectangleVertex a w h, v.1.1 = a.1 → σ v = true)
    (z : RectangleDualVertex a w h) (hz : z.1.1 = a.1 - 1) :
    (rectangleLabelCutDualGraph a w h σ).IsIsolated z := by
  intro y hadj
  obtain ⟨⟨⟨x, y0⟩, axis⟩, hs0, ht0, hdiff, huv⟩ :=
    (rectangleLabelCutDual_adj_iff_bond a w h σ z y).mp hadj
  have hs := (mem_latticeRectangle _ _ _ _).mp hs0
  have ht := (mem_latticeRectangle _ _ _ _).mp ht0
  cases axis <;> simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs ht
  · rcases huv with ⟨h1, _⟩ | ⟨h1, _⟩ <;> have := congrArg Prod.fst h1 <;> omega
  · rcases huv with ⟨h1, _⟩ | ⟨h1, _⟩ <;> have := congrArg Prod.fst h1
    · have hx : x = a.1 := by omega
      change σ ⟨(x, y0), hs0⟩ != σ ⟨(x, y0 + 1), ht0⟩ at hdiff
      simp [hleft ⟨(x, y0), hs0⟩ hx, hleft ⟨(x, y0 + 1), ht0⟩ hx] at hdiff
    · omega

theorem rectangleDualRightColumn_isolated (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool)
    (hright : ∀ v : RectangleVertex a w h,
      v.1.1 = a.1 + (w : ℤ) → σ v = false)
    (z : RectangleDualVertex a w h) (hz : z.1.1 = a.1 + (w : ℤ)) :
    (rectangleLabelCutDualGraph a w h σ).IsIsolated z := by
  intro y hadj
  obtain ⟨⟨⟨x, y0⟩, axis⟩, hs0, ht0, hdiff, huv⟩ :=
    (rectangleLabelCutDual_adj_iff_bond a w h σ z y).mp hadj
  have hs := (mem_latticeRectangle _ _ _ _).mp hs0
  have ht := (mem_latticeRectangle _ _ _ _).mp ht0
  cases axis <;> simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs ht
  · rcases huv with ⟨h1, _⟩ | ⟨h1, _⟩ <;> have := congrArg Prod.fst h1 <;> omega
  · rcases huv with ⟨h1, _⟩ | ⟨h1, _⟩ <;> have := congrArg Prod.fst h1
    · omega
    · have hx : x = a.1 + (w : ℤ) := by omega
      change σ ⟨(x, y0), hs0⟩ != σ ⟨(x, y0 + 1), ht0⟩ at hdiff
      simp [hright ⟨(x, y0), hs0⟩ hx, hright ⟨(x, y0 + 1), ht0⟩ hx] at hdiff

theorem rectangleDualBottomPortDegreeSum_odd (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool)
    (hends : σ ⟨(a.1, a.2), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩ !=
      σ ⟨(a.1 + (w : ℤ), a.2), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩) :
    Odd (∑ i ∈ Finset.range w,
      (rectangleLabelCutDualGraph a w h σ).degree
        (rectangleDualBottomPortVertex a w h i)) := by
  rw [Finset.sum_congr rfl fun i hi =>
    rectangleDualBottomPort_degree a w h σ i (Finset.mem_range.mp hi)]
  exact rectangleBottomRow_flipCount_odd a w h σ hends

lemma rectangleDualBottomPortVertex_injOn_range (a : LatticeVertex) (w h : ℕ) :
    Set.InjOn (rectangleDualBottomPortVertex a w h) (Finset.range w : Set ℕ) := by
  intro i hi j hj heq
  have hix := congrArg (fun z : RectangleDualVertex a w h => z.1.1) heq
  rw [rectangleDualBottomPort_val_of_lt a w h i (Finset.mem_range.mp hi),
    rectangleDualBottomPort_val_of_lt a w h j (Finset.mem_range.mp hj)] at hix
  exact_mod_cast add_left_cancel hix

theorem rectangleDualBottomPortsDegreeSum_odd (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool)
    (hends : σ ⟨(a.1, a.2), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩ !=
      σ ⟨(a.1 + (w : ℤ), a.2), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩) :
    Odd (∑ v ∈ rectangleDualBottomPorts a w h,
      (rectangleLabelCutDualGraph a w h σ).degree v) := by
  rw [rectangleDualBottomPorts, Finset.sum_image (rectangleDualBottomPortVertex_injOn_range a w h)]
  exact rectangleDualBottomPortDegreeSum_odd a w h σ hends

end PottsDiscontinuity.FK
