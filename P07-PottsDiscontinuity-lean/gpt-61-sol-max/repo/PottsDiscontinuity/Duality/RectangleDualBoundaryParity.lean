/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import PottsDiscontinuity.Duality.RectangleLabelCutIncidence

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial


noncomputable section

/-- The dual port just below the original bottom edge indexed by its horizontal
bond coordinate. `i` is clamped only so the auxiliary vertex is total; in the
port finset we use `i < w`. -/
def rectangleDualBottomPortVertex (a : LatticeVertex) (w h i : ℕ) :
    RectangleDualVertex a w h := by
  have hmin : Nat.min i w ≤ w := Nat.min_le_right i w
  refine ⟨(a.1 + ((Nat.min i w : ℕ) : ℤ), a.2 - 1), ?_⟩
  rw [rectangleDualExpanded, mem_latticeRectangle]
  constructor
  · constructor <;> omega
  · constructor <;> omega

/-- The corresponding dual port just above the original top edge. -/
def rectangleDualTopPortVertex (a : LatticeVertex) (w h i : ℕ) :
    RectangleDualVertex a w h := by
  have hmin : Nat.min i w ≤ w := Nat.min_le_right i w
  refine ⟨(a.1 + ((Nat.min i w : ℕ) : ℤ), a.2 + (h : ℤ)), ?_⟩
  rw [rectangleDualExpanded, mem_latticeRectangle]
  constructor
  · constructor <;> omega
  · constructor <;> omega

def rectangleDualBottomPorts (a : LatticeVertex) (w h : ℕ)  :=
  (Finset.range w).image (rectangleDualBottomPortVertex a w h)

def rectangleDualTopPorts (a : LatticeVertex) (w h : ℕ)  :=
  (Finset.range w).image (rectangleDualTopPortVertex a w h)

section

variable (a : LatticeVertex) (w h : ℕ)


theorem rectangleDualBottomTopPorts_disjoint  :
    Disjoint (rectangleDualBottomPorts a w h) (rectangleDualTopPorts a w h) := by
  rw [Finset.disjoint_left]
  intro v hb ht
  rcases Finset.mem_image.mp hb with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp ht with ⟨j, hj, heq⟩
  have hy := congrArg (fun z  => z.1.2) heq
  simp only [rectangleDualBottomPortVertex, rectangleDualTopPortVertex] at hy
  
  
  omega

lemma rectangleDualBottomPort_val_of_lt 
    (i : ℕ) (hi : i < w) :
    (rectangleDualBottomPortVertex a w h i).1 = (a.1 + (i : ℤ), a.2 - 1) := by
  grind +locals

lemma rectangleClampedBottomLabel_val 
    (σ : RectangleVertex a w h → Bool) (i : ℕ) (hi : i ≤ w) :
    rectangleClampedBottomLabel a w h σ i =
      σ ⟨(a.1 + (i : ℤ), a.2), by rw [mem_latticeRectangle]
                                  simp_all⟩ := by
  simp_all [rectangleClampedBottomLabel]

end

def rectangleDualBottomUpVertex (a : LatticeVertex) (w h i : ℕ) :
    RectangleDualVertex a w h := by
  have hmin : Nat.min i w ≤ w := Nat.min_le_right i w
  refine ⟨(a.1 + ((Nat.min i w : ℕ) : ℤ), a.2), ?_⟩
  rw [rectangleDualExpanded, mem_latticeRectangle]
  constructor
  · constructor <;> omega
  · constructor <;> omega

section

variable (a : LatticeVertex) (w h : ℕ)
include a w h

lemma rectangleDualBottomUpVertex_val_of_lt 
    (i : ℕ) (hi : i < w) :
    (rectangleDualBottomUpVertex a w h i).1 = (a.1 + (i : ℤ), a.2) := by
  grind +locals

section

variable (σ : RectangleVertex a w h → Bool) (i : ℕ) (hi : i < w) (z : RectangleDualVertex a w h)
include hi

lemma rectangleDualBottomAdj_implies_up 
    
    (hadj : (rectangleLabelCutDualGraph a w h σ).Adj
      (rectangleDualBottomPortVertex a w h i) z) :
    z = rectangleDualBottomUpVertex a w h i := by
  obtain ⟨b, hs, ht, hdiff, huv⟩ :=
    (rectangleLabelCutDual_adj_iff_bond a w h σ
      (rectangleDualBottomPortVertex a w h i) z).mp hadj
  rcases b with ⟨⟨x,y⟩, axis⟩
  rw [mem_latticeRectangle] at hs ht
  have hport := rectangleDualBottomPort_val_of_lt a w h i hi
  cases axis
  · aesop  (add norm (by omega))  (add simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target])
       (add
        unsafe
          apply [_root_.Or.casesOn, _root_.congr, _root_.congrArg, _root_.congrFun', _root_.Prod.mk.injEq,
            _root_.Order.add_one_le_iff._simp_1, _root_.StarOrderedRing.toIsOrderedRing])
  · grind [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target]

lemma rectangleDualBottomAdj_iff_up_and_flip 
     :
    (rectangleLabelCutDualGraph a w h σ).Adj
      (rectangleDualBottomPortVertex a w h i) z ↔
      z = rectangleDualBottomUpVertex a w h i ∧
        rectangleClampedBottomLabel a w h σ i !=
          rectangleClampedBottomLabel a w h σ (i + 1) := by
  constructor
  · intro hadj
    have hz := rectangleDualBottomAdj_implies_up a w h σ i hi z hadj
    subst z
    refine ⟨rfl, ?_⟩
    obtain ⟨b, hs, ht, hdiff, huv⟩ :=
      (rectangleLabelCutDual_adj_iff_bond a w h σ
        (rectangleDualBottomPortVertex a w h i)
        (rectangleDualBottomUpVertex a w h i)).mp hadj
    rcases b with ⟨⟨x,y⟩, axis⟩
    have hs0 := hs
    have ht0 := ht
    rw [mem_latticeRectangle] at hs ht
    have hport := rectangleDualBottomPort_val_of_lt a w h i hi
    cases axis
    · simp [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target] at huv hs ht
      
      rcases huv with hcase | hcase
      · 
        
        
        
        
        
        have hfirst := rectangleClampedBottomLabel_val a w h σ i (Nat.le_of_lt hi)
        have hsecond := rectangleClampedBottomLabel_val a w h σ (i + 1) (Nat.succ_le_of_lt hi)
        
        have htargetPoint : (⟨(a.1 +  (i + 1 ) , a.2), by
            grind⟩ : RectangleVertex a w h) =
            ⟨(x + 1,y), ht0⟩ := by
          
          grind
        
        
        
        simpa only [ hfirst.trans (congrArg σ (by
                                                 simp_all : (⟨(a.1 + (i ), a.2), by
            grind⟩ : RectangleVertex a w h) =
            ⟨(x,y), hs0⟩)) , (by
                                                                 simp_all : rectangleClampedBottomLabel a w h σ (i + 1) =
            σ ⟨(x + 1,y), ht0⟩)] using (by
                                                                                 assumption : σ ⟨(x,y), hs0⟩ != σ ⟨(x + 1,y), ht0⟩) 
      · simp_all
    · grind [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target]
  · rintro ⟨rfl, hflip⟩
    let b : LatticeBond := ⟨(a.1 +  i , a.2), .horizontal⟩
    have hs : b.source ∈ latticeRectangle a w h := by
      rw [mem_latticeRectangle]
      simp only [b, LatticeBond.source]
      constructor <;> constructor <;> omega
    have ht : b.target ∈ latticeRectangle a w h := by
      rw [mem_latticeRectangle]
      simp only [b, LatticeBond.target]
      constructor <;> constructor <;> omega
     
    have hadj := (rectangleLabelCutDual_adj_iff_bond a w h σ
      (rectangleDualBottomPortVertex a w h i) (rectangleDualBottomUpVertex a w h i)).2
      ⟨b, hs, ht,  by
                     have hi1  := Nat.succ_le_of_lt hi
                     have hfirst := rectangleClampedBottomLabel_val a w h σ i (Nat.le_of_lt hi)
                     have hsecond := rectangleClampedBottomLabel_val a w h σ (i + 1) hi1
                     have htargetcoord : (a.1 +  (i + 1 ) , a.2) =
                         (a.1 +  i  + 1, a.2) := by
                       congr 1
                       
                       omega
                     
                     have hfirst' : rectangleClampedBottomLabel a w h σ i = σ ⟨b.source, hs⟩ := by
                       assumption
                     have htargetPoint : (⟨(a.1 +  i  + 1, a.2), ht⟩ : RectangleVertex a w h) =
                         ⟨b.target, ht⟩ := by
                       rfl
                     simp_all , ?_⟩
    · exact hadj
    · grind [LatticeBond.faceBase, rectangleDualBottomPort_val_of_lt, rectangleDualBottomUpVertex_val_of_lt]

end

end

end

local instance rectangleDualVertexFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectangleDualVertex a w h) :=
  Fintype.ofFinset (rectangleDualExpanded a w h)  fun _ => Iff.rfl 

noncomputable local instance rectangleLabelCutNeighborFintype (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (v : RectangleDualVertex a w h) :
    Fintype ((rectangleLabelCutDualGraph a w h σ).neighborSet v) := by
  classical
  exact Fintype.ofFinset
    ((Finset.univ : Finset (RectangleDualVertex a w h)).filter
      ((rectangleLabelCutDualGraph a w h σ).Adj v))
    (by intro z; simp [SimpleGraph.neighborSet])

section

variable (a : LatticeVertex) (w h : ℕ) (σ : RectangleVertex a w h → Bool)
include σ

theorem rectangleDualBottomPort_degree  (i : ℕ) (hi : i < w) :
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
  
  rw [(by
         ext z
         rw [G.mem_neighborFinset]
         grind : G.neighborFinset u = if h : L = R then ∅ else {v})]
  by_cases h : L = R <;> simp [L, R, h]

theorem rectangleDualLeftColumn_isolated 
    (hleft : ∀ v : RectangleVertex a w h, v.1.1 = a.1 → σ v = true)
    (z : RectangleDualVertex a w h) (hz : z.1.1 = a.1 - 1) :
    (rectangleLabelCutDualGraph a w h σ).IsIsolated z := by
  intro y hadj
  obtain ⟨b, hs0, ht0, hdiff, huv⟩ :=
    (rectangleLabelCutDual_adj_iff_bond a w h σ z y).mp hadj
  rcases b with ⟨⟨x,y0⟩,axis⟩
  
  
  
  rw [mem_latticeRectangle] at hs0 ht0
  cases axis
  · grind [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target]
  · grind [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target]

theorem rectangleDualRightColumn_isolated 
    (hright : ∀ v : RectangleVertex a w h,
      v.1.1 = a.1 + (w : ℤ) → σ v = false)
    (z : RectangleDualVertex a w h) (hz : z.1.1 = a.1 + (w : ℤ)) :
    (rectangleLabelCutDualGraph a w h σ).IsIsolated z := by
  intro y hadj
  obtain ⟨b, hs0, ht0, hdiff, huv⟩ :=
    (rectangleLabelCutDual_adj_iff_bond a w h σ z y).mp hadj
  rcases b with ⟨⟨x,y0⟩,axis⟩
  
  
  
  rw [mem_latticeRectangle] at hs0 ht0
  cases axis
  · grind [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target]
  · grind [LatticeBond.faceBase, LatticeBond.source, LatticeBond.target]

theorem rectangleDualBottomPortDegreeSum_odd 
    (hends : σ ⟨(a.1, a.2), by rw [mem_latticeRectangle]
                               simp_all⟩ !=
      σ ⟨(a.1 + (w : ℤ), a.2), by rw [mem_latticeRectangle]
                                  simp_all⟩) :
    Odd (∑ i ∈ Finset.range w,
      (rectangleLabelCutDualGraph a w h σ).degree
        (rectangleDualBottomPortVertex a w h i)) := Eq.mpr
                                                      (congrArg Odd (Finset.sum_congr rfl fun i hi => rectangleDualBottomPort_degree a w h σ i (Finset.mem_range.mp hi)))
                                                      (rectangleBottomRow_flipCount_odd a w h σ hends)

end

lemma rectangleDualBottomPortVertex_injOn_range (a : LatticeVertex) (w h : ℕ) :
    Set.InjOn (rectangleDualBottomPortVertex a w h) (Finset.range w : Set ℕ) := by
  intro i hi j hj heq
  have hix := congrArg (fun z  => z.1.1) heq
  rw [rectangleDualBottomPort_val_of_lt a w h i (Finset.mem_range.mp hi),
    rectangleDualBottomPort_val_of_lt a w h j (Finset.mem_range.mp hj)] at hix
  exact_mod_cast  add_left_cancel hix 

theorem rectangleDualBottomPortsDegreeSum_odd (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool)
    (hends : σ ⟨(a.1, a.2), by rw [mem_latticeRectangle]
                               simp_all⟩ !=
      σ ⟨(a.1 + (w : ℤ), a.2), by rw [mem_latticeRectangle]
                                  simp_all⟩) :
    Odd (∑ v ∈ rectangleDualBottomPorts a w h,
      (rectangleLabelCutDualGraph a w h σ).degree v) := Eq.mpr (congrArg Odd (Finset.sum_image (rectangleDualBottomPortVertex_injOn_range a w h)))
                                                          (rectangleDualBottomPortDegreeSum_odd a w h σ hends)

end PottsDiscontinuity.FK
