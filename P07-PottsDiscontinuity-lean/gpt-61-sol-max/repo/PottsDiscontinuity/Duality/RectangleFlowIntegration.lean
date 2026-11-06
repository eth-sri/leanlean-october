/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import PottsDiscontinuity.Duality.RectangleCurl
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

abbrev RectanglePrimalFlow (a : LatticeVertex) (w h : ℕ) :=
  RectanglePrimalBond a w h → ℝ

def rectangleExtendedPrimalFlow (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (b : LatticeBond)  :=
  if hb : b.source ∈ latticeRectangle a w h ∧ b.target ∈ latticeRectangle a w h
  then F ⟨b, hb⟩ else 0

noncomputable def rectanglePrimalFlowDivergence (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (v : LatticeVertex)  :=
  ∑ b : rectangleActualIncidentBonds a w h v,
    if b.1.1.source = v then F b.1 else -F b.1

def rectangleFlowH (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (x y : ℤ)  :=
  rectangleExtendedPrimalFlow a w h F ⟨(x,y), .horizontal⟩

def rectangleFlowV (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (x y : ℤ)  :=
  rectangleExtendedPrimalFlow a w h F ⟨(x,y), .vertical⟩

def rectangleFlowX (a : LatticeVertex) (n : ℤ)  := a.1 + n
def rectangleFlowY (a : LatticeVertex) (m : ℤ)  := a.2 + m

def rectangleFlowVertex (a : LatticeVertex) (n m : ℤ) : LatticeVertex :=
  (rectangleFlowX a n, rectangleFlowY a m)

def rectangleFlowDivergenceStencil (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (v : LatticeVertex)  :=
  rectangleExtendedPrimalFlow a w h F ⟨v, .horizontal⟩ -
    rectangleExtendedPrimalFlow a w h F ⟨(v.1 - 1, v.2), .horizontal⟩ +
    rectangleExtendedPrimalFlow a w h F ⟨v, .vertical⟩ -
    rectangleExtendedPrimalFlow a w h F ⟨(v.1, v.2 - 1), .vertical⟩

/-- A flow with genuine zero incidence divergence at every primal vertex. -/
def RectangleDivergenceFreeFlow (a : LatticeVertex) (w h : ℕ) :=
  {F : RectanglePrimalFlow a w h //
    ∀ v, v ∈ latticeRectangle a w h → rectanglePrimalFlowDivergence a w h F v = 0}

def rectangleFlowSignedCandidate (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (v : LatticeVertex) (i : Fin 4)  :=
  if (rectangleCurlIncidentCandidate v i).source = v then
    rectangleExtendedPrimalFlow a w h F (rectangleCurlIncidentCandidate v i)
  else -rectangleExtendedPrimalFlow a w h F (rectangleCurlIncidentCandidate v i)

section

variable (a : LatticeVertex) (w h : ℕ) (F : RectanglePrimalFlow a w h)


private theorem rectangleFlowCandidate_outside_zero
    
    (v : LatticeVertex) (i : Fin 4)
    (hout : ¬ rectangleCurlCandidateInside a w h v i) :
    rectangleExtendedPrimalFlow a w h F (rectangleCurlIncidentCandidate v i) = 0 := by
  simp only [rectangleExtendedPrimalFlow]
  split_ifs with hb
  · 
    exact (hout  hb ).elim
  · rfl

private theorem rectangleFlowSignedCandidate_eq_term
    
    (v : LatticeVertex) (i : Fin 4)
    (hi : rectangleCurlCandidateInside a w h v i) :
    rectangleFlowSignedCandidate a w h F v i =
      match i.val with
      | 0 => rectangleFlowH a w h F v.1 v.2
      | 1 => -rectangleFlowH a w h F (v.1 - 1) v.2
      | 2 => rectangleFlowV a w h F v.1 v.2
      | _ => -rectangleFlowV a w h F v.1 (v.2 - 1) := by
  rcases v with ⟨x, y⟩
  fin_cases i
  · (simp [rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate,
      rectangleExtendedPrimalFlow, rectangleFlowH, LatticeBond.source];
      split_ifs) <;> rfl
  · have hn : (x - 1, y) ≠ (x, y) := by
      intro hh
      have hx := congrArg Prod.fst hh
      omega
    (simp [rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate,
      rectangleExtendedPrimalFlow, rectangleFlowH, LatticeBond.source, hn];
      split_ifs) <;> rfl
  · (simp [rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate,
      rectangleExtendedPrimalFlow, rectangleFlowV, LatticeBond.source];
      split_ifs) <;> rfl
  · have hn : (x, y - 1) ≠ (x, y) := by
      intro hh
      have hy := congrArg Prod.snd hh
      omega
    (simp [rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate,
      rectangleExtendedPrimalFlow, rectangleFlowV, LatticeBond.source, hn];
      split_ifs) <;> rfl

theorem rectanglePrimalFlowDivergence_eq_stencil
    
    (v : LatticeVertex) :
    rectanglePrimalFlowDivergence a w h F v = rectangleFlowDivergenceStencil a w h F v := by
  classical
  let e := rectangleActualIncidentCandidateEquiv a w h v
  let p  := rectangleCurlCandidateInside a w h v
  
  
  calc
    rectanglePrimalFlowDivergence a w h F v =
        ∑ b : rectangleActualIncidentBonds a w h v,
          rectangleFlowSignedCandidate a w h F v (e b).1 := by
      
      apply Finset.sum_congr rfl
      intro b hb
      have hmap : rectangleCurlIncidentCandidate v (e b).1 = b.1.1 :=
        congrArg (fun z : rectangleActualIncidentBonds a w h v => z.1.1) (e.left_inv b)
      
      simp [rectangleFlowSignedCandidate, hmap,
        rectangleExtendedPrimalFlow, b.1.2]
    _ = ∑ i : {i : Fin 4 // p i}, rectangleFlowSignedCandidate a w h F v i.1 :=
      Equiv.sum_comp e  fun i => rectangleFlowSignedCandidate a w h F v i.1 
    _ = rectangleFlowDivergenceStencil a w h F v := by
      rw [←  Finset.sum_subtype (p := p) (Finset.univ.filter p)
                 (by  simp )
                  (rectangleFlowSignedCandidate a w h F v)  ]
      rw [Finset.sum_filter]
      change (∑ i : Fin 4,
        if p i then rectangleFlowSignedCandidate a w h F v i else 0) = _
      have hterm (i : Fin 4) :
          (if p i then rectangleFlowSignedCandidate a w h F v i else 0) =
            match i.val with
            | 0 => rectangleFlowH a w h F v.1 v.2
            | 1 => -rectangleFlowH a w h F (v.1 - 1) v.2
            | 2 => rectangleFlowV a w h F v.1 v.2
            | _ => -rectangleFlowV a w h F v.1 (v.2 - 1) := by
        fin_cases i
        · by_cases hp : p 0
          · simpa [hp] using
              rectangleFlowSignedCandidate_eq_term a w h F v 0 hp
          · 
            simpa [hp, rectangleCurlIncidentCandidate, rectangleFlowH] using (rectangleFlowCandidate_outside_zero a w h F v 0 hp).symm
        · by_cases hp : p 1
          · simpa [hp] using
              rectangleFlowSignedCandidate_eq_term a w h F v 1 hp
          · 
            simpa [hp, rectangleCurlIncidentCandidate, rectangleFlowH] using  rectangleFlowCandidate_outside_zero a w h F v 1 hp 
        · by_cases hp : p 2
          · simpa [hp] using
              rectangleFlowSignedCandidate_eq_term a w h F v 2 hp
          · 
            simpa [hp, rectangleCurlIncidentCandidate, rectangleFlowV] using (rectangleFlowCandidate_outside_zero a w h F v 2 hp).symm
        · by_cases hp : p 3
          · simpa [hp] using
              rectangleFlowSignedCandidate_eq_term a w h F v 3 hp
          · 
            have hn := congrArg Neg.neg (rectangleFlowCandidate_outside_zero a w h F v 3 hp)
            simpa [hp, rectangleCurlIncidentCandidate, rectangleFlowV] using hn
      simp_rw [hterm]
      simp [Fin.sum_univ_succ, rectangleFlowDivergenceStencil,
        rectangleFlowH, rectangleFlowV]
      ring_nf

private theorem rectangleFlowDivergenceStencil_offset
    
    (n m : ℤ) :
    rectangleFlowDivergenceStencil a w h F (rectangleFlowVertex a n m) =
      rectangleFlowH a w h F (rectangleFlowX a n) (rectangleFlowY a m) -
        rectangleFlowH a w h F (rectangleFlowX a (n - 1)) (rectangleFlowY a m) +
      rectangleFlowV a w h F (rectangleFlowX a n) (rectangleFlowY a m) -
        rectangleFlowV a w h F (rectangleFlowX a n) (rectangleFlowY a (m - 1)) := by
  simp [rectangleFlowDivergenceStencil, rectangleFlowH, rectangleFlowV,
    rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
  grind

end

private theorem rectangleFlowVertex_mem
    (a : LatticeVertex) (w h n m : ℕ)
    (hn : n ≤ w) (hm : m ≤ h) :
    rectangleFlowVertex a (n : ℤ) (m : ℤ) ∈ latticeRectangle a w h := by
  rw [mem_latticeRectangle]
  simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
  omega

def rectangleFlowRowSumV (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (n m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    rectangleFlowV a w h F (rectangleFlowX a (k : ℤ)) (rectangleFlowY a (m : ℤ))

section

variable (a : LatticeVertex) (w h : ℕ)
include a w h

section

variable (F : RectangleDivergenceFreeFlow a w h) (n m : ℕ) (hn : n ≤ w) (hm : m ≤ h)
include hn hm

private theorem rectangleFlowOffsetDiv_zero
      :
    rectangleFlowH a w h F.1 (rectangleFlowX a (n : ℤ)) (rectangleFlowY a (m : ℤ)) -
      rectangleFlowH a w h F.1 (rectangleFlowX a ((n : ℤ) - 1)) (rectangleFlowY a (m : ℤ)) +
      rectangleFlowV a w h F.1 (rectangleFlowX a (n : ℤ)) (rectangleFlowY a (m : ℤ)) -
      rectangleFlowV a w h F.1 (rectangleFlowX a (n : ℤ)) (rectangleFlowY a ((m : ℤ) - 1)) = 0 := by
  
  have hz := F.2 _ (rectangleFlowVertex_mem a w h n m hn hm)
  rw [rectanglePrimalFlowDivergence_eq_stencil a w h F.1 _] at hz
  rw [rectangleFlowDivergenceStencil_offset] at hz
  exact hz

private theorem rectangleFlowRowDiff_sum
      :
     ∑ k ∈ Finset.range (n + 1),
      (rectangleFlowV a w h F.1 (rectangleFlowX a (k : ℤ)) (rectangleFlowY a (m : ℤ)) -
        rectangleFlowV a w h F.1 (rectangleFlowX a (k : ℤ))
          (rectangleFlowY a ((m : ℤ) - 1)))  =
      rectangleFlowH a w h F.1 (rectangleFlowX a ((0 : ℤ) - 1)) (rectangleFlowY a (m : ℤ)) -
        rectangleFlowH a w h F.1 (rectangleFlowX a (n : ℤ)) (rectangleFlowY a (m : ℤ)) := by
  induction n with
  | zero =>
      have hd := rectangleFlowOffsetDiv_zero a w h F 0 m (by omega) hm
      simp  at hd ⊢
      linarith
  | succ n ih =>
      
      have hd := rectangleFlowOffsetDiv_zero a w h F (n + 1) m (by omega) hm
      rw [Finset.sum_range_succ]
      grind

end

private theorem rectangleFlowSideHorizontal_zero
     (F : RectanglePrimalFlow a w h)
    (m : ℕ) :
    rectangleFlowH a w h F (rectangleFlowX a ((0 : ℤ) - 1))
        (rectangleFlowY a (m : ℤ)) = 0 ∧
    rectangleFlowH a w h F (rectangleFlowX a (w : ℤ))
        (rectangleFlowY a (m : ℤ)) = 0 := by
  constructor
  · simp [rectangleFlowH, rectangleFlowX, rectangleExtendedPrimalFlow, LatticeBond.source, mem_latticeRectangle]
  · simp [rectangleFlowH, rectangleFlowX, rectangleExtendedPrimalFlow, LatticeBond.target, mem_latticeRectangle]

private theorem rectangleFlowBottomVertical_zero
     (F : RectanglePrimalFlow a w h)
    (k : ℕ) :
    rectangleFlowV a w h F (rectangleFlowX a (k : ℤ))
      (rectangleFlowY a ((0 : ℤ) - 1)) = 0 := by
  simp [rectangleFlowV, rectangleFlowY, rectangleExtendedPrimalFlow, LatticeBond.source, mem_latticeRectangle]

theorem rectangleFlow_rowCutSum_zero
     (F : RectangleDivergenceFreeFlow a w h)
    (m : ℕ) (hm : m < h) :
    rectangleFlowRowSumV a w h F.1 w m = 0 := by
  have hrow (j : ℕ) (hj : j ≤ h) : rectangleFlowRowSumV a w h F.1 w j = 0 := by
    induction j with
    | zero =>
        have hd := rectangleFlowRowDiff_sum a w h F w 0 (by omega) (by omega)
        have hs := rectangleFlowSideHorizontal_zero a w h F.1 0
        
        have hlower :  ∑ k ∈ Finset.range (w + 1),
            rectangleFlowV a w h F.1 (rectangleFlowX a  k )
              (rectangleFlowY a ( 0  - 1))  = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          simpa using (rectangleFlowBottomVertical_zero a w h F.1) k
        
        exact  by
                 aesop 
    | succ j ih =>
        
        have hs := rectangleFlowSideHorizontal_zero a w h F.1 (j + 1)
        have hdiff :
            rectangleFlowRowSumV a w h F.1 w (j + 1) -
              rectangleFlowRowSumV a w h F.1 w j = 0 := by
          have hh :=  rectangleFlowRowDiff_sum a w h F w (j + 1) (by omega) hj 
          rw [hs.1, hs.2] at hh
          
          simpa [rectangleFlowRowSumV] using hh
        have hnext := ih (by omega)
        linarith
  exact hrow m (Nat.le_of_lt hm)

private theorem rectangleFlowVerticalTop_zero
     (F : RectanglePrimalFlow a w h)
    (n : ℕ) :
    rectangleFlowV a w h F (rectangleFlowX a (n : ℤ))
      (rectangleFlowY a (h : ℤ)) = 0 := by
  simp [rectangleFlowV, rectangleFlowY, rectangleExtendedPrimalFlow, LatticeBond.target, mem_latticeRectangle]

private theorem rectangleFlowRowSumV_top_zero
     (F : RectanglePrimalFlow a w h)
    (n : ℕ) : rectangleFlowRowSumV a w h F n h = 0 := by
                                                        solve_by_elim [_root_.Finset.sum_eq_zero, _root_.PottsDiscontinuity.FK.rectangleFlowVerticalTop_zero]

end

def rectangleFlowPotentialValue (a : LatticeVertex) (w h : ℕ)
    (F : RectangleDivergenceFreeFlow a w h) (z : LatticeVertex)  :=
  if _hz : z ∈ rectangleDualInterior a w h then
    - ∑ k ∈ Finset.range ((z.1 - a.1).toNat + 1),
      rectangleFlowV a w h F.1 (rectangleFlowX a (k : ℤ)) z.2 
  else 0

noncomputable def rectangleFlowExteriorPotential
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h) :
    RectangleExteriorPotential a w h := by
  refine ⟨fun z => rectangleFlowPotentialValue a w h F z.1, ?_⟩
  intro z hz
  simp only [rectangleDualBoundary, Finset.mem_filter] at hz
  simp [rectangleFlowPotentialValue, hz.2]

section

variable (a : LatticeVertex) (w h : ℕ)
include a w h

section

variable (F : RectangleDivergenceFreeFlow a w h)


private theorem rectangleFlowExtendedPotential_eq_value
     
    (z : LatticeVertex) (hz : z ∈ rectangleDualExpanded a w h) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F) z =
      rectangleFlowPotentialValue a w h F z := by
  aesop

private theorem rectangleFlowPotentialLeftBoundary
     
    (m : ℕ) (hm : m ≤ h) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (-1) (m : ℤ)) = 0 := by
  
  rw [rectangleFlowExtendedPotential_eq_value a w h F _ (by
                                                           rw [rectangleDualExpanded, mem_latticeRectangle]
                                                           simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
                                                           omega)]
  have hout : rectangleFlowVertex a (-1)  m  ∉ rectangleDualInterior a w h := by
    intro hz
    have hx := (Finset.mem_filter.mp hz).2.1
    simp [rectangleFlowVertex, rectangleFlowX] at hx
  simp [rectangleFlowPotentialValue, hout]

private theorem rectangleFlowPotentialBottomBoundary
     
    (n : ℕ) (hn : n ≤ w) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (n : ℤ) (-1)) = 0 := by
  
  rw [rectangleFlowExtendedPotential_eq_value a w h F _ (by
                                                           rw [rectangleDualExpanded, mem_latticeRectangle]
                                                           simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
                                                           omega)]
  have hout : rectangleFlowVertex a  n  (-1) ∉ rectangleDualInterior a w h := by
    intro hz
    have hy := (Finset.mem_filter.mp hz).2.2.2.1
    simp [rectangleFlowVertex, rectangleFlowY] at hy
  simp [rectangleFlowPotentialValue, hout]

private theorem rectangleFlowPotentialValue_interior
     
    (n m : ℕ) (hn : n < w) (hm : m < h) :
    rectangleFlowPotentialValue a w h F
      (rectangleFlowVertex a (n : ℤ) (m : ℤ)) =
        -rectangleFlowRowSumV a w h F.1 n m := by
  
  
  have hx :
      ((rectangleFlowVertex a  n   m ).1 - a.1).toNat = n := by
    change (a.1 +  n  - a.1).toNat = n
    
    
    simp
  rw [rectangleFlowPotentialValue, dite_eq_left (by
                                                   apply Finset.mem_filter.mpr
                                                   refine ⟨ by
                                                              rw [rectangleDualExpanded, mem_latticeRectangle]
                                                              simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
                                                              omega , ?_⟩
                                                   simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
                                                   omega), hx]
  simp [rectangleFlowRowSumV, rectangleFlowVertex]

end

private theorem rectangleFlowVertex_mem_interior_iff
     (n m : ℕ) :
    rectangleFlowVertex a (n : ℤ) (m : ℤ) ∈ rectangleDualInterior a w h ↔
      n < w ∧ m < h := by
  simp [rectangleDualInterior, rectangleDualExpanded, latticeRectangle, rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
  omega

section

variable (F : RectangleDivergenceFreeFlow a w h) (n m : ℕ)


private theorem rectangleFlowPotentialValue_face
      :
    rectangleFlowPotentialValue a w h F
      (rectangleFlowVertex a (n : ℤ) (m : ℤ)) =
      if n < w ∧ m < h then -rectangleFlowRowSumV a w h F.1 n m else 0 := by
  have hi := rectangleFlowVertex_mem_interior_iff a w h n m
  by_cases hnm : n < w ∧ m < h
  · rw [ite_eq_left hnm]
    exact rectangleFlowPotentialValue_interior a w h F n m hnm.1 hnm.2
  · rw [ite_eq_right hnm]
    have hout : rectangleFlowVertex a (n : ℤ) (m : ℤ) ∉ rectangleDualInterior a w h :=
      by
        simp_all
    simp [rectangleFlowPotentialValue, hout]

private theorem rectangleFlowPotentialAtOffset
      (hn : n ≤ w) (hm : m ≤ h) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (n : ℤ) (m : ℤ)) =
        if n < w ∧ m < h then -rectangleFlowRowSumV a w h F.1 n m else 0 := by
  
  rw [rectangleFlowExtendedPotential_eq_value a w h F _ (by
                                                           rw [rectangleDualExpanded, mem_latticeRectangle]
                                                           simp [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
                                                           omega)]
  exact rectangleFlowPotentialValue_face a w h F n m

private theorem rectangleFlowPotentialAtOffset_eq_neg_rowSum
      (hn : n < w) (hm : m ≤ h) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (n : ℤ) (m : ℤ)) =
      -rectangleFlowRowSumV a w h F.1 n m := by
  rw [rectangleFlowPotentialAtOffset a w h F n m (Nat.le_of_lt hn) hm]
  by_cases hm' : m < h
  · simp [hn, hm']
  · have hmh : m = h := by omega
    subst m
    simp [rectangleFlowRowSumV_top_zero]

end

private theorem rectangleFlowPotentialAtOffset_right_zero
     (F : RectangleDivergenceFreeFlow a w h)
    (m : ℕ) (hm : m < h) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (w : ℤ) (m : ℤ)) = 0 := by
  rw [rectangleFlowPotentialAtOffset a w h F w m le_rfl (Nat.le_of_lt hm)]
  simp 

private theorem rectangleFlowRowSumV_succ
     (F : RectanglePrimalFlow a w h)
    (n m : ℕ) :
    rectangleFlowRowSumV a w h F (n + 1) m =
      rectangleFlowRowSumV a w h F n m +
        rectangleFlowV a w h F (rectangleFlowX a ((n + 1 : ℕ) : ℤ))
          (rectangleFlowY a (m : ℤ)) := by
  simp [rectangleFlowRowSumV, Finset.sum_range_succ]

section

variable (F : RectangleDivergenceFreeFlow a w h)


private theorem rectangleFlowHorizontalOffset_recovery
     
    (n m : ℕ) (hn : n < w) (hm : m ≤ h) :
    rectangleCurlFlow a w h (rectangleFlowExteriorPotential a w h F)
        ⟨rectangleFlowVertex a (n : ℤ) (m : ℤ), LatticeAxis.horizontal⟩ =
      rectangleFlowH a w h F.1 (rectangleFlowX a (n : ℤ))
        (rectangleFlowY a (m : ℤ)) := by
  simp only [rectangleCurlFlow, LatticeBond.faceBase]
  have hface :
      ((rectangleFlowVertex a  n   m ).1,
        (rectangleFlowVertex a  n   m ).2 - 1) =
      rectangleFlowVertex a  n  ( m  - 1) := by
    ext <;> simp [rectangleFlowVertex, rectangleFlowY]; ring
  rw [hface]
  
  by_cases hm0 : m = 0
  · subst m
    rw [rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F n 0 hn (by omega)]
    have hbot := rectangleFlowPotentialBottomBoundary a w h F n (by omega)
    
    
    
    have hd := rectangleFlowRowDiff_sum a w h F n 0 (by omega) (by omega)
    
    rw [(rectangleFlowSideHorizontal_zero a w h F.1 0).1] at hd
    change  ∑ k ∈ Finset.range (n + 1),
      (rectangleFlowV a w h F.1 (rectangleFlowX a  k ) (rectangleFlowY a 0) -
        rectangleFlowV a w h F.1 (rectangleFlowX a  k ) (rectangleFlowY a (-1)))  =
      0 - rectangleFlowH a w h F.1 (rectangleFlowX a  n ) (rectangleFlowY a 0) at hd
    
    have hbot' :  ∑ k ∈ Finset.range (n + 1),
        rectangleFlowV a w h F.1 (rectangleFlowX a  k )
          (rectangleFlowY a (-1 ))  = 0 := by
      simpa  using  by
                                      apply Finset.sum_eq_zero
                                      intro k hk
                                      exact rectangleFlowBottomVertical_zero a w h F.1 k 
    rw [Finset.sum_sub_distrib] at hd
    rw [hbot'] at hd
    have hrec : rectangleFlowRowSumV a w h F.1 n 0 =
        -rectangleFlowH a w h F.1 (rectangleFlowX a  n )
          (rectangleFlowY a  0 ) := by
      simpa [rectangleFlowRowSumV] using hd
    simp_all
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    rw [rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F n (m + 1) hn hm]
    have hlow := rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F n m hn (by omega)
    
    
    
    have hd := rectangleFlowRowDiff_sum a w h F n (m + 1) (by omega) hm
    
    rw [(rectangleFlowSideHorizontal_zero a w h F.1 (m + 1)).1] at hd
    
    
    
    have hrec : rectangleFlowRowSumV a w h F.1 n (m + 1) -
        rectangleFlowRowSumV a w h F.1 n m =
        -rectangleFlowH a w h F.1 (rectangleFlowX a  n )
          (rectangleFlowY a  (m + 1 ) ) := by
      aesop
    grind

private theorem rectangleFlowVerticalOffset_recovery
     
    (n m : ℕ) (hn : n ≤ w) (hm : m < h) :
    rectangleCurlFlow a w h (rectangleFlowExteriorPotential a w h F)
        ⟨rectangleFlowVertex a (n : ℤ) (m : ℤ), LatticeAxis.vertical⟩ =
      rectangleFlowV a w h F.1 (rectangleFlowX a (n : ℤ))
        (rectangleFlowY a (m : ℤ)) := by
  simp only [rectangleCurlFlow, LatticeBond.faceBase]
  have hface :
      ((rectangleFlowVertex a  n   m ).1 - 1,
        (rectangleFlowVertex a  n   m ).2) =
      rectangleFlowVertex a ( n  - 1)  m  := by
    ext <;> simp [rectangleFlowVertex, rectangleFlowX]; ring
  rw [hface]
  
  by_cases hn0 : n = 0
  · subst n
    have hleftcoord : rectangleFlowVertex a ( (0 : ℕ)  - 1)  m  =
        rectangleFlowVertex a (-1)  m  := by
      simp 
    rw [hleftcoord]
    rw [rectangleFlowPotentialLeftBoundary a w h F m (by omega)]
    by_cases hw0 : w = 0
    · subst w
      rw [rectangleFlowPotentialAtOffset_right_zero a 0 h F m hm]
      
      have hval : rectangleFlowV a 0 h F.1 (rectangleFlowX a 0)
          (rectangleFlowY a  m ) = 0 := by
        simpa [rectangleFlowRowSumV] using  rectangleFlow_rowCutSum_zero a 0 h F m hm 
      simp_all
    · 
      rw [ rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F 0 m
             (by omega) (by omega) ]
      have hrow : rectangleFlowRowSumV a w h F.1 0 m =
          rectangleFlowV a w h F.1 (rectangleFlowX a 0) (rectangleFlowY a  m ) := by
        simp [rectangleFlowRowSumV]
      rw [hrow]
      ring
  · obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hleftcoord : rectangleFlowVertex a ( (n' + 1 : ℕ)  - 1)  m  =
        rectangleFlowVertex a  n'   m  := by
       simp
    rw [hleftcoord]
    
    have hrightPot : rectangleExtendedPotential a w h
        (rectangleFlowExteriorPotential a w h F)
        (rectangleFlowVertex a  n'.succ   m ) =
          -rectangleFlowRowSumV a w h F.1 n'.succ m := by
      by_cases hright : n'.succ < w
      · simpa  using
          rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F n'.succ m hright (by omega)
      · have hrightEq : n'.succ = w := by omega
        have hrowzero := rectangleFlow_rowCutSum_zero a w h F m hm
        
        rw [hrightEq]
        rw [rectangleFlowPotentialAtOffset_right_zero a w h F m hm]
        simp [hrowzero]
    rw [ rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F n' m
           (by omega) (by omega) , hrightPot]
    have hrec := rectangleFlowRowSumV_succ a w h F.1 n' m
    simp_all

/-- Every genuinely divergence-free rectangle flow is the curl of its normalized
zero-exterior dual potential on each actual rectangle edge. -/
theorem rectangleFlowExteriorPotential_curl_eq_flow
     
    (b : RectanglePrimalBond a w h) :
    rectangleCurlFlow a w h (rectangleFlowExteriorPotential a w h F) b.1 = F.1 b := by
  rcases b with ⟨⟨⟨x, y⟩, axis⟩, hb⟩
  cases axis
  · have hs := (mem_latticeRectangle a (x,y) w h).mp hb.1
    have ht := (mem_latticeRectangle a (x+1,y) w h).mp hb.2
    let n  := (x - a.1).toNat
    let m  := (y - a.2).toNat
    
    
    have hx : x = a.1 +  n  := by
      
      
      omega
    have hy : y = a.2 +  m  := by
      
      
      omega
    
    
    have hcoords : (x,y) = rectangleFlowVertex a  n   m  := by
      bound
    have hinside :
        (⟨(a.1 +  n , a.2 +  m ), LatticeAxis.horizontal⟩ : LatticeBond).source ∈
            latticeRectangle a w h ∧
          (⟨(a.1 +  n , a.2 +  m ), LatticeAxis.horizontal⟩ : LatticeBond).target ∈
            latticeRectangle a w h := by
      simp_all
    have hrec := rectangleFlowHorizontalOffset_recovery a w h F n m (by omega) (by omega)
    rw [← hcoords] at hrec
    simpa [rectangleFlowH, rectangleExtendedPrimalFlow, rectangleFlowX,
      rectangleFlowY, hx, hy, hinside] using hrec
  · have hs := (mem_latticeRectangle a (x,y) w h).mp hb.1
    have ht := (mem_latticeRectangle a (x,y+1) w h).mp hb.2
    let n  := (x - a.1).toNat
    let m  := (y - a.2).toNat
    
    
    have hx : x = a.1 +  n  := by
      
      
      omega
    have hy : y = a.2 +  m  := by
      
      
      omega
    
    
    have hcoords : (x,y) = rectangleFlowVertex a  n   m  := by
      bound
    have hinside :
        (⟨(a.1 +  n , a.2 +  m ), LatticeAxis.vertical⟩ : LatticeBond).source ∈
            latticeRectangle a w h ∧
          (⟨(a.1 +  n , a.2 + (m )), LatticeAxis.vertical⟩ : LatticeBond).target ∈
            latticeRectangle a w h := by
      simp_all
    have hrec := rectangleFlowVerticalOffset_recovery a w h F n m (by omega) (by omega)
    rw [← hcoords] at hrec
    simpa [rectangleFlowV, rectangleExtendedPrimalFlow, rectangleFlowX,
      rectangleFlowY, hx, hy, hinside] using hrec

end

end

end PottsDiscontinuity.FK
