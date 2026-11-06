/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleCurl
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

abbrev RectanglePrimalFlow (a : LatticeVertex) (w h : ℕ) :=
  RectanglePrimalBond a w h → ℝ

section
variable (a : LatticeVertex) (w h : ℕ) (F : RectanglePrimalFlow a w h)
def rectangleExtendedPrimalFlow (b : LatticeBond) : ℝ :=
  if hb : b.source ∈ latticeRectangle a w h ∧ b.target ∈ latticeRectangle a w h
  then F ⟨b, hb⟩ else 0

def rectanglePrimalFlowDivergence (v : LatticeVertex) : ℝ :=
  ∑ b : rectangleActualIncidentBonds a w h v,
    if b.1.1.source = v then F b.1 else -F b.1

def rectangleFlowH (x y : ℤ) : ℝ :=
  rectangleExtendedPrimalFlow a w h F ⟨(x,y), .horizontal⟩

def rectangleFlowV (x y : ℤ) : ℝ :=
  rectangleExtendedPrimalFlow a w h F ⟨(x,y), .vertical⟩
end

def rectangleFlowX (a : LatticeVertex) (n : ℤ) : ℤ := a.1 + n
def rectangleFlowY (a : LatticeVertex) (m : ℤ) : ℤ := a.2 + m

def rectangleFlowVertex (a : LatticeVertex) (n m : ℤ) : LatticeVertex :=
  (rectangleFlowX a n, rectangleFlowY a m)

section
variable (a : LatticeVertex) (w h : ℕ)
def rectangleFlowDivergenceStencil (F : RectanglePrimalFlow a w h) (v : LatticeVertex) : ℝ :=
  rectangleExtendedPrimalFlow a w h F ⟨v, .horizontal⟩ -
    rectangleExtendedPrimalFlow a w h F ⟨(v.1 - 1, v.2), .horizontal⟩ +
    rectangleExtendedPrimalFlow a w h F ⟨v, .vertical⟩ -
    rectangleExtendedPrimalFlow a w h F ⟨(v.1, v.2 - 1), .vertical⟩

/-- A flow with genuine zero incidence divergence at every primal vertex. -/
def RectangleDivergenceFreeFlow  :=
  {F : RectanglePrimalFlow a w h //
    ∀ v, v ∈ latticeRectangle a w h → rectanglePrimalFlowDivergence a w h F v = 0}
end

section
variable (a : LatticeVertex) (w h : ℕ) (F : RectanglePrimalFlow a w h) (v : LatticeVertex)
def rectangleFlowSignedCandidate (i : Fin 4) : ℝ :=
  if (rectangleCurlIncidentCandidate v i).source = v then
    rectangleExtendedPrimalFlow a w h F (rectangleCurlIncidentCandidate v i)
  else -rectangleExtendedPrimalFlow a w h F (rectangleCurlIncidentCandidate v i)

theorem rectangleFlowCandidate_outside_zero
    (i : Fin 4)
    (hout : ¬ rectangleCurlCandidateInside a w h v i) :
    rectangleExtendedPrimalFlow a w h F (rectangleCurlIncidentCandidate v i) = 0 := by
  simp only [rectangleExtendedPrimalFlow]
  split_ifs with hb
  · tauto
  rfl

theorem rectangleFlowSignedCandidate_eq_term
    (i : Fin 4)
    (hi : rectangleCurlCandidateInside a w h v i) :
    rectangleFlowSignedCandidate a w h F v i =
      match i.val with
      | 0 => rectangleFlowH a w h F v.1 v.2
      | 1 => -rectangleFlowH a w h F (v.1 - 1) v.2
      | 2 => rectangleFlowV a w h F v.1 v.2
      | _ => -rectangleFlowV a w h F v.1 (v.2 - 1) := by
  rcases v with ⟨x, y⟩
  fin_cases i
  · (grind [rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate, rectangleExtendedPrimalFlow, rectangleFlowH, LatticeBond.source])
  · have hn : (x - 1, y) ≠ (x, y) := by
      simp
    (simp [rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate,
      rectangleExtendedPrimalFlow, rectangleFlowH, LatticeBond.source, hn]) <;> rfl
  · (grind [rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate, rectangleExtendedPrimalFlow, rectangleFlowV, LatticeBond.source])
  · have hn : (x, y - 1) ≠ (x, y) := by
      simp
    (simp [rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate,
      rectangleExtendedPrimalFlow, rectangleFlowV, LatticeBond.source, hn]) <;> rfl

theorem rectanglePrimalFlowDivergence_eq_stencil
     :
    rectanglePrimalFlowDivergence a w h F v = rectangleFlowDivergenceStencil a w h F v := by
  classical
  let e := rectangleActualIncidentCandidateEquiv a w h v
  let p := rectangleCurlCandidateInside a w h v
  have hsub :
      (∑ i ∈ Finset.univ.filter p, rectangleFlowSignedCandidate a w h F v i) =
        (∑ i : {i : Fin 4 // p i}, rectangleFlowSignedCandidate a w h F v i.1) :=
    Finset.sum_subtype (p := p) (Finset.univ.filter p)
      (by simp)
      (fun i => rectangleFlowSignedCandidate a w h F v i)
  calc
    rectanglePrimalFlowDivergence a w h F v =
        ∑ b : rectangleActualIncidentBonds a w h v,
          rectangleFlowSignedCandidate a w h F v (e b).1 := by
      apply Finset.sum_congr rfl
      intro b hb
      have hmap : rectangleCurlIncidentCandidate v (e b).1 = b.1.1 :=
        congrArg (fun z : rectangleActualIncidentBonds a w h v => z.1.1) (e.left_inv b)
      grind [rectangleExtendedPrimalFlow, rectangleCurlIncidentCandidate, rectangleFlowSignedCandidate]
    _ = ∑ i : {i : Fin 4 // p i}, rectangleFlowSignedCandidate a w h F v i.1 :=
      Equiv.sum_comp e (fun i => rectangleFlowSignedCandidate a w h F v i.1)
    _ = rectangleFlowDivergenceStencil a w h F v := by
      rw [← hsub, Finset.sum_filter]
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
          · grind [rectangleFlowH, rectangleFlowV, rectangleFlowSignedCandidate_eq_term]
          · have hz := rectangleFlowCandidate_outside_zero a w h F v 0 hp
            simp_all [rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate, rectangleFlowH]
        · by_cases hp : p 1
          · grind [rectangleFlowH, rectangleFlowV, rectangleFlowSignedCandidate_eq_term]
          · have hz := rectangleFlowCandidate_outside_zero a w h F v 1 hp
            simp_all [rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate, rectangleFlowH]
        · by_cases hp : p 2
          · grind [rectangleFlowH, rectangleFlowV, rectangleFlowSignedCandidate_eq_term]
          · have hz := rectangleFlowCandidate_outside_zero a w h F v 2 hp
            simp_all [rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate, rectangleFlowV]
        · by_cases hp : p 3
          · grind [rectangleFlowH, rectangleFlowV, rectangleFlowSignedCandidate_eq_term]
          · have hz := rectangleFlowCandidate_outside_zero a w h F v 3 hp
            simp_all [rectangleFlowSignedCandidate, rectangleCurlIncidentCandidate, rectangleFlowV]
      simp_rw [hterm]
      simp [Fin.sum_univ_succ, rectangleFlowDivergenceStencil,
        rectangleFlowH, rectangleFlowV]
      ring_nf
end

section
variable (a : LatticeVertex) (w h : ℕ)
theorem rectangleFlowDivergenceStencil_offset
    (F : RectanglePrimalFlow a w h)
    (n m : ℤ) :
    rectangleFlowDivergenceStencil a w h F (rectangleFlowVertex a n m) =
      rectangleFlowH a w h F (rectangleFlowX a n) (rectangleFlowY a m) -
        rectangleFlowH a w h F (rectangleFlowX a (n - 1)) (rectangleFlowY a m) +
      rectangleFlowV a w h F (rectangleFlowX a n) (rectangleFlowY a m) -
        rectangleFlowV a w h F (rectangleFlowX a n) (rectangleFlowY a (m - 1)) := by
  grind [rectangleFlowDivergenceStencil, rectangleFlowH, rectangleFlowV, rectangleFlowVertex, rectangleFlowX, rectangleFlowY]

theorem rectangleFlowVertex_mem
    (n m : ℕ)
    (hn : n ≤ w) (hm : m ≤ h) :
    rectangleFlowVertex a (n : ℤ) (m : ℤ) ∈ latticeRectangle a w h := by
  rw [mem_latticeRectangle]
  simp_all [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]

def rectangleFlowRowSumV (F : RectanglePrimalFlow a w h) (n m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    rectangleFlowV a w h F (rectangleFlowX a (k : ℤ)) (rectangleFlowY a (m : ℤ))

theorem rectangleFlowOffsetDiv_zero
    (F : RectangleDivergenceFreeFlow a w h)
    (n m : ℕ) (hn : n ≤ w) (hm : m ≤ h) :
    rectangleFlowH a w h F.1 (rectangleFlowX a (n : ℤ)) (rectangleFlowY a (m : ℤ)) -
      rectangleFlowH a w h F.1 (rectangleFlowX a ((n : ℤ) - 1)) (rectangleFlowY a (m : ℤ)) +
      rectangleFlowV a w h F.1 (rectangleFlowX a (n : ℤ)) (rectangleFlowY a (m : ℤ)) -
      rectangleFlowV a w h F.1 (rectangleFlowX a (n : ℤ)) (rectangleFlowY a ((m : ℤ) - 1)) = 0 := by
  have hv := rectangleFlowVertex_mem a w h n m hn hm
  grind [rectanglePrimalFlowDivergence_eq_stencil, rectangleFlowDivergenceStencil_offset]

theorem rectangleFlowRowDiff_sum
    (F : RectangleDivergenceFreeFlow a w h)
    (n m : ℕ) (hn : n ≤ w) (hm : m ≤ h) :
    (∑ k ∈ Finset.range (n + 1),
      (rectangleFlowV a w h F.1 (rectangleFlowX a (k : ℤ)) (rectangleFlowY a (m : ℤ)) -
        rectangleFlowV a w h F.1 (rectangleFlowX a (k : ℤ))
          (rectangleFlowY a ((m : ℤ) - 1)))) =
      rectangleFlowH a w h F.1 (rectangleFlowX a ((0 : ℤ) - 1)) (rectangleFlowY a (m : ℤ)) -
        rectangleFlowH a w h F.1 (rectangleFlowX a (n : ℤ)) (rectangleFlowY a (m : ℤ)) := by
  induction n with
  | zero =>
      have hd := rectangleFlowOffsetDiv_zero a w h F 0 m (by omega) hm
      simp at hd ⊢
      linarith
  | succ n ih =>
      have hd := rectangleFlowOffsetDiv_zero a w h F (n + 1) m (by omega) hm
      rw [Finset.sum_range_succ]
      grind

theorem rectangleFlowSideHorizontal_zero
    (F : RectanglePrimalFlow a w h)
    (m : ℕ) :
    rectangleFlowH a w h F (rectangleFlowX a ((0 : ℤ) - 1))
        (rectangleFlowY a (m : ℤ)) = 0 ∧
    rectangleFlowH a w h F (rectangleFlowX a (w : ℤ))
        (rectangleFlowY a (m : ℤ)) = 0 := by
  constructor
  · simp [rectangleFlowH, rectangleFlowX, rectangleFlowY,
      rectangleExtendedPrimalFlow, LatticeBond.source, LatticeBond.target,
      mem_latticeRectangle]
  · simp [rectangleFlowH, rectangleFlowX, rectangleFlowY,
      rectangleExtendedPrimalFlow, LatticeBond.source, LatticeBond.target,
      mem_latticeRectangle]

theorem rectangleFlowBottomVertical_zero
    (F : RectanglePrimalFlow a w h)
    (k : ℕ) :
    rectangleFlowV a w h F (rectangleFlowX a (k : ℤ))
      (rectangleFlowY a ((0 : ℤ) - 1)) = 0 := by
  simp [rectangleFlowV, rectangleFlowX, rectangleFlowY,
    rectangleExtendedPrimalFlow, LatticeBond.source, LatticeBond.target,
    mem_latticeRectangle]

theorem rectangleFlow_rowCutSum_zero
    (F : RectangleDivergenceFreeFlow a w h)
    (m : ℕ) (hm : m < h) :
    rectangleFlowRowSumV a w h F.1 w m = 0 := by
  have hrow (j : ℕ) (hj : j ≤ h) : rectangleFlowRowSumV a w h F.1 w j = 0 := by
    induction j with
    | zero =>
        have hd := rectangleFlowRowDiff_sum a w h F w 0 (by omega) (by omega)
        grind [rectangleFlowSideHorizontal_zero, rectangleFlowBottomVertical_zero, Finset.range, rectangleFlowV, rectangleFlowX, rectangleFlowY, rectangleFlowRowSumV]
    | succ j ih =>
        have hd := rectangleFlowRowDiff_sum a w h F w (j + 1) (by omega) hj
        have hs := rectangleFlowSideHorizontal_zero a w h F.1 (j + 1)
        have hdiff :
            rectangleFlowRowSumV a w h F.1 w (j + 1) -
              rectangleFlowRowSumV a w h F.1 w j = 0 := by
          simp_all [rectangleFlowRowSumV]
        grind
  grind

theorem rectangleFlowVerticalTop_zero
    (F : RectanglePrimalFlow a w h)
    (n : ℕ) :
    rectangleFlowV a w h F (rectangleFlowX a (n : ℤ))
      (rectangleFlowY a (h : ℤ)) = 0 := by
  simp [rectangleFlowV, rectangleFlowX, rectangleFlowY,
    rectangleExtendedPrimalFlow, LatticeBond.source, LatticeBond.target,
    mem_latticeRectangle]

theorem rectangleFlowRowSumV_top_zero
    (F : RectanglePrimalFlow a w h)
    (n : ℕ) : rectangleFlowRowSumV a w h F n h = 0 := by
  simp [rectangleFlowRowSumV, rectangleFlowVerticalTop_zero]

def rectangleFlowPotentialValue (F : RectangleDivergenceFreeFlow a w h) (z : LatticeVertex) : ℝ :=
  if _hz : z ∈ rectangleDualInterior a w h then
    -(∑ k ∈ Finset.range ((z.1 - a.1).toNat + 1),
      rectangleFlowV a w h F.1 (rectangleFlowX a (k : ℤ)) z.2)
  else 0
end

section
variable (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h)
def rectangleFlowExteriorPotential
     :
    RectangleExteriorPotential a w h := by
  refine ⟨fun z => rectangleFlowPotentialValue a w h F z.1, ?_⟩
  simp_all [rectangleDualBoundary, rectangleFlowPotentialValue]

theorem rectangleFlowExtendedPotential_eq_value
    (z : LatticeVertex) (hz : z ∈ rectangleDualExpanded a w h) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F) z =
      rectangleFlowPotentialValue a w h F z := by
  aesop

theorem rectangleFlowPotentialLeftBoundary
    (m : ℕ) (hm : m ≤ h) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (-1) (m : ℤ)) = 0 := by
  have hex : rectangleFlowVertex a (-1) (m : ℤ) ∈ rectangleDualExpanded a w h := by
    rw [rectangleDualExpanded, mem_latticeRectangle]
    grind [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
  grind [rectangleFlowExtendedPotential_eq_value, rectangleFlowVertex, rectangleDualInterior, rectangleFlowX, rectangleFlowPotentialValue]

theorem rectangleFlowPotentialBottomBoundary
    (n : ℕ) (hn : n ≤ w) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (n : ℤ) (-1)) = 0 := by
  have hex : rectangleFlowVertex a (n : ℤ) (-1) ∈ rectangleDualExpanded a w h := by
    rw [rectangleDualExpanded, mem_latticeRectangle]
    grind [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
  grind [rectangleFlowExtendedPotential_eq_value, rectangleFlowVertex, rectangleDualInterior, rectangleFlowY, rectangleFlowPotentialValue]

theorem rectangleFlowPotentialValue_interior
    (n m : ℕ) (hn : n < w) (hm : m < h) :
    rectangleFlowPotentialValue a w h F
      (rectangleFlowVertex a (n : ℤ) (m : ℤ)) =
        -rectangleFlowRowSumV a w h F.1 n m := by
  have hex : rectangleFlowVertex a (n : ℤ) (m : ℤ) ∈ rectangleDualExpanded a w h := by
    rw [rectangleDualExpanded, mem_latticeRectangle]
    grind [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
  simp_all [rectangleFlowVertex, rectangleDualInterior, rectangleFlowX, rectangleFlowY, rectangleFlowPotentialValue, rectangleFlowRowSumV]
end

theorem rectangleFlowVertex_mem_interior_iff
    (a : LatticeVertex) (w h : ℕ) (n m : ℕ) :
    rectangleFlowVertex a (n : ℤ) (m : ℤ) ∈ rectangleDualInterior a w h ↔
      n < w ∧ m < h := by
  grind [rectangleDualInterior, rectangleDualExpanded, latticeRectangle, rectangleFlowVertex, rectangleFlowX, rectangleFlowY]

section
variable (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h) (n m : ℕ)
theorem rectangleFlowPotentialValue_face
     :
    rectangleFlowPotentialValue a w h F
      (rectangleFlowVertex a (n : ℤ) (m : ℤ)) =
      if n < w ∧ m < h then -rectangleFlowRowSumV a w h F.1 n m else 0 := by
  grind [rectangleFlowVertex_mem_interior_iff, rectangleFlowPotentialValue_interior, rectangleFlowVertex, rectangleDualInterior, rectangleFlowPotentialValue]

theorem rectangleFlowPotentialAtOffset
    (hn : n ≤ w) (hm : m ≤ h) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (n : ℤ) (m : ℤ)) =
        if n < w ∧ m < h then -rectangleFlowRowSumV a w h F.1 n m else 0 := by
  have hex : rectangleFlowVertex a (n : ℤ) (m : ℤ) ∈ rectangleDualExpanded a w h := by
    rw [rectangleDualExpanded, mem_latticeRectangle]
    grind [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
  grind [rectangleFlowExtendedPotential_eq_value, rectangleFlowPotentialValue_face]

theorem rectangleFlowPotentialAtOffset_eq_neg_rowSum
    (hn : n < w) (hm : m ≤ h) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (n : ℤ) (m : ℤ)) =
      -rectangleFlowRowSumV a w h F.1 n m := by
  grind [rectangleFlowPotentialAtOffset, rectangleFlowRowSumV_top_zero]
end

section
variable (a : LatticeVertex) (w h : ℕ)
theorem rectangleFlowPotentialAtOffset_right_zero
    (F : RectangleDivergenceFreeFlow a w h)
    (m : ℕ) (hm : m < h) :
    rectangleExtendedPotential a w h (rectangleFlowExteriorPotential a w h F)
      (rectangleFlowVertex a (w : ℤ) (m : ℤ)) = 0 := by
  grind [rectangleFlowPotentialAtOffset]

theorem rectangleFlowRowSumV_succ
    (F : RectanglePrimalFlow a w h)
    (n m : ℕ) :
    rectangleFlowRowSumV a w h F (n + 1) m =
      rectangleFlowRowSumV a w h F n m +
        rectangleFlowV a w h F (rectangleFlowX a ((n + 1 : ℕ) : ℤ))
          (rectangleFlowY a (m : ℤ)) := by
  simp [rectangleFlowRowSumV, Finset.sum_range_succ]
end

section
variable (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h)
theorem rectangleFlowHorizontalOffset_recovery
    (n m : ℕ) (hn : n < w) (hm : m ≤ h) :
    rectangleCurlFlow a w h (rectangleFlowExteriorPotential a w h F)
        ⟨rectangleFlowVertex a (n : ℤ) (m : ℤ), LatticeAxis.horizontal⟩ =
      rectangleFlowH a w h F.1 (rectangleFlowX a (n : ℤ))
        (rectangleFlowY a (m : ℤ)) := by
  simp only [rectangleCurlFlow, LatticeBond.faceBase]
  have hface :
      ((rectangleFlowVertex a (n : ℤ) (m : ℤ)).1,
        (rectangleFlowVertex a (n : ℤ) (m : ℤ)).2 - 1) =
      rectangleFlowVertex a (n : ℤ) ((m : ℤ) - 1) := by
    grind [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
  rw [hface]
  by_cases hm0 : m = 0
  · subst m
    rw [rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F n 0 hn (by omega)]
    have hbot := rectangleFlowPotentialBottomBoundary a w h F n (by omega)
    have hd := rectangleFlowRowDiff_sum a w h F n 0 (by omega) (by omega)
    grind [rectangleFlowSideHorizontal_zero, Finset.range, rectangleFlowV, rectangleFlowX, rectangleFlowY, rectangleFlowH, rectangleFlowBottomVertical_zero, rectangleFlowRowSumV]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    rw [rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F n (m + 1) hn hm]
    have hlow := rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F n m hn (by omega)
    have hlow' : rectangleExtendedPotential a w h
        (rectangleFlowExteriorPotential a w h F)
        (rectangleFlowVertex a (n : ℤ) (((m.succ : ℕ) : ℤ) - 1)) =
          -rectangleFlowRowSumV a w h F.1 n m := by
      simp_all
    have hd := rectangleFlowRowDiff_sum a w h F n (m + 1) (by omega) hm
    have hs := rectangleFlowSideHorizontal_zero a w h F.1 (m + 1)
    have hrec : rectangleFlowRowSumV a w h F.1 n (m + 1) -
        rectangleFlowRowSumV a w h F.1 n m =
        -rectangleFlowH a w h F.1 (rectangleFlowX a (n : ℤ))
          (rectangleFlowY a ((m + 1 : ℕ) : ℤ)) := by
      simp_all [rectangleFlowRowSumV, rectangleFlowY]
    linarith

theorem rectangleFlowVerticalOffset_recovery
    (n m : ℕ) (hn : n ≤ w) (hm : m < h) :
    rectangleCurlFlow a w h (rectangleFlowExteriorPotential a w h F)
        ⟨rectangleFlowVertex a (n : ℤ) (m : ℤ), LatticeAxis.vertical⟩ =
      rectangleFlowV a w h F.1 (rectangleFlowX a (n : ℤ))
        (rectangleFlowY a (m : ℤ)) := by
  simp only [rectangleCurlFlow, LatticeBond.faceBase]
  have hface :
      ((rectangleFlowVertex a (n : ℤ) (m : ℤ)).1 - 1,
        (rectangleFlowVertex a (n : ℤ) (m : ℤ)).2) =
      rectangleFlowVertex a ((n : ℤ) - 1) (m : ℤ) := by
    grind [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
  rw [hface]
  by_cases hn0 : n = 0
  · subst n
    have hleftcoord : rectangleFlowVertex a (((0 : ℕ) : ℤ) - 1) (m : ℤ) =
        rectangleFlowVertex a (-1) (m : ℤ) := by
      rfl
    rw [hleftcoord, rectangleFlowPotentialLeftBoundary a w h F m (by omega)]
    by_cases hw0 : w = 0
    · subst w
      rw [rectangleFlowPotentialAtOffset_right_zero a 0 h F m hm]
      have hrow := rectangleFlow_rowCutSum_zero a 0 h F m hm
      simp_all [rectangleFlowV, rectangleFlowX, rectangleFlowY, rectangleFlowRowSumV]
    · have hpot := rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F 0 m
        (by omega) (by omega)
      simp_all [rectangleFlowRowSumV, rectangleFlowV, rectangleFlowX, rectangleFlowY]
  · obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hleft := rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F n' m
      (by omega) (by omega)
    have hrightPot : rectangleExtendedPotential a w h
        (rectangleFlowExteriorPotential a w h F)
        (rectangleFlowVertex a (n'.succ : ℤ) (m : ℤ)) =
          -rectangleFlowRowSumV a w h F.1 n'.succ m := by
      by_cases hright : n'.succ < w
      · simpa [Nat.succ_eq_add_one] using
          rectangleFlowPotentialAtOffset_eq_neg_rowSum a w h F n'.succ m hright (by omega)
      · have hrightEq : n'.succ = w := by omega
        have hrowzero := rectangleFlow_rowCutSum_zero a w h F m hm
        simp_all [rectangleFlowRowSumV, rectangleFlowPotentialAtOffset_right_zero]
    grind [rectangleFlowRowSumV_succ, rectangleFlowRowSumV, rectangleFlowV, rectangleFlowX, rectangleFlowY]

/-- Every genuinely divergence-free rectangle flow is the curl of its normalized
zero-exterior dual potential on each actual rectangle edge. -/
theorem rectangleFlowExteriorPotential_curl_eq_flow
    (b : RectanglePrimalBond a w h) :
    rectangleCurlFlow a w h (rectangleFlowExteriorPotential a w h F) b.1 = F.1 b := by
  rcases b with ⟨⟨⟨x, y⟩, axis⟩, hb⟩
  cases axis
  · have hs := (mem_latticeRectangle a (x,y) w h).mp hb.1
    let n := (x - a.1).toNat
    let m := (y - a.2).toNat
    have hx : x = a.1 + (n : ℤ) := by
      omega
    have hy : y = a.2 + (m : ℤ) := by
      omega
    have hcoords : (x,y) = rectangleFlowVertex a (n : ℤ) (m : ℤ) := by
      simp_all [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
    grind [latticeRectangle, LatticeBond.source, LatticeBond.target, rectangleFlowHorizontalOffset_recovery, rectangleFlowH, rectangleExtendedPrimalFlow, rectangleFlowX, rectangleFlowY]
  · have hs := (mem_latticeRectangle a (x,y) w h).mp hb.1
    let n := (x - a.1).toNat
    let m := (y - a.2).toNat
    have hx : x = a.1 + (n : ℤ) := by
      omega
    have hy : y = a.2 + (m : ℤ) := by
      omega
    have hcoords : (x,y) = rectangleFlowVertex a (n : ℤ) (m : ℤ) := by
      simp_all [rectangleFlowVertex, rectangleFlowX, rectangleFlowY]
    grind [latticeRectangle, LatticeBond.source, LatticeBond.target, rectangleFlowVerticalOffset_recovery, rectangleFlowV, rectangleExtendedPrimalFlow, rectangleFlowX, rectangleFlowY]
end

end PottsDiscontinuity.FK
