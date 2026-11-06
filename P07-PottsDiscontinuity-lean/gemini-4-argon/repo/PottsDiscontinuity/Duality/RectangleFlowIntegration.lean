module

public import PottsDiscontinuity.Duality.RectangleCurl
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

abbrev RectanglePrimalFlow (a : LatticeVertex) (w h : ℕ) :=
  RectanglePrimalBond a w h → ℝ

def rectangleExtendedPrimalFlow (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (b : LatticeBond) : ℝ :=
  if hb : b.source ∈ latticeRectangle a w h ∧ b.target ∈ latticeRectangle a w h
  then F ⟨b, hb⟩ else 0

noncomputable def rectanglePrimalFlowDivergence (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (v : LatticeVertex) : ℝ :=
  ∑ b : rectangleActualIncidentBonds a w h v,
    if b.1.1.source = v then F b.1 else -F b.1

def rectangleFlowH (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (x y : ℤ) : ℝ :=
  rectangleExtendedPrimalFlow a w h F ⟨(x,y), .horizontal⟩

def rectangleFlowV (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (x y : ℤ) : ℝ :=
  rectangleExtendedPrimalFlow a w h F ⟨(x,y), .vertical⟩

def rectangleFlowX (a : LatticeVertex) (n : ℤ) : ℤ := a.1 + n
def rectangleFlowY (a : LatticeVertex) (m : ℤ) : ℤ := a.2 + m

def rectangleFlowVertex (a : LatticeVertex) (n m : ℤ) : LatticeVertex :=
  (rectangleFlowX a n, rectangleFlowY a m)

def rectangleFlowDivergenceStencil (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (v : LatticeVertex) : ℝ :=
  rectangleExtendedPrimalFlow a w h F ⟨v, .horizontal⟩ -
    rectangleExtendedPrimalFlow a w h F ⟨(v.1 - 1, v.2), .horizontal⟩ +
    rectangleExtendedPrimalFlow a w h F ⟨v, .vertical⟩ -
    rectangleExtendedPrimalFlow a w h F ⟨(v.1, v.2 - 1), .vertical⟩

/-- A flow with genuine zero incidence divergence at every primal vertex. -/
abbrev RectangleDivergenceFreeFlow (a : LatticeVertex) (w h : ℕ) :=
  {F : RectanglePrimalFlow a w h //
    ∀ v, v ∈ latticeRectangle a w h → rectanglePrimalFlowDivergence a w h F v = 0}

def rectangleFlowSignedCandidate (a : LatticeVertex) (w h : ℕ)
    (F : RectanglePrimalFlow a w h) (v : LatticeVertex) (i : Fin 4) : ℝ :=
  if (rectangleCurlIncidentCandidate v i).source = v then
    rectangleExtendedPrimalFlow a w h F (rectangleCurlIncidentCandidate v i)
  else -rectangleExtendedPrimalFlow a w h F (rectangleCurlIncidentCandidate v i)

open Classical in
private theorem rectangleFlowCandidate_term
    (a : LatticeVertex) (w h : ℕ) (F : RectanglePrimalFlow a w h)
    (v : LatticeVertex) (i : Fin 4) :
    (if rectangleCurlCandidateInside a w h v i then
      rectangleFlowSignedCandidate a w h F v i else 0) =
      match i.val with
      | 0 => rectangleFlowH a w h F v.1 v.2
      | 1 => -rectangleFlowH a w h F (v.1 - 1) v.2
      | 2 => rectangleFlowV a w h F v.1 v.2
      | _ => -rectangleFlowV a w h F v.1 (v.2 - 1) := by
  rcases v with ⟨x, y⟩
  have h1 : (x - 1, y) ≠ (x, y) := fun hh => by have := congrArg Prod.fst hh; omega
  have h3 : (x, y - 1) ≠ (x, y) := fun hh => by have := congrArg Prod.snd hh; omega
  fin_cases i <;>
    (simp [rectangleCurlCandidateInside, rectangleFlowSignedCandidate,
      rectangleCurlIncidentCandidate, rectangleExtendedPrimalFlow,
      rectangleFlowH, rectangleFlowV, LatticeBond.source, h1, h3];
     split_ifs with h <;> simp [h])

theorem rectanglePrimalFlowDivergence_eq_stencil
    (a : LatticeVertex) (w h : ℕ) (F : RectanglePrimalFlow a w h)
    (v : LatticeVertex) :
    rectanglePrimalFlowDivergence a w h F v = rectangleFlowDivergenceStencil a w h F v := by
  classical
  let e := rectangleActualIncidentCandidateEquiv a w h v
  let p : Fin 4 → Prop := rectangleCurlCandidateInside a w h v
  calc
    rectanglePrimalFlowDivergence a w h F v =
        ∑ b : rectangleActualIncidentBonds a w h v,
          rectangleFlowSignedCandidate a w h F v (e b).1 := by
      refine Finset.sum_congr rfl fun b _ => ?_
      have hmap : rectangleCurlIncidentCandidate v (e b).1 = b.1.1 :=
        congrArg (fun z : rectangleActualIncidentBonds a w h v => z.1.1) (e.left_inv b)
      simp [rectangleFlowSignedCandidate, hmap, rectangleExtendedPrimalFlow, b.1.2]
    _ = ∑ i : {i : Fin 4 // p i}, rectangleFlowSignedCandidate a w h F v i.1 :=
      Equiv.sum_comp e (fun i => rectangleFlowSignedCandidate a w h F v i.1)
    _ = rectangleFlowDivergenceStencil a w h F v := by
      rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp [p]) _, Finset.sum_filter]
      change (∑ i : Fin 4,
        if rectangleCurlCandidateInside a w h v i then
          rectangleFlowSignedCandidate a w h F v i else 0) = _
      simp_rw [rectangleFlowCandidate_term]
      simp [Fin.sum_univ_four, rectangleFlowDivergenceStencil, rectangleFlowH, rectangleFlowV]
      ring

def rectangleFlowPotentialValue (a : LatticeVertex) (w h : ℕ)
    (F : RectangleDivergenceFreeFlow a w h) (z : LatticeVertex) : ℝ :=
  - ∑ k ∈ Finset.Icc a.1 z.1, rectangleFlowV a w h F.1 k z.2

lemma rectangleFlowPotentialValue_vert_step (a : LatticeVertex) (w h : ℕ)
    (F : RectangleDivergenceFreeFlow a w h) (x y : ℤ) (hx : a.1 ≤ x) :
    rectangleFlowPotentialValue a w h F (x - 1, y) -
      rectangleFlowPotentialValue a w h F (x, y) =
      rectangleFlowV a w h F.1 x y := by
  unfold rectangleFlowPotentialValue; dsimp
  rw [show Finset.Icc a.1 x = insert x (Finset.Icc a.1 (x - 1)) by ext k; simp; omega,
    Finset.sum_insert (by simp)]
  ring

lemma rectangleFlowPotentialValue_horiz_step (a : LatticeVertex) (w h : ℕ)
    (F : RectangleDivergenceFreeFlow a w h) (x y : ℤ)
    (hx0 : a.1 ≤ x) (hx1 : x ≤ a.1 + (w : ℤ))
    (hy0 : a.2 ≤ y) (hy1 : y ≤ a.2 + (h : ℤ)) :
    rectangleFlowPotentialValue a w h F (x, y) -
      rectangleFlowPotentialValue a w h F (x, y - 1) =
      rectangleFlowH a w h F.1 x y := by
  have hdiv (k : ℤ) (hk0 : a.1 ≤ k) (hk1 : k ≤ a.1 + (w : ℤ)) :
      rectangleFlowV a w h F.1 k (y - 1) - rectangleFlowV a w h F.1 k y =
        rectangleFlowH a w h F.1 k y - rectangleFlowH a w h F.1 (k - 1) y := by
    have hz := F.2 (k, y) ((mem_latticeRectangle _ _ _ _).mpr ⟨⟨hk0, hk1⟩, ⟨hy0, hy1⟩⟩)
    rw [rectanglePrimalFlowDivergence_eq_stencil] at hz
    dsimp [rectangleFlowDivergenceStencil, rectangleFlowH, rectangleFlowV] at hz ⊢
    linarith
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, x = a.1 + (n : ℤ) := ⟨(x - a.1).toNat, by omega⟩
  induction n with
  | zero =>
    unfold rectangleFlowPotentialValue
    simp only [Nat.cast_zero, add_zero, Finset.Icc_self, Finset.sum_singleton]
    have hd := hdiv a.1 le_rfl (by omega)
    have hleft : rectangleFlowH a w h F.1 (a.1 - 1) y = 0 := by
      simp [rectangleFlowH, rectangleExtendedPrimalFlow, LatticeBond.source, mem_latticeRectangle]
    linarith
  | succ n ih =>
    have hstep1 := rectangleFlowPotentialValue_vert_step a w h F (a.1 + ((n + 1 : ℕ) : ℤ)) y (by omega)
    have hstep2 := rectangleFlowPotentialValue_vert_step a w h F (a.1 + ((n + 1 : ℕ) : ℤ)) (y - 1) (by omega)
    have hprev : a.1 + ((n + 1 : ℕ) : ℤ) - 1 = a.1 + (n : ℤ) := by push_cast; ring
    have hd := hdiv (a.1 + ((n + 1 : ℕ) : ℤ)) (by omega) hx1
    rw [hprev] at hstep1 hstep2 hd
    linarith [ih (by omega) (by omega)]

noncomputable def rectangleFlowExteriorPotential
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h) :
    RectangleExteriorPotential a w h := by
  refine ⟨fun z => rectangleFlowPotentialValue a w h F z.1, ?_⟩
  rintro ⟨⟨x, y⟩, hmem⟩ hbd
  rw [rectangleDualBoundary, Finset.mem_filter, rectangleDualInterior, Finset.mem_filter] at hbd
  rcases (mem_latticeRectangle _ (x, y) _ _).1 hmem with ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
  have hnot : ¬ (a.1 ≤ x ∧ x < a.1 + (w : ℤ) ∧ a.2 ≤ y ∧ y < a.2 + (h : ℤ)) :=
    fun h => hbd.2 ⟨hmem, h⟩
  dsimp at hx0 hx1 hy0 hy1 ⊢
  have hvzero (y' : ℤ) (hy' : y' < a.2 ∨ a.2 + (h : ℤ) ≤ y') :
      rectangleFlowPotentialValue a w h F (x, y') = 0 := by
    unfold rectangleFlowPotentialValue; dsimp
    rw [Finset.sum_eq_zero, neg_zero]
    intro k _
    unfold rectangleFlowV rectangleExtendedPrimalFlow
    rw [dite_eq_right_iff]; intro hk
    simp only [LatticeBond.source, LatticeBond.target, mem_latticeRectangle] at hk; omega
  by_cases hx : x < a.1
  · unfold rectangleFlowPotentialValue; dsimp
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, neg_zero]
  · by_cases hy : y < a.2 ∨ a.2 + (h : ℤ) ≤ y
    · exact hvzero y hy
    · have hxr : x = a.1 + (w : ℤ) := by omega
      subst hxr
      have hright (m : ℕ) (hm : m ≤ h) :
          rectangleFlowPotentialValue a w h F (a.1 + (w : ℤ), a.2 - 1 + (m : ℤ)) = 0 := by
        induction m with
        | zero => exact hvzero _ (Or.inl (by omega))
        | succ m ih =>
          have hstep := rectangleFlowPotentialValue_horiz_step a w h F (a.1 + (w : ℤ))
            (a.2 - 1 + ((m + 1 : ℕ) : ℤ)) (by omega) le_rfl (by omega) (by omega)
          have hprev : a.2 - 1 + ((m + 1 : ℕ) : ℤ) - 1 = a.2 - 1 + (m : ℤ) := by push_cast; ring
          have hH0 : rectangleFlowH a w h F.1 (a.1 + (w : ℤ)) (a.2 - 1 + ((m + 1 : ℕ) : ℤ)) = 0 := by
            unfold rectangleFlowH rectangleExtendedPrimalFlow
            rw [dite_eq_right_iff]; intro hk
            simp only [LatticeBond.target, mem_latticeRectangle] at hk; omega
          rw [hprev, ih (by omega), hH0, sub_zero] at hstep
          exact hstep
      rw [show (a.1 + (w : ℤ), y) = (a.1 + (w : ℤ), a.2 - 1 + (((y - (a.2 - 1)).toNat : ℕ) : ℤ)) by
        ext <;> omega]
      exact hright _ (by omega)

/-- Every genuinely divergence-free rectangle flow is the curl of its normalized
zero-exterior dual potential on each actual rectangle edge. -/
theorem rectangleFlowExteriorPotential_curl_eq_flow
    (a : LatticeVertex) (w h : ℕ) (F : RectangleDivergenceFreeFlow a w h)
    (b : RectanglePrimalBond a w h) :
    rectangleCurlFlow a w h (rectangleFlowExteriorPotential a w h F) b.1 = F.1 b := by
  rcases b with ⟨⟨⟨x, y⟩, axis⟩, hb⟩
  have hs_mem := (mem_latticeRectangle a _ w h).1 hb.1
  have ht_mem := (mem_latticeRectangle a _ w h).1 hb.2
  cases axis <;> dsimp [LatticeBond.source, LatticeBond.target] at hs_mem ht_mem <;>
    dsimp [rectangleCurlFlow, LatticeBond.faceBase]
  · rw [rectangleExtendedPotential_of_mem _ _ _ _ _
        (by rw [rectangleDualExpanded, mem_latticeRectangle]; dsimp; omega),
      rectangleExtendedPotential_of_mem _ _ _ _ _
        (by rw [rectangleDualExpanded, mem_latticeRectangle]; dsimp; omega)]
    exact (rectangleFlowPotentialValue_horiz_step a w h F x y
      hs_mem.1.1 (by omega) hs_mem.2.1 hs_mem.2.2).trans
      (by simp [rectangleFlowH, rectangleExtendedPrimalFlow, hb])
  · rw [rectangleExtendedPotential_of_mem _ _ _ _ _
        (by rw [rectangleDualExpanded, mem_latticeRectangle]; dsimp; omega),
      rectangleExtendedPotential_of_mem _ _ _ _ _
        (by rw [rectangleDualExpanded, mem_latticeRectangle]; dsimp; omega)]
    exact (rectangleFlowPotentialValue_vert_step a w h F x y hs_mem.1.1).trans
      (by simp [rectangleFlowV, rectangleExtendedPrimalFlow, hb])

end PottsDiscontinuity.FK
