import Mathlib.Tactic

import RequestProject.OrderNerveCharacteristicMap

namespace FiniteChains.Comb
open CategoryTheory Simplicial

variable {P : Type}
/-- Closed characteristic cells are precisely the canonical simplex images. -/
theorem orderNerveCharacteristicMap_closedCell  [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    orderNerveCharacteristicMap s '' Metric.closedBall 0 1 =
      Set.range (orderNerveRealizationSimplex P s.val) := by
  rw [← orderNerveClosedBallChart_range s]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, (orderNerveCharacteristicFunction_closedBall s ⟨u, hu⟩).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u.val, u.property, orderNerveCharacteristicFunction_closedBall s u⟩

/-- The open characteristic cell consists exactly of the positive-coordinate simplex points. -/
theorem orderNerveCharacteristicMap_openCell  [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    orderNerveCharacteristicMap s '' Metric.ball 0 1 =
      {x | ∃ z : SimplexCategory.toTop.obj ⦋n⦌,
        (∀ i, 0 < z.down.weights i) ∧ orderNerveRealizationSimplex P s.val z = x} := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hc := Metric.ball_subset_closedBall hu
    let v : (Metric.closedBall 0 1 : Set (Fin n → ℝ)) := ⟨u, hc⟩
    let z := (orderNerveSimplexClosedBallHomeomorph n).symm v
    refine ⟨ULift.up z, ?_, ?_⟩
    · apply (orderNerveSimplexClosedBallHomeomorph_positive_iff n z).mpr
      
      rw [Homeomorph.apply_symm_apply]
      exact hu
    · exact (orderNerveCharacteristicFunction_closedBall s v).symm
  · rintro ⟨z, hz, rfl⟩
    let u := orderNerveSimplexClosedBallHomeomorph n z.down
    have hu : u.val ∈ Metric.ball 0 1 :=
      (orderNerveSimplexClosedBallHomeomorph_positive_iff n z.down).mp hz
    refine ⟨u.val, hu, ?_⟩
    rw [show orderNerveCharacteristicMap s u.val = orderNerveClosedBallChart s u from
      orderNerveCharacteristicFunction_closedBall s u]
    dsimp [FiniteChains.Comb.orderNerveClosedBallChart]
    rw [Homeomorph.symm_apply_apply]
    rfl

variable (P : Type)
/-- The actual characteristic open cells are pairwise disjoint in all dimensions. -/
theorem orderNerveCharacteristicMap_pairwiseDisjoint  [PartialOrder P] :
    (Set.univ : Set (Σ n, (nerve P).nonDegenerate n)).PairwiseDisjoint
      (fun a => orderNerveCharacteristicMap a.2 '' Metric.ball 0 1) := by
  intro a _ b _ hab
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  rcases a with ⟨n, s⟩
  rcases b with ⟨m, t⟩
  dsimp at hxa hxb
  rw [orderNerveCharacteristicMap_openCell] at hxa hxb
  obtain ⟨z, hz, hx⟩ := hxa
  obtain ⟨w, hw, hy⟩ := hxb
  have he := hx.trans hy.symm
  have hnm := orderNerveRealization_nonDegenerate_interior_dimension_eq s t z w hz hw he
  subst m
  have hst := orderNerveRealization_nonDegenerate_interior_eq s t z w hz hw he
  subst t
  exact hab rfl

/-- The actual closed characteristic cells cover the entire realization. -/
theorem orderNerveCharacteristicMap_union  [PartialOrder P] :
    (⋃ (n : ℕ) (s : (nerve P).nonDegenerate n),
      orderNerveCharacteristicMap s '' Metric.closedBall 0 1) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n, s, z, hz⟩ := orderNerveRealization_nonDegenerate_jointly_surjective P x
  apply Set.mem_iUnion.mpr
  refine ⟨n, Set.mem_iUnion.mpr ⟨s, ?_⟩⟩
  rw [orderNerveCharacteristicMap_closedCell]
  exact ⟨z, hz⟩

/-- The characteristic closed cells give the weak topology of the actual realization. -/
theorem orderNerveCharacteristicMap_isClosed  [PartialOrder P]
    (A : Set (orderNerveRealization P))
    (h : ∀ n (s : (nerve P).nonDegenerate n),
      IsClosed (A ∩ orderNerveCharacteristicMap s '' Metric.closedBall 0 1)) : IsClosed A := by
  apply (orderNerveRealization_isClosed_iff_inter_simplex_range P A).mpr
  intro n s
  simpa only [orderNerveCharacteristicMap_closedCell] using h n s

variable {P : Type}
/-- Characteristic sphere boundaries lie in finitely many codimension-one closed cells. -/
theorem orderNerveCharacteristicMap_boundary  [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate (n + 1)) :
    ∃ I : Finset ((nerve P).nonDegenerate n),
      ∀ x ∈ Metric.sphere (0 : Fin (n + 1) → ℝ) 1,
        ∃ t ∈ I, orderNerveCharacteristicMap s x ∈
          orderNerveCharacteristicMap t '' Metric.closedBall 0 1 := by
  obtain ⟨I, hI⟩ := orderNerveRealizationSimplex_boundary_finite_faces s
  refine ⟨I, ?_⟩
  intro x hx
  have hxc : x ∈ Metric.closedBall 0 1 := Metric.sphere_subset_closedBall hx
  let u : (Metric.closedBall 0 1 : Set (Fin (n + 1) → ℝ)) := ⟨x, hxc⟩
  let z := (orderNerveSimplexClosedBallHomeomorph (n + 1)).symm u
  have hz : ¬ ∀ i, 0 < z.weights i := by
    intro hp
    have hb := (orderNerveSimplexClosedBallHomeomorph_positive_iff (n + 1) z).mp hp
    
    rw [Homeomorph.apply_symm_apply] at hb
    have he := Metric.mem_sphere.mp hx
    have hl := Metric.mem_ball.mp hb
    
    rw [he] at hl
    exact (lt_irrefl _ hl)
  obtain ⟨t, ht, w, hw⟩ := hI (ULift.up z) hz
  refine ⟨t, ht, ?_⟩
  rw [orderNerveCharacteristicMap_closedCell]
  refine ⟨w, ?_⟩
  exact hw.trans (orderNerveCharacteristicFunction_closedBall s u).symm

end FiniteChains.Comb
