import RequestProject.OrderNerveCharacteristicMap
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- Closed characteristic cells are precisely the canonical simplex images. -/
theorem orderNerveCharacteristicMap_closedCell {P} [PartialOrder P]
    {n} (s : (nerve P).nonDegenerate n) :
    orderNerveCharacteristicMap s '' Metric.closedBall 0 1 =
      Set.range (orderNerveRealizationSimplex P s.val) := by
  rw [← orderNerveClosedBallChart_range s]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, (orderNerveCharacteristicFunction_closedBall s _).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u.val, u.property, orderNerveCharacteristicFunction_closedBall s u⟩

/-- The open characteristic cell consists exactly of the positive-coordinate simplex points. -/
theorem orderNerveCharacteristicMap_openCell {P} [PartialOrder P]
    {n} s :
    orderNerveCharacteristicMap s '' Metric.ball 0 1 =
      {x | ∃ z : SimplexCategory.toTop.obj ⦋n⦌,
        (∀ i, 0 < z.down.weights i) ∧ orderNerveRealizationSimplex P s.val z = x} := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hc := Metric.ball_subset_closedBall hu
    let v : (Metric.closedBall 0 1 : Set (Fin n → ℝ)) := by tauto
    let z := (orderNerveSimplexClosedBallHomeomorph n).symm v
    refine ⟨ULift.up z, ?_, ?_⟩
    · apply (orderNerveSimplexClosedBallHomeomorph_positive_iff n z).mpr
      aesop
    · exact (orderNerveCharacteristicFunction_closedBall s v).symm
  · rintro ⟨z, hz, rfl⟩
    let u := orderNerveSimplexClosedBallHomeomorph n z.down
    have hu :=
      (orderNerveSimplexClosedBallHomeomorph_positive_iff n z.down).mp hz
    refine ⟨u.val, hu, ?_⟩
    rw [show orderNerveCharacteristicMap s u.val = orderNerveClosedBallChart s u from
      orderNerveCharacteristicFunction_closedBall s u]
    change orderNerveRealizationSimplex P s.val
      (ULift.up ((orderNerveSimplexClosedBallHomeomorph n).symm
        (orderNerveSimplexClosedBallHomeomorph n z.down))) = _
    aesop

/-- The actual characteristic open cells are pairwise disjoint in all dimensions. -/
theorem orderNerveCharacteristicMap_pairwiseDisjoint P [PartialOrder P] :
    (Set.univ : Set (Σ n, (nerve P).nonDegenerate n)).PairwiseDisjoint
      (orderNerveCharacteristicMap ·.2 '' Metric.ball 0 1) := by
  intro a _ b _ hab
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  cases' a with n s
  cases' b with m t
  dsimp at hxa hxb
  rw [orderNerveCharacteristicMap_openCell] at hxa hxb
  obtain ⟨z, hz, hx⟩ := hxa
  obtain ⟨w, hw, hy⟩ := hxb
  have he := hx.trans hy.symm
  have hnm := orderNerveRealization_nonDegenerate_interior_dimension_eq s t z w hz hw he
  subst m
  have hst := orderNerveRealization_nonDegenerate_interior_eq s t z w hz hw he
  simp_all

/-- The actual closed characteristic cells cover the entire realization. -/
theorem orderNerveCharacteristicMap_union P [PartialOrder P] :
    (⋃ (n) (s : (nerve P).nonDegenerate n),
      orderNerveCharacteristicMap s '' Metric.closedBall 0 1) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n, s, z, hz⟩ := orderNerveRealization_nonDegenerate_jointly_surjective P x
  apply Set.mem_iUnion.mpr
  refine ⟨n, Set.mem_iUnion.mpr ⟨s, ?_⟩⟩
  rw [orderNerveCharacteristicMap_closedCell]
  tauto

/-- The characteristic closed cells give the weak topology of the actual realization. -/
theorem orderNerveCharacteristicMap_isClosed P [PartialOrder P]
    A
    (h : ∀ n (s : (nerve P).nonDegenerate n),
      IsClosed (A ∩ orderNerveCharacteristicMap s '' Metric.closedBall 0 1)) : IsClosed A := by
  apply (orderNerveRealization_isClosed_iff_inter_simplex_range P A).mpr
  simp_all [orderNerveCharacteristicMap_closedCell]

/-- Characteristic sphere boundaries lie in finitely many codimension-one closed cells. -/
theorem orderNerveCharacteristicMap_boundary {P} [PartialOrder P]
    {n} s :
    ∃ I : Finset ((nerve P).nonDegenerate n),
      ∀ x ∈ Metric.sphere (0 : Fin (n + 1) → ℝ) 1,
        ∃ t ∈ I, orderNerveCharacteristicMap s x ∈
          orderNerveCharacteristicMap t '' Metric.closedBall 0 1 := by
  cases' orderNerveRealizationSimplex_boundary_finite_faces s with I hI
  refine ⟨I, ?_⟩
  intro x hx
  have hxc := Metric.sphere_subset_closedBall hx
  let u : (Metric.closedBall 0 1 : Set (Fin (n + 1) → ℝ)) := by tauto
  let z := (orderNerveSimplexClosedBallHomeomorph _).symm u
  have hz : ¬ ∀ i, 0 < z.weights i := by
    intro hp
    have hb := (orderNerveSimplexClosedBallHomeomorph_positive_iff _ z).mp hp
    aesop
  obtain ⟨t, ht, w, hw⟩ := hI _ hz
  refine ⟨t, ht, ?_⟩
  rw [orderNerveCharacteristicMap_closedCell]
  refine ⟨w, ?_⟩
  exact hw.trans (orderNerveCharacteristicFunction_closedBall s u).symm
