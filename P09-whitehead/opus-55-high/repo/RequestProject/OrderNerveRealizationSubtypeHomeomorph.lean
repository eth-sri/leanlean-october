import RequestProject.OrderNerveRealizationMapCoordinates
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- A lifted simplex realizes to the original simplex under subtype inclusion. -/
theorem orderNerveRealizationSimplex_subtype {P} [PartialOrder P] (A : Set P)
    {n} (s : (nerve P).obj (Opposite.op n))
    (hs : ∀ i, s.obj i ∈ A) (z : SimplexCategory.toTop.obj n) :
    orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h)
      (orderNerveRealizationSimplex A (orderNerveSimplexSubtype A s hs) z) =
      orderNerveRealizationSimplex P s z := by
  have ht : (nerveMap (show Monotone Subtype.val from
      by tauto).functor).app _ (orderNerveSimplexSubtype A s hs) = s := by
    rfl
  have he := congrArg (· z)
    (orderNerveRealizationSimplex_natural (Subtype.val : A → P)
      (by grind) (orderNerveSimplexSubtype A s hs))
  simp_all

/-- Induced-subposet realization inclusions are closed maps in the actual CW topology. -/
theorem orderNerveRealizationSubtype_isClosedMap {P} [PartialOrder P] (A : Set P) :
    IsClosedMap (orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h)) := by
  intro B hB
  let f := orderNerveRealizationMap (Subtype.val : A → P) (by tauto)
  apply (CWComplex.closed (orderNerveRealizationSubcomplex P A)
    (f '' B) ?_).mpr
  · intro n j
    change IsClosed (f '' B ∩ orderNerveCharacteristicMap j.val '' Metric.closedBall 0 1)
    rwd [orderNerveCharacteristicMap_closedCell]
    haveI : CompactSpace (SimplexCategory.toTop.obj (SimplexCategory.mk n)) :=
      inferInstanceAs (CompactSpace (ULift.{0} (Convexity.StdSimplex ℝ (Fin (n + 1)))))
    let t := orderNerveSimplexSubtype A j.val.val j.property
    have he : f '' B ∩ Set.range (orderNerveRealizationSimplex P j.val.val) =
        orderNerveRealizationSimplex P j.val.val ''
          (orderNerveRealizationSimplex A t ⁻¹' B) := by
      ext x
      constructor
      · rintro ⟨⟨y, hy, hxy⟩, ⟨z, hzx⟩⟩
        refine ⟨z, ?_, hzx⟩
        have hz : f (orderNerveRealizationSimplex A t z) = f y := by
          grind [orderNerveRealizationSimplex_subtype]
        grind [orderNerveRealizationMap_injective _
          _ Subtype.val_injective hz]
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨orderNerveRealizationSimplex A t z, hz,
          orderNerveRealizationSimplex_subtype A j.val.val j.property z⟩, ⟨z, rfl⟩⟩
    rwd [he]
    exact ((hB.preimage (orderNerveRealizationSimplex A t).hom.continuous).isCompact.image
      (orderNerveRealizationSimplex P j.val.val).hom.continuous).isClosed
  · rintro x ⟨y, _, rfl⟩
    have h := orderNerveRealizationMap_mem_subcomplex (Subtype.val : A → P)
      (by tauto) y
    aesop

/-- The actual realization inclusion of an induced subposet is a closed embedding. -/
theorem orderNerveRealizationSubtype_isClosedEmbedding {P} [PartialOrder P]
    (A : Set P) :
    IsClosedEmbedding (orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h)) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (orderNerveRealizationMap _ (by tauto)).hom.continuous
    (orderNerveRealizationMap_injective _
      _ Subtype.val_injective)
    (orderNerveRealizationSubtype_isClosedMap A)

/-- The induced-subposet realization is homeomorphic to the genuine supported CW carrier. -/
noncomputable def orderNerveRealizationSubtypeHomeomorph {P} [PartialOrder P]
    (A : Set P) : orderNerveRealization A ≃ₜ
      (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) :=
  (orderNerveRealizationSubtype_isClosedEmbedding A).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (orderNerveRealizationSubtype_range A))

/-- The carrier homeomorphism is the actual realized inclusion on points. -/
theorem orderNerveRealizationSubtypeHomeomorph_coe {P} [PartialOrder P]
    (A : Set P) (x : orderNerveRealization A) :
    (orderNerveRealizationSubtypeHomeomorph A x).val =
      orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h) x := by
  rfl
