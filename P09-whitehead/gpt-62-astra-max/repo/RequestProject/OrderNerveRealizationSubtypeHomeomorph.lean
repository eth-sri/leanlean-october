module

public import RequestProject.OrderNerveRealizationMapCoordinates

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

variable {P : Type} [PartialOrder P] (A : Set P)

/-- A lifted simplex realizes to the original simplex under subtype inclusion. -/
theorem orderNerveRealizationSimplex_subtype
    {n : SimplexCategory} (s : (nerve P).obj _)
    (hs : ∀ i, s.obj i ∈ A) (z : SimplexCategory.toTop.obj n) :
    orderNerveRealizationMap Subtype.val (fun _ _ h => h)
      (orderNerveRealizationSimplex A (orderNerveSimplexSubtype A s hs) z) =
      orderNerveRealizationSimplex P s z := by
  have he := congrArg (fun k => k z)
    (orderNerveRealizationSimplex_natural Subtype.val
      (fun _ _ h => h) (orderNerveSimplexSubtype A s hs))
  assumption

/-- Induced-subposet realization inclusions are closed maps in the actual CW topology. -/
theorem orderNerveRealizationSubtype_isClosedMap :
    IsClosedMap (orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h)) := by
  intro B hB
  let f := orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h)
  apply (CWComplex.closed (orderNerveRealizationSubcomplex P A)
    (f '' B) ?_).mpr
  · intro n j
    change IsClosed (f '' B ∩ orderNerveCharacteristicMap j.val '' Metric.closedBall 0 1)
    erw [orderNerveCharacteristicMap_closedCell]
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
          rw [orderNerveRealizationSimplex_subtype]
          exact hzx.trans hxy.symm
        change orderNerveRealizationSimplex A t z ∈ B
        erw [orderNerveRealizationMap_injective Subtype.val
          _ Subtype.val_injective hz] <;> assumption
      · grind [orderNerveRealizationSimplex_subtype]
    erw [he]
    exact ((hB.preimage (orderNerveRealizationSimplex A t).hom.continuous).isCompact.image
      (orderNerveRealizationSimplex P j.val.val).hom.continuous).isClosed
  · rintro x ⟨y, _, rfl⟩
    have h := orderNerveRealizationMap_mem_subcomplex Subtype.val
      (fun _ _ h => h) y
    aesop

/-- The actual realization inclusion of an induced subposet is a closed embedding. -/
theorem orderNerveRealizationSubtype_isClosedEmbedding :
    IsClosedEmbedding (orderNerveRealizationMap (Subtype.val : A → P) (fun _ _ h => h)) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (orderNerveRealizationMap Subtype.val (fun _ _ h => h)).hom.continuous
    (orderNerveRealizationMap_injective Subtype.val
      (fun _ _ h => h) Subtype.val_injective)
    (orderNerveRealizationSubtype_isClosedMap A)

/-- The induced-subposet realization is homeomorphic to the genuine supported CW carrier. -/
noncomputable def orderNerveRealizationSubtypeHomeomorph :=
  (orderNerveRealizationSubtype_isClosedEmbedding A).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (orderNerveRealizationSubtype_range A))

/-- The carrier homeomorphism is the actual realized inclusion on points. -/
theorem orderNerveRealizationSubtypeHomeomorph_coe (x : orderNerveRealization A) :
    (orderNerveRealizationSubtypeHomeomorph A x).val =
      orderNerveRealizationMap Subtype.val (fun _ _ h => h) x := rfl

end FiniteChains.Comb
