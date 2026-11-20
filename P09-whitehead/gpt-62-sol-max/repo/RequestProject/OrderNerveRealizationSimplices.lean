module

public import RequestProject.OrderNerveRealizationComparison

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open CategoryTheory

/-- The canonical continuous simplex in the actual geometric realization, obtained
by realizing the Yoneda map of a nerve simplex. -/
noncomputable def orderNerveRealizationSimplex (P : Type) [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) :
    SimplexCategory.toTop.obj n ⟶ orderNerveRealization P :=
  SSet.toTopSimplex.inv.app n ≫ SSet.toTop.map (SSet.yonedaEquiv.symm s)

private theorem realizationSimplex_comp_hom (P : Type) [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) :
    SSet.toTopSimplex.hom.app n ≫ orderNerveRealizationSimplex P s =
      SSet.toTop.map (SSet.yonedaEquiv.symm s) := by
  simp only [orderNerveRealizationSimplex, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- Realized simplex maps commute with actual monotone maps of posets. -/
theorem orderNerveRealizationSimplex_natural {P Q : Type} [PartialOrder P]
    [PartialOrder Q] (f : P → Q) (hf : Monotone f) {n : SimplexCategory}
    (s : (nerve P).obj (Opposite.op n)) (z : SimplexCategory.toTop.obj n) :
    orderNerveRealizationMap f hf (orderNerveRealizationSimplex P s z) =
      orderNerveRealizationSimplex Q ((nerveMap hf.functor).app _ s) z := by
  suffices h : orderNerveRealizationSimplex P s ≫ orderNerveRealizationMap f hf =
      orderNerveRealizationSimplex Q ((nerveMap hf.functor).app _ s) by
    exact congrArg (fun k => k z) h
  unfold orderNerveRealizationSimplex orderNerveRealizationMap
  rw [Category.assoc, ← Functor.map_comp]
  congr 2

/-- Canonical realized simplices respect every simplex operator, including faces
and degeneracies. This is the attaching-map compatibility for the realization. -/
theorem orderNerveRealizationSimplex_operator (P : Type) [PartialOrder P]
    {m n : SimplexCategory} (a : m ⟶ n) (s : (nerve P).obj (Opposite.op n))
    (z : SimplexCategory.toTop.obj m) :
    orderNerveRealizationSimplex P s (SimplexCategory.toTop.map a z) =
      orderNerveRealizationSimplex P ((nerve P).map a.op s) z := by
  suffices h : SimplexCategory.toTop.map a ≫ orderNerveRealizationSimplex P s =
      orderNerveRealizationSimplex P ((nerve P).map a.op s) by
    exact congrArg (fun k => k z) h
  unfold orderNerveRealizationSimplex
  rw [← Category.assoc, SSet.toTopSimplex.inv.naturality a, Category.assoc,
    Functor.comp_map, ← Functor.map_comp]
  congr 2

/-- Every point of the actual realization lies in a canonical realized simplex. -/
theorem orderNerveRealizationSimplex_jointly_surjective (P : Type) [PartialOrder P]
    (x : orderNerveRealization P) :
    ∃ (n : SimplexCategory) (s : (nerve P).obj (Opposite.op n))
      (z : SimplexCategory.toTop.obj n), orderNerveRealizationSimplex P s z = x := by
  letI := sSetTopAdj.leftAdjoint_preservesColimits
  have hc := CategoryTheory.Limits.isColimitOfPreserves SSet.toTop
    (CategoryTheory.Presheaf.colimitOfRepresentable (nerve P))
  have ht := CategoryTheory.Limits.isColimitOfPreserves (CategoryTheory.forget TopCat) hc
  obtain ⟨j, y, hy⟩ := CategoryTheory.Limits.Types.jointly_surjective_of_isColimit ht x
  refine ⟨j.unop.1.unop, j.unop.2, SSet.toTopSimplex.hom.app _ y, ?_⟩
  change (SSet.toTopSimplex.hom.app _ ≫ orderNerveRealizationSimplex P j.unop.2) y = x
  rwa [realizationSimplex_comp_hom]

/-- Continuity on the actual realization is detected by its canonical continuous simplices. -/
theorem orderNerveRealization_continuous_iff (P : Type) [PartialOrder P]
    {X : Type*} [TopologicalSpace X] (f : orderNerveRealization P → X) :
    Continuous f ↔ ∀ (n : SimplexCategory) (s : (nerve P).obj (Opposite.op n)),
      Continuous (f ∘ orderNerveRealizationSimplex P s) := by
  constructor
  · intro h n s
    exact h.comp (orderNerveRealizationSimplex P s).hom.continuous
  · intro h
    letI := sSetTopAdj.leftAdjoint_preservesColimits
    have hc := CategoryTheory.Limits.isColimitOfPreserves SSet.toTop
      (CategoryTheory.Presheaf.colimitOfRepresentable (nerve P))
    apply (TopCat.continuous_iff_of_isColimit _ hc f).mpr
    intro j
    change Continuous (f ∘ SSet.toTop.map (SSet.yonedaEquiv.symm j.unop.2))
    rw [← realizationSimplex_comp_hom, TopCat.coe_comp, ← Function.comp_assoc]
    exact (h _ _).comp (SSet.toTopSimplex.hom.app j.unop.1.unop).hom.continuous

/-- The actual realization has the weak topology defined by its canonical simplices. -/
theorem orderNerveRealization_isOpen_iff (P : Type) [PartialOrder P]
    (U : Set (orderNerveRealization P)) :
    IsOpen U ↔ ∀ (n : SimplexCategory) (s : (nerve P).obj (Opposite.op n)),
      IsOpen (orderNerveRealizationSimplex P s ⁻¹' U) := by
  constructor
  · intro h n s
    exact h.preimage (orderNerveRealizationSimplex P s).hom.continuous
  · intro h
    letI := sSetTopAdj.leftAdjoint_preservesColimits
    have hc := CategoryTheory.Limits.isColimitOfPreserves SSet.toTop
      (CategoryTheory.Presheaf.colimitOfRepresentable (nerve P))
    apply (TopCat.isOpen_iff_of_isColimit _ hc U).mpr
    intro j
    change IsOpen (SSet.toTop.map (SSet.yonedaEquiv.symm j.unop.2) ⁻¹' U)
    rw [← realizationSimplex_comp_hom, TopCat.coe_comp, Set.preimage_comp]
    exact (h _ _).preimage (SSet.toTopSimplex.hom.app j.unop.1.unop).hom.continuous

/-- Closedness on the actual realization is detected simplex by simplex. -/
theorem orderNerveRealization_isClosed_iff (P : Type) [PartialOrder P]
    (U : Set (orderNerveRealization P)) :
    IsClosed U ↔ ∀ (n : SimplexCategory) (s : (nerve P).obj (Opposite.op n)),
      IsClosed (orderNerveRealizationSimplex P s ⁻¹' U) := by
  simpa only [← isOpen_compl_iff, Set.preimage_compl] using
    orderNerveRealization_isOpen_iff P Uᶜ

end FiniteChains.Comb
