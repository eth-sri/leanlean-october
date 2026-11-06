import RequestProject.OrderNerveRealizationComparison
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory

/-- The canonical continuous simplex in the actual geometric realization, obtained
by realizing the Yoneda map of a nerve simplex. -/
noncomputable def orderNerveRealizationSimplex P [PartialOrder P]
    {n} (s : (nerve P).obj (Opposite.op n)) :
    SimplexCategory.toTop.obj n ⟶ orderNerveRealization P :=
  SSet.toTopSimplex.inv.app n ≫ SSet.toTop.map (SSet.yonedaEquiv.symm s)

/-- Realized simplex maps commute with actual monotone maps of posets. -/
theorem orderNerveRealizationSimplex_natural {P Q} [PartialOrder P]
    [PartialOrder Q] f hf {n}
    (s : (nerve P).obj (Opposite.op n)) :
    orderNerveRealizationSimplex P s ≫ orderNerveRealizationMap f hf =
      orderNerveRealizationSimplex Q ((nerveMap hf.functor).app _ s) := by
  unfold orderNerveRealizationSimplex orderNerveRealizationMap
  rw [Category.assoc, ← Functor.map_comp]
  congr 2

/-- Canonical realized simplices respect every simplex operator, including faces
and degeneracies. This is the attaching-map compatibility for the realization. -/
theorem orderNerveRealizationSimplex_operator P [PartialOrder P]
    {m n : SimplexCategory} (a : m ⟶ n) s :
    SimplexCategory.toTop.map a ≫ orderNerveRealizationSimplex P s =
      orderNerveRealizationSimplex P ((nerve P).map a.op s) := by
  unfold orderNerveRealizationSimplex
  rw [← Category.assoc, SSet.toTopSimplex.inv.naturality a, Category.assoc,
    Functor.comp_map, ← Functor.map_comp]
  congr 2

/-- Every point of the actual realization lies in a canonical realized simplex. -/
theorem orderNerveRealizationSimplex_jointly_surjective P [PartialOrder P]
    x :
    ∃ (n : SimplexCategory) (s : (nerve P).obj (Opposite.op n))
      (z : SimplexCategory.toTop.obj n), orderNerveRealizationSimplex P s z = x := by
  have hc := CategoryTheory.Limits.isColimitOfPreserves SSet.toTop
    (CategoryTheory.Presheaf.colimitOfRepresentable (nerve P))
  have ht := CategoryTheory.Limits.isColimitOfPreserves (CategoryTheory.forget TopCat) hc
  obtain ⟨j, y, hy⟩ := CategoryTheory.Limits.Types.jointly_surjective_of_isColimit ht x
  refine ⟨j.unop.1.unop, j.unop.2, SSet.toTopSimplex.hom.app _ y, ?_⟩
  change SSet.toTop.map (SSet.yonedaEquiv.symm j.unop.2)
      (SSet.toTopSimplex.inv.app _ (SSet.toTopSimplex.hom.app _ y)) = x
  have hi := congrArg (· y) (SSet.toTopSimplex.hom_inv_id_app j.unop.1.unop)
  change SSet.toTopSimplex.inv.app j.unop.1.unop
    (SSet.toTopSimplex.hom.app j.unop.1.unop y) = y at hi
  aesop

/-- Continuity on the actual realization is detected by its canonical continuous simplices. -/
theorem orderNerveRealization_continuous_iff P [PartialOrder P]
    {X} [TopologicalSpace X] (f : orderNerveRealization P → X) :
    Continuous f ↔ ∀ n (s : (nerve P).obj (Opposite.op n)),
      Continuous (f ∘ orderNerveRealizationSimplex P s) := by
  constructor
  · fun_prop
  · intro h
    have hc := CategoryTheory.Limits.isColimitOfPreserves SSet.toTop
      (CategoryTheory.Presheaf.colimitOfRepresentable (nerve P))
    apply (TopCat.continuous_iff_of_isColimit _ hc f).mpr
    intro j
    have hj := (h j.unop.1.unop j.unop.2).comp
      (SSet.toTopSimplex.hom.app j.unop.1.unop).hom.continuous
    convert hj using 1
    all_goals try rfl
    funext y
    change f (SSet.toTop.map (SSet.yonedaEquiv.symm j.unop.2) y) =
      f (SSet.toTop.map (SSet.yonedaEquiv.symm j.unop.2)
        (SSet.toTopSimplex.inv.app j.unop.1.unop
          (SSet.toTopSimplex.hom.app j.unop.1.unop y)))
    norm_num

/-- The actual realization has the weak topology defined by its canonical simplices. -/
theorem orderNerveRealization_isOpen_iff P [PartialOrder P]
    U :
    IsOpen U ↔ ∀ n (s : (nerve P).obj (Opposite.op n)),
      IsOpen (orderNerveRealizationSimplex P s ⁻¹' U) := by
  constructor
  · intro h n s
    exact h.preimage (orderNerveRealizationSimplex P s).hom.continuous
  · intro h
    have hc := CategoryTheory.Limits.isColimitOfPreserves SSet.toTop
      (CategoryTheory.Presheaf.colimitOfRepresentable (nerve P))
    apply (TopCat.isOpen_iff_of_isColimit _ hc U).mpr
    intro j
    have hj := (h j.unop.1.unop j.unop.2).preimage
      (SSet.toTopSimplex.hom.app j.unop.1.unop).hom.continuous
    convert hj using 1
    all_goals try rfl
    ext y
    change SSet.toTop.map (SSet.yonedaEquiv.symm j.unop.2) y ∈ U ↔
      SSet.toTop.map (SSet.yonedaEquiv.symm j.unop.2)
        (SSet.toTopSimplex.inv.app j.unop.1.unop
          (SSet.toTopSimplex.hom.app j.unop.1.unop y)) ∈ U
    norm_num

/-- Closedness on the actual realization is detected simplex by simplex. -/
theorem orderNerveRealization_isClosed_iff P [PartialOrder P]
    U :
    IsClosed U ↔ ∀ n (s : (nerve P).obj (Opposite.op n)),
      IsClosed (orderNerveRealizationSimplex P s ⁻¹' U) := by
  simpa [← isOpen_compl_iff, Set.preimage_compl] using
    orderNerveRealization_isOpen_iff P Uᶜ
