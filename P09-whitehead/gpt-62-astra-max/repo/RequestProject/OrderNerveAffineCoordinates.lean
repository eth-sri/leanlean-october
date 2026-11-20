module

public import RequestProject.OrderNerveRealizationSimplices

@[expose] public section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace FiniteChains.Comb
open CategoryTheory
open scoped Classical

variable {P : Type} [PartialOrder P]

variable (v : P → ℝ)

/-- Affine interpolation of vertex values on a genuine topological nerve simplex. -/
def orderNerveAffineSimplex
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) :
    C(SimplexCategory.toTop.obj n, ℝ) where
  toFun z := ∑ i, z.down.weights i * v (s.obj i)
  continuous_toFun := by
    fun_prop

/-- Affine interpolation respects every actual topological simplex operator. -/
theorem orderNerveAffineSimplex_operator
    {m n : SimplexCategory} (a : m ⟶ n) (s : (nerve P).obj _)
    (z : SimplexCategory.toTop.obj m) :
    orderNerveAffineSimplex v s (SimplexCategory.toTop.map a z) =
      orderNerveAffineSimplex v ((nerve P).map a.op s) z := by
  classical
  change (∑ j, (Finsupp.mapDomain a.toOrderHom z.down.weights) j * v _) =
    ∑ i, z.down.weights i * v (s.obj (a.toOrderHom i))
  have hw : (fun j => (Finsupp.mapDomain a.toOrderHom z.down.weights) j) =
      FunOnFinite.linearMap ℝ ℝ a.toOrderHom z.down.weights := by
    funext j
    simp [FunOnFinite.linearMap_apply_apply, Finsupp.mapDomain_apply, Finsupp.sum_fintype,
      Finsupp.single_apply, Finset.sum_filter, eq_comm]
  change (∑ j, (fun j => (Finsupp.mapDomain a.toOrderHom z.down.weights) j) j * v _) = _
  rw [hw]
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_mul]
  have h := Finset.sum_fiberwise Finset.univ a.toOrderHom
    (fun i => z.down.weights i * v (s.obj (a.toOrderHom i)))
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  simp_all

/-- The compatible affine functions form an actual cocone on the realized
representable-simplex diagram. -/
def orderNerveAffineCocone :
    CategoryTheory.Limits.Cocone (Presheaf.functorToRepresentables (nerve P) ⋙ SSet.toTop) where
  pt := TopCat.of ℝ
  ι :=
    { app := fun j => SSet.toTopSimplex.hom.app _ ≫
        TopCat.ofHom (orderNerveAffineSimplex v j.unop.2)
      naturality := by
        intro j k a
        ext z
        have hn := congrArg (fun f => f z)
          (SSet.toTopSimplex.hom.naturality a.unop.1.unop)
        change SSet.toTopSimplex.hom.app _
            (SSet.toTop.map (SSet.stdSimplex.map a.unop.1.unop) z) =
          SimplexCategory.toTop.map _
            _ at hn
        change orderNerveAffineSimplex v k.unop.2
            (SSet.toTopSimplex.hom.app k.unop.1.unop
              (SSet.toTop.map (SSet.stdSimplex.map a.unop.1.unop) z)) =
          orderNerveAffineSimplex v j.unop.2 _
        rw [hn, orderNerveAffineSimplex_operator]
        congr 1
        exact congrArg _ a.unop.2 }

/-- Continuous affine interpolation of arbitrary vertex values on the actual realization. -/
def orderNerveAffineRealization :
    orderNerveRealization P ⟶ TopCat.of ℝ := (CategoryTheory.Limits.isColimitOfPreserves SSet.toTop
    (Presheaf.colimitOfRepresentable _)).desc (orderNerveAffineCocone v)

/-- The global affine function has the prescribed formula on each canonical simplex. -/
theorem orderNerveAffineRealization_simplex
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) :
    orderNerveRealizationSimplex P s ≫ orderNerveAffineRealization v =
      TopCat.ofHom (orderNerveAffineSimplex v s) := by
  have h := (CategoryTheory.Limits.isColimitOfPreserves SSet.toTop
    (Presheaf.colimitOfRepresentable _)).fac (orderNerveAffineCocone v)
      (Opposite.op (Functor.elementsMk (nerve P) (Opposite.op n) s)); change SSet.toTop.map (SSet.yonedaEquiv.symm s) ≫ orderNerveAffineRealization v =
    SSet.toTopSimplex.hom.app n ≫ TopCat.ofHom _ at h; unfold orderNerveRealizationSimplex; rw [Category.assoc, h, ← Category.assoc,
    SSet.toTopSimplex.inv_hom_id_app, Category.id_comp]

variable {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) (hs : Function.Injective s.obj)
include n hs

/-- A vertex indicator recovers each barycentric coordinate of a nondegenerate simplex. -/
theorem orderNerveAffineSimplex_indicator (i : Fin _)
    (z : SimplexCategory.toTop.obj n) :
    orderNerveAffineSimplex (fun p => if p = s.obj i then 1 else 0) s z = z.down.weights i := by
  simp [orderNerveAffineSimplex, hs.eq_iff]

/-- Every simplex with distinct vertices is injectively realized, including its boundary. -/
theorem orderNerveRealizationSimplex_injective : Function.Injective (orderNerveRealizationSimplex P s) := by
  classical
  intro z w h
  apply ULift.ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  let v : P → ℝ := fun p => if p = s.obj i then 1 else 0
  have hc := congrArg (fun k => k z) (orderNerveAffineRealization_simplex v s)
  have hd := congrArg (fun k => k w) (orderNerveAffineRealization_simplex v s)
  change orderNerveAffineRealization v (orderNerveRealizationSimplex P s z) =
    orderNerveAffineSimplex v s z at hc
  change orderNerveAffineRealization v (orderNerveRealizationSimplex P s w) =
    orderNerveAffineSimplex v s w at hd
  grind [orderNerveAffineSimplex_indicator]

end FiniteChains.Comb
