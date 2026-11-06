import RequestProject.OrderNerveRealizationSimplices
noncomputable section


set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open CategoryTheory
open scoped Classical

/-- Affine interpolation of vertex values on a genuine topological nerve simplex. -/
def orderNerveAffineSimplex {P : Type} [PartialOrder P] (v : P → ℝ)
    {n} (s : (nerve P).obj (Opposite.op n)) :
    C(SimplexCategory.toTop.obj n, ℝ) where
  toFun z := ∑ i, z.down.weights i * v (s.obj i)
  continuous_toFun := by
    fun_prop

/-- Affine interpolation respects every actual topological simplex operator. -/
theorem orderNerveAffineSimplex_operator {P} [PartialOrder P] v
    {m n : SimplexCategory} (a : m ⟶ n) s
    z :
    orderNerveAffineSimplex v s (SimplexCategory.toTop.map a z) =
      orderNerveAffineSimplex v ((nerve P).map a.op s) z := by
  classical
  change (∑ j, (Finsupp.mapDomain a.toOrderHom z.down.weights) j * v (s.obj j)) =
    ∑ i, z.down.weights i * v (s.obj (a.toOrderHom i))
  have hw : (Finsupp.mapDomain a.toOrderHom z.down.weights) =
      FunOnFinite.linearMap ℝ ℝ a.toOrderHom z.down.weights := by
    funext j
    simp [FunOnFinite.linearMap_apply_apply, Finsupp.mapDomain_apply, Finsupp.sum_fintype,
      Finsupp.single_apply, Finset.sum_filter, eq_comm]
  change (∑ j, (Finsupp.mapDomain a.toOrderHom z.down.weights) j * v (s.obj j)) = _
  rw [hw]
  simp [FunOnFinite.linearMap_apply_apply, Finset.sum_mul]
  have h := Finset.sum_fiberwise Finset.univ a.toOrderHom
    (fun i => z.down.weights i * v (s.obj (a.toOrderHom i)))
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  simp_all

/-- The compatible affine functions form an actual cocone on the realized
representable-simplex diagram. -/
def orderNerveAffineCocone {P : Type} [PartialOrder P] (v : P → ℝ) :
    CategoryTheory.Limits.Cocone (Presheaf.functorToRepresentables (nerve P) ⋙ SSet.toTop) where
  pt := TopCat.of ℝ
  ι :=
    { app := fun j => SSet.toTopSimplex.hom.app j.unop.1.unop ≫
        TopCat.ofHom (orderNerveAffineSimplex v j.unop.2)
      naturality := by
        intro j k a
        apply TopCat.hom_ext
        ext z
        have hn := congrArg (· z)
          (SSet.toTopSimplex.hom.naturality a.unop.1.unop)
        change SSet.toTopSimplex.hom.app k.unop.1.unop
            (SSet.toTop.map (SSet.stdSimplex.map a.unop.1.unop) z) =
          SimplexCategory.toTop.map a.unop.1.unop
            (SSet.toTopSimplex.hom.app j.unop.1.unop z) at hn
        change orderNerveAffineSimplex v k.unop.2
            (SSet.toTopSimplex.hom.app k.unop.1.unop
              (SSet.toTop.map (SSet.stdSimplex.map a.unop.1.unop) z)) =
          orderNerveAffineSimplex v j.unop.2 (SSet.toTopSimplex.hom.app j.unop.1.unop z)
        rw [hn, orderNerveAffineSimplex_operator]
        congr 1
        exact congrArg (orderNerveAffineSimplex v) a.unop.2 }

/-- Continuous affine interpolation of arbitrary vertex values on the actual realization. -/
def orderNerveAffineRealization {P} [PartialOrder P] (v : P → ℝ) :
    orderNerveRealization P ⟶ TopCat.of ℝ := (CategoryTheory.Limits.isColimitOfPreserves SSet.toTop
    (Presheaf.colimitOfRepresentable _)).desc (orderNerveAffineCocone v)

/-- The global affine function has the prescribed formula on each canonical simplex. -/
theorem orderNerveAffineRealization_simplex {P} [PartialOrder P] v
    {n} (s : (nerve P).obj (Opposite.op n)) :
    orderNerveRealizationSimplex P s ≫ orderNerveAffineRealization v =
      TopCat.ofHom (orderNerveAffineSimplex v s) := by
  have h := (CategoryTheory.Limits.isColimitOfPreserves SSet.toTop
    (Presheaf.colimitOfRepresentable _)).fac (orderNerveAffineCocone v)
      (Opposite.op (Functor.elementsMk (nerve P) (Opposite.op n) s))
  change SSet.toTop.map (SSet.yonedaEquiv.symm s) ≫ orderNerveAffineRealization v =
    SSet.toTopSimplex.hom.app n ≫ TopCat.ofHom (orderNerveAffineSimplex v s) at h
  unfold orderNerveRealizationSimplex
  simp_all

/-- A vertex indicator recovers each barycentric coordinate of a nondegenerate simplex. -/
theorem orderNerveAffineSimplex_indicator {P} [PartialOrder P]
    {n} (s : (nerve P).obj (Opposite.op n))
    (hs : Function.Injective s.obj) (i : Fin (n.len + 1))
    z :
    orderNerveAffineSimplex (if · = s.obj i then 1 else 0) s z = z.down.weights i := by
  classical
  simp [orderNerveAffineSimplex, hs.eq_iff]

/-- Every simplex with distinct vertices is injectively realized, including its boundary. -/
theorem orderNerveRealizationSimplex_injective {P} [PartialOrder P]
    {n} (s : (nerve P).obj (Opposite.op n))
    (hs : Function.Injective s.obj) : Function.Injective (orderNerveRealizationSimplex P s) := by
  classical
  intro z w h
  apply ULift.ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  let v : P → ℝ := fun p => if p = s.obj i then 1 else 0
  have hf := congrArg (orderNerveAffineRealization v) h
  have hc := congrArg (· z) (orderNerveAffineRealization_simplex v s)
  have hd := congrArg (· w) (orderNerveAffineRealization_simplex v s)
  change orderNerveAffineRealization v (orderNerveRealizationSimplex P s z) =
    orderNerveAffineSimplex v s z at hc
  change orderNerveAffineRealization v (orderNerveRealizationSimplex P s w) =
    orderNerveAffineSimplex v s w at hd
  rw [hc, hd] at hf
  exact (orderNerveAffineSimplex_indicator s hs i z).symm.trans
    (hf.trans (orderNerveAffineSimplex_indicator s hs i w))
