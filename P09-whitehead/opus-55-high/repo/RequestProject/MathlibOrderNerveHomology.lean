import RequestProject.MathlibOrderNerveCycles
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
noncomputable section


namespace FiniteChains.Comb
open CategoryTheory
variable (P : Type) [PartialOrder P]

/-- The actual degree-three to degree-one segment of Mathlib's alternating-face complex. -/
def mathlibOrderNerveShortComplex :=
  ShortComplex.mk
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 2)
    (AlgebraicTopology.AlternatingFaceMapComplex.objD _ 1)
    (by
      apply ModuleCat.hom_ext
      ext c
      exact mathlibOrderNerve_d2_d3 P c)

/-- The genuine order-cell quotient is linearly equivalent to Mathlib's
categorical homology of its actual alternating-face differential segment. -/
def mathlibOrderNerveCategoricalH2Equiv :
    OrderNerveH2 P ≃ₗ[ℤ] (mathlibOrderNerveShortComplex P).homology :=
  (mathlibOrderNerveH2Equiv P).trans
    ((mathlibOrderNerveShortComplex P).moduleCatHomologyIso.symm.toLinearEquiv)

/-- The explicit differential segment is the actual degree-two short complex. -/
def mathlibOrderNerveShortComplexIso :=
  (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      rfl)
    (by
      rfl) :
      mathlibOrderNerveShortComplex P ≅
        (AlgebraicTopology.AlternatingFaceMapComplex.obj
          (mathlibOrderNerveModule P)).sc' 3 2 1) ≪≫
    ((AlgebraicTopology.AlternatingFaceMapComplex.obj
      (mathlibOrderNerveModule P)).isoSc' 3 2 1
        (by simp)
        (by simp)).symm

/-- The order-cell quotient is the actual degree-two categorical homology of
Mathlib's alternating-face chain complex. -/
def mathlibOrderNerveComplexH2Equiv :
    OrderNerveH2 P ≃ₗ[ℤ]
      (AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).homology 2 :=
  (mathlibOrderNerveCategoricalH2Equiv P).trans
    (((ShortComplex.homologyFunctor _).mapIso
      (mathlibOrderNerveShortComplexIso P)).toLinearEquiv)
