module

public import RequestProject.MathlibOrderNerveCycles
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

noncomputable section

namespace FiniteChains.Comb
open CategoryTheory
variable (P : Type) [PartialOrder P]

/-- The actual degree-three to degree-one segment of Mathlib's alternating-face complex. -/
def mathlibOrderNerveShortComplex :=
  ShortComplex.mk
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 2)
    (AlgebraicTopology.AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) 1)
    (by
      ext c
      exact mathlibOrderNerve_d2_d3 P c)

/-- The genuine order-cell quotient is linearly equivalent to Mathlib's
categorical homology of its actual alternating-face differential segment. -/
def mathlibOrderNerveCategoricalH2Equiv :=
  (mathlibOrderNerveH2Equiv P).trans
    ((mathlibOrderNerveShortComplex P).moduleCatHomologyIso.symm.toLinearEquiv)

/-- The explicit differential segment is the actual degree-two short complex. -/
def mathlibOrderNerveShortComplexIso :=
  (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (rfl)
    (rfl) :
      mathlibOrderNerveShortComplex P ≅
        (AlgebraicTopology.AlternatingFaceMapComplex.obj
          (mathlibOrderNerveModule P)).sc' 3 2 1) ≪≫
    ((AlgebraicTopology.AlternatingFaceMapComplex.obj
      (mathlibOrderNerveModule P)).isoSc' 3 2 1
        ((ComplexShape.down ℕ).prev_eq' (by decide))
        ((ComplexShape.down ℕ).next_eq' (by decide))).symm

/-- The order-cell quotient is the actual degree-two categorical homology of
Mathlib's alternating-face chain complex. -/
def mathlibOrderNerveComplexH2Equiv :
    OrderNerveH2 P ≃ₗ[ℤ]
      (AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule P)).homology 2 :=
  (mathlibOrderNerveCategoricalH2Equiv P).trans
    (((ShortComplex.homologyFunctor (ModuleCat ℤ)).mapIso
      (mathlibOrderNerveShortComplexIso P)).toLinearEquiv)

end FiniteChains.Comb
