import RequestProject.MathlibOrderNerveCategoricalNaturality
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

/-- The actual differential-segment identification commutes with chain maps. -/
theorem mathlibOrderNerveShortComplexIso_natural f hf :
    mathlibOrderNerveShortComplexMap f hf ≫ (mathlibOrderNerveShortComplexIso Q).hom =
    (mathlibOrderNerveShortComplexIso P).hom ≫
      (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map
        (mathlibOrderNerveChainMap f hf) := by
  unfold mathlibOrderNerveShortComplexIso
  have h := (HomologicalComplex.natIsoSc' _ _ 3 2 1
    ((ComplexShape.down ℕ).prev_eq' (by rfl))
    ((ComplexShape.down ℕ).next_eq' (by rfl))).inv.naturality
      (mathlibOrderNerveChainMap f hf)
  tauto

/-- The segment and full-chain-complex homology maps agree under the proved identification. -/
theorem mathlibOrderNerveComplex_homologyMap_natural f hf :
    ShortComplex.homologyMap (mathlibOrderNerveShortComplexMap f hf) ≫
      ((ShortComplex.homologyFunctor (ModuleCat ℤ)).mapIso
        (mathlibOrderNerveShortComplexIso Q)).hom =
    ((ShortComplex.homologyFunctor (ModuleCat ℤ)).mapIso
        (mathlibOrderNerveShortComplexIso P)).hom ≫
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map
        (mathlibOrderNerveChainMap f hf) := by
  change (ShortComplex.homologyFunctor _).map _ ≫
      (ShortComplex.homologyFunctor _).map _ =
    (ShortComplex.homologyFunctor _).map _ ≫
      (ShortComplex.homologyFunctor _).map _
  grind [← Functor.map_comp, mathlibOrderNerveShortComplexIso_natural]

/-- A proved zero order-homology map induces zero on the actual full Mathlib chain complex. -/
theorem mathlibOrderNerveComplex_homologyMap_zero (f : P → Q) hf
    (hzero : orderNerveH2Map f hf = 0) :
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map
      (mathlibOrderNerveChainMap f hf) = 0 := by
  apply (cancel_epi (((ShortComplex.homologyFunctor (ModuleCat ℤ)).mapIso
    (mathlibOrderNerveShortComplexIso P)).hom)).mp
  rw [← mathlibOrderNerveComplex_homologyMap_natural,
    mathlibOrderNerve_homologyMap_zero f hf hzero]
  simp

/-- The actual order-cell homology equivalence is natural on full chain-complex homology. -/
theorem mathlibOrderNerveComplexH2Equiv_natural f hf
    z :
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) 2).map
      (mathlibOrderNerveChainMap f hf)).hom (mathlibOrderNerveComplexH2Equiv P z) =
      mathlibOrderNerveComplexH2Equiv Q (orderNerveH2Map f hf z) := by
  have h := congrArg (fun k =>
        k (mathlibOrderNerveCategoricalH2Equiv P z))
    (mathlibOrderNerveComplex_homologyMap_natural f hf)
  change (((ShortComplex.homologyFunctor _).mapIso
      (mathlibOrderNerveShortComplexIso Q)).hom)
        ((ShortComplex.homologyMap (mathlibOrderNerveShortComplexMap f hf)).hom
          (mathlibOrderNerveCategoricalH2Equiv P z)) =
    ((HomologicalComplex.homologyFunctor _ _ 2).map
      (mathlibOrderNerveChainMap f hf)).hom (mathlibOrderNerveComplexH2Equiv P z) at h
  rw [mathlibOrderNerveCategoricalH2Equiv_natural] at h
  exact h.symm
