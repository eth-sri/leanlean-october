module

public import RequestProject.MathlibOrderNerveCategoricalNaturality
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open CategoryTheory
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

variable (f : P → Q) (hf : Monotone f)

/-- The actual differential-segment identification commutes with chain maps. -/
theorem mathlibOrderNerveShortComplexIso_natural :
    mathlibOrderNerveShortComplexMap f hf ≫ (mathlibOrderNerveShortComplexIso Q).hom =
    (mathlibOrderNerveShortComplexIso P).hom ≫
      (HomologicalComplex.shortComplexFunctor (ModuleCat ℤ) _ 2).map
        (mathlibOrderNerveChainMap f hf) := by
  unfold mathlibOrderNerveShortComplexIso
  have h := (HomologicalComplex.natIsoSc' (ModuleCat ℤ) _ 3 2 1
    ((ComplexShape.down ℕ).prev_eq' (by decide))
    ((ComplexShape.down ℕ).next_eq' (by decide))).inv.naturality
      (mathlibOrderNerveChainMap f hf)
  simp only [Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  dsimp only [HomologicalComplex.isoSc', Iso.app] at h ⊢
  rw [← h]
  rfl

/-- The segment and full-chain-complex homology maps agree under the proved identification. -/
theorem mathlibOrderNerveComplex_homologyMap_natural :
    ShortComplex.homologyMap (mathlibOrderNerveShortComplexMap f hf) ≫
      ((ShortComplex.homologyFunctor (ModuleCat ℤ)).mapIso
        (mathlibOrderNerveShortComplexIso Q)).hom =
    ((ShortComplex.homologyFunctor (ModuleCat ℤ)).mapIso
        (mathlibOrderNerveShortComplexIso P)).hom ≫
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ 2).map
        (mathlibOrderNerveChainMap f hf) := by
  change (ShortComplex.homologyFunctor (ModuleCat ℤ)).map _ ≫
      (ShortComplex.homologyFunctor (ModuleCat ℤ)).map _ =
    (ShortComplex.homologyFunctor (ModuleCat ℤ)).map _ ≫
      (ShortComplex.homologyFunctor (ModuleCat ℤ)).map _
  grind [mathlibOrderNerveShortComplexIso_natural]

/-- A proved zero order-homology map induces zero on the actual full Mathlib chain complex. -/
theorem mathlibOrderNerveComplex_homologyMap_zero
    (hzero : orderNerveH2Map f hf = 0) :
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ 2).map
      (mathlibOrderNerveChainMap f hf) = 0 := by
  apply (cancel_epi (((ShortComplex.homologyFunctor (ModuleCat ℤ)).mapIso
    _).hom)).mp
  rw [← mathlibOrderNerveComplex_homologyMap_natural,
    mathlibOrderNerve_homologyMap_zero f hf hzero] <;> simp_all

/-- The actual order-cell homology equivalence is natural on full chain-complex homology. -/
theorem mathlibOrderNerveComplexH2Equiv_natural
    (z : OrderNerveH2 P) :
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ 2).map
      (mathlibOrderNerveChainMap f hf)).hom (mathlibOrderNerveComplexH2Equiv P z) =
      mathlibOrderNerveComplexH2Equiv Q (orderNerveH2Map f hf z) := by
  have h := congrArg (fun k : (mathlibOrderNerveShortComplex P).homology ⟶
      (AlgebraicTopology.AlternatingFaceMapComplex.obj (mathlibOrderNerveModule Q)).homology 2 =>
        k (mathlibOrderNerveCategoricalH2Equiv P z))
    (mathlibOrderNerveComplex_homologyMap_natural f hf)
  change (((ShortComplex.homologyFunctor (ModuleCat ℤ)).mapIso
      _).hom)
        ((ShortComplex.homologyMap (mathlibOrderNerveShortComplexMap f hf)).hom
          (mathlibOrderNerveCategoricalH2Equiv P z)) =
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) _ 2).map
      _).hom _ at h
  rw [mathlibOrderNerveCategoricalH2Equiv_natural] at h
  exact h.symm

end FiniteChains.Comb
