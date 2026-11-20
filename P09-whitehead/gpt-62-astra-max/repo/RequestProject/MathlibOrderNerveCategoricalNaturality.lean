module

public import RequestProject.MathlibOrderNerveHomology
public import RequestProject.MathlibOrderNerveCycleNaturality

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open CategoryTheory CategoryTheory.Limits
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

variable (f : P → Q) (hf : Monotone f)

/-- The actual monotone-map chain morphism on the degree-two differential segment. -/
noncomputable def mathlibOrderNerveShortComplexMap :
    mathlibOrderNerveShortComplex P ⟶ mathlibOrderNerveShortComplex Q where
  τ₁ := (mathlibOrderNerveChainMap f hf).f 3
  τ₂ := (mathlibOrderNerveChainMap f hf).f 2
  τ₃ := (mathlibOrderNerveChainMap f hf).f 1
  comm₁₂ := by
    have h := (mathlibOrderNerveChainMap f hf).comm 3 2
    assumption
  comm₂₃ := by
    have h := (mathlibOrderNerveChainMap f hf).comm 2 1
    assumption

/-- Actual cycle and quotient maps form Mathlib's verified homology map data. -/
noncomputable def mathlibOrderNerveLeftHomologyMapData :
    ShortComplex.LeftHomologyMapData (mathlibOrderNerveShortComplexMap f hf)
      (mathlibOrderNerveShortComplex P).moduleCatLeftHomologyData
      (mathlibOrderNerveShortComplex Q).moduleCatLeftHomologyData where
  φK := ModuleCat.ofHom _
  φH := ModuleCat.ofHom (mathlibOrderNerveQuotientH2Map f hf)
  commi := rfl
  commf' := by
    ext c
    apply Subtype.ext
    have h := congrArg (fun m :
      ModuleCat.of ℤ (ComposableArrows P 3 →₀ ℤ) ⟶
        ModuleCat.of ℤ (ComposableArrows Q 2 →₀ ℤ) => m c)
      (mathlibOrderNerveShortComplexMap f hf).comm₁₂
    exact h.symm
  commπ := rfl

/-- The actual categorical homology map is conjugate to the genuine differential quotient map. -/
theorem mathlibOrderNerve_homologyMap_eq :
    ShortComplex.homologyMap (mathlibOrderNerveShortComplexMap f hf) =
      (mathlibOrderNerveShortComplex P).moduleCatHomologyIso.hom ≫
        ModuleCat.ofHom (mathlibOrderNerveQuotientH2Map f hf) ≫
          (mathlibOrderNerveShortComplex Q).moduleCatHomologyIso.inv :=
  (mathlibOrderNerveLeftHomologyMapData f hf).homologyMap_eq

/-- A proved zero order-homology map gives the zero actual categorical homology map. -/
theorem mathlibOrderNerve_homologyMap_zero
    (hzero : orderNerveH2Map f hf = 0) :
    ShortComplex.homologyMap (mathlibOrderNerveShortComplexMap f hf) = 0 := by
  simp_all [mathlibOrderNerve_homologyMap_eq, mathlibOrderNerveQuotientH2Map_zero]

/-- The categorical homology comparison commutes with the actual monotone-map homology map. -/
theorem mathlibOrderNerveCategoricalH2Equiv_natural
    (z : OrderNerveH2 P) :
    (ShortComplex.homologyMap (mathlibOrderNerveShortComplexMap f hf)).hom
      (mathlibOrderNerveCategoricalH2Equiv P z) =
        mathlibOrderNerveCategoricalH2Equiv Q (orderNerveH2Map f hf z) := by
  rw [mathlibOrderNerve_homologyMap_eq]
  change (mathlibOrderNerveShortComplex Q).moduleCatHomologyIso.symm.toLinearEquiv
    (mathlibOrderNerveQuotientH2Map f hf
      ((mathlibOrderNerveShortComplex P).moduleCatHomologyIso.toLinearEquiv
        ((mathlibOrderNerveShortComplex P).moduleCatHomologyIso.toLinearEquiv.symm
          (mathlibOrderNerveH2Equiv P z)))) = _
  rw [LinearEquiv.apply_symm_apply, mathlibOrderNerveH2Equiv_natural]
  rfl

end FiniteChains.Comb
