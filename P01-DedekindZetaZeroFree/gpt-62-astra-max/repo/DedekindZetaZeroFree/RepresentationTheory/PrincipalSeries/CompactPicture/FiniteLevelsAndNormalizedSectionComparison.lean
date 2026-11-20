module
public import DedekindZetaZeroFree.Metaplectic.Torus.ReferenceTensorEvaluation

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteTensorRealizations

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option quotPrecheck false
namespace DedekindZetaZeroFree.KPLiteralScalarHCSourceComparison
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
    (C : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P)

alias localReference_one := DedekindZetaZeroFree.EisensteinReferenceSections.TorusReference.localReference_one

theorem finiteTensorRealization_one
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hT : C.exceptional ⊆ T)
    (x : ∀ q : T, KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C q) :
    (KPGlobalTorusFiniteStages.finiteTensorRealization F ζ hζ P C T hT
      (PiTensorProduct.tprod ℂ x)).val.val 1 = ∏ q : T, (x q).val 1 := by
  rw [KPGlobalTorusFiniteStages.finiteTensorRealization_formula F ζ hζ P C T hT x
    1 (fun _ => 1) 1 (by intro w; rfl) (fun q => (map_one _).symm)
    (by simp)]
  have hlocal (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
      (f : KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C q) :
      KPGlobalTorusFiniteStages.localUntwistedEvaluation F ζ hζ P C q f 1 = f.val 1 := by
    simp [KPGlobalTorusFiniteStages.localUntwistedEvaluation,
      KPGlobalCenterRationalCharacter.localAbs]
  simp_rw [hlocal]
  rw [finprod_eq_prod_of_mulSupport_subset _]
  · rw [← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro q _
    simp
  · intro q hq
    by_contra hn
    apply hq
    have hn' : q ∉ T := hn
    simp only [dite_eq_right hn']
    exact localReference_one F ζ hζ P C q

end DedekindZetaZeroFree.KPLiteralScalarHCSourceComparison

end
