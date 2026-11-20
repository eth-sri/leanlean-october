module

public import DedekindZetaZeroFree.LFunctions.Dedekind.MixedThetaPairMellin
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitivePrincipalCharacters

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

open scoped NumberField

theorem principal_prefactor_all_ideal_hasSum
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F) (m : Ideal (𝓞 F))
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (hprimitive : η.IsPrimitive) (hprincipal : η.IsPrincipal)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun I : Ideal (𝓞 F) =>
      (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2) *
        Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F *
        (η I * (Ideal.absNorm I : ℂ) ^ (-s)))
      ((DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).Λ s) := by
  classical
  have hpref :
      (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm m : ℂ)) ^ (s / 2) *
        Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F =
      DedekindZetaZeroFree.AbelianQuotient.zetaGammaFactor F s := by
    simp [(primitivePrincipal_modulus_eq_top η hprimitive hprincipal), DedekindZetaZeroFree.AbelianQuotient.zetaGammaFactor, (NumberField.nrRealPlaces_eq_zero_iff.mpr hF)]
  rw [(((DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair F).hasMellin
    (by exact hs)).2.symm.trans (DedekindZetaZeroFree.AbelianQuotient.Theta.hasMellin_mixedThetaPair F hs).2)]
  convert ((DedekindZetaZeroFree.Odlyzko.hasSum_idealInverseNormPower F hs).mul_left
    (DedekindZetaZeroFree.AbelianQuotient.zetaGammaFactor F s)) using 1
  funext I
  rw [hpref, primitivePrincipal_apply_eq_ite η hprimitive hprincipal I]
  by_cases hI : I = ⊥
  · simp [hI, DedekindZetaZeroFree.Odlyzko.idealInverseNormPower]
  · simp [hI, DedekindZetaZeroFree.Odlyzko.idealInverseNormPower]

end DedekindZetaZeroFree.Hecke
