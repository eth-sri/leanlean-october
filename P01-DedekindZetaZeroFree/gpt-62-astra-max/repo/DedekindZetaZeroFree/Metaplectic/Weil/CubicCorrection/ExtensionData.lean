module

public import DedekindZetaZeroFree.Metaplectic.Weil.CubicCorrection.PhaseCharacters
public import DedekindZetaZeroFree.Metaplectic.Weil.NormalizedLocalIndicesAndProductFormula

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.GaussCorrection
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

structure CorrectedWeilExtension (A : SArithmeticData F) (H : A.V → A.V → Fˣ)
    (B : Subgroup A.V) (σ : F →+* ℂ) (hS : A.ContainsTraceBadPlaces) where
  G : A.ArithmeticIdeleClasses →* Circle
  continuous : Continuous G
  finiteOrder : A.IdeleCharacterHasFiniteOrder G
  unramified : A.IdeleCharacterUnramifiedOutside G
  infinity : ∀ (w : InfinitePlace F) (z : w.Completionˣ),
    A.ideleInfiniteComponent G w z = 1
  prime : ∀ (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F))
    (hIv : I.val = v.asIdeal) (p : A.R) (hp : A.Generates I p)
    (a : Fˣ) (ha : A.IsAllowed B a) (hap : (a : F) = (p : F))
    (x : NumberField.IdeleGroup (𝓞 F) F), A.RepresentsExteriorIdeal I x →
      (G (QuotientGroup.mk x) : ℂ) =
        star (σ (A.sexticResidue I (4 : A.R))) * A.idealGauss σ hS I p hp 3

end
end DedekindZetaZeroFree.SArithmeticData.GaussCorrection
