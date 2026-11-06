module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.FrequencyNormalConvergence

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawEulerLocal31

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.EulerDomain
open DedekindZetaZeroFree.AllRowEuler.InitialSeparation

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def rawQ (U : RawFrequency D.recipe.A) : ℝ := D.recipe.A.exteriorNorm U.ideal

theorem correctionProduct_subpower (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : RawFrequency D.recipe.A), ∀ p ∈ OmegaStarMargin δ,
      Multipliable (fun pr : LocalFiniteSums.ExteriorPrime D.recipe.A =>
        localCorrection D.context U pr p.1 p.2.1 p.2.2) ∧
      ‖correctionProduct D.context U p.1 p.2.1 p.2.2‖ ≤ C * rawQ D U ^ ε := by
  obtain ⟨C, hC, h⟩ := RawEulerProduct31.correctionProduct_subpower D δ hδ ε hε
  exact ⟨C, hC, fun U p hp => h U p hp⟩

end

end DedekindZetaZeroFree.Quantitative.RawEulerLocal31
