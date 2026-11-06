module

public import Mathlib

public import DedekindZetaZeroFree.LFunctions.Dedekind.WeightedIdealSummability
public import DedekindZetaZeroFree.LFunctions.Dedekind.MultiplicativeIdealEulerProduct

@[expose] public section


namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField BigOperators

section
variable (K : Type*) [Field K] [NumberField K]
include K
theorem weightedIdealEulerProduct_hasProd
     
    (w : Ideal (𝓞 K) → ℂ)
    (hmul : ∀ I J, w (I * J) = w I * w J)
    (htop : w ⊤ = 1) (hbot : w ⊥ = 0)
    (hnorm : ∀ I, ‖w I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasProd
      (fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
        (1 - w P.asIdeal * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹)
      (∑' I : Ideal (𝓞 K), w I * (Ideal.absNorm I : ℂ) ^ (-s)) := by
  obtain ⟨g, hg⟩ := weightedIdealSummandHom_exists K w hmul htop hbot hnorm s hs
  have hsum : Summable (fun I : Ideal (𝓞 K) => ‖g I‖) := by
    simpa only [hg] using weightedIdealSummability K w hmul htop hbot hnorm s hs
  simpa only [hg] using genericIdealEulerProduct K g hsum

def dedekindZeta_hasSum_nonzeroIdeals
      (s : ℂ) (hs : 1 < s.re)  := DedekindZetaZeroFree.Odlyzko.hasSum_nonzeroIdeal_inverseNormPower K hs

def dedekindZeta_idealEulerProduct_hasProd
      (s : ℂ) (hs : 1 < s.re)  := DedekindZetaZeroFree.Odlyzko.dedekindZeta_primeIdeal_eulerProduct_hasProd K hs
end


end DedekindZetaZeroFree.AbelianQuotient
