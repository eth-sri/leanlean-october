module

public import OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform

@[expose] public section

namespace OAI

section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSourceInputTailSeed
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open CenteredMomentSupportedTailAggregate CenteredMomentSourceMass
open CenteredMomentExceptionalAmplitudePair

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


section
variable (Z Bseed saving seedNorm A : ℝ) (hZ : 0<Z) (hs : 0<seedNorm) (hcap : seedNorm≤Z^Bseed)


include hZ hs hcap in
lemma paid_seed_power    
        :
    Z^(-(saving+Bseed))≤Z^(-saving)/seedNorm := by
  apply (le_div_iff₀ hs).mpr
  calc
    _≤Z^(-(saving+Bseed))*Z^Bseed :=
      mul_le_mul_of_nonneg_left hcap (Real.rpow_nonneg hZ.le _)
    _=Z^(-saving) := by rw [←Real.rpow_add hZ];congr 1;ring

include hZ hs hcap in
lemma paid_seed_term    
        (hA : 0≤A) :
    A*Z^(-(saving+Bseed))≤A*Z^(-saving)/seedNorm := by
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (paid_seed_power Z Bseed saving seedNorm hZ hs hcap) hA

end

end SevenEighths.CenteredMomentSourceInputTailSeed

end

end OAI
