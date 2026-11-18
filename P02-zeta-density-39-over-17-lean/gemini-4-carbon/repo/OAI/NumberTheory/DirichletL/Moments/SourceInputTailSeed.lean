module
public import OAI.NumberTheory.DirichletL.Moments.SourceInputTailUniform

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSourceInputTailSeed
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open CenteredMomentSupportedTailAggregate CenteredMomentSourceMass
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

lemma paid_seed_power (Z Bseed saving seedNorm : ℝ) (hZ : 0<Z)
    (hs : 0<seedNorm) (hcap : seedNorm≤Z^Bseed) :
    Z^(-(saving+Bseed))≤Z^(-saving)/seedNorm := by
  apply (le_div_iff₀ hs).mpr
  calc
    _≤Z^(-(saving+Bseed))*Z^Bseed :=
      mul_le_mul_of_nonneg_left hcap (Real.rpow_nonneg hZ.le _)
    _=Z^(-saving) := by rw [←Real.rpow_add hZ];congr 1;ring

lemma paid_seed_term (Z Bseed saving seedNorm A : ℝ) (hZ : 0<Z)
    (hs : 0<seedNorm) (hcap : seedNorm≤Z^Bseed) (hA : 0≤A) :
    A*Z^(-(saving+Bseed))≤A*Z^(-saving)/seedNorm := by
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (paid_seed_power Z Bseed saving seedNorm hZ hs hcap) hA

end SevenEighths.CenteredMomentSourceInputTailSeed

end

end OAI
