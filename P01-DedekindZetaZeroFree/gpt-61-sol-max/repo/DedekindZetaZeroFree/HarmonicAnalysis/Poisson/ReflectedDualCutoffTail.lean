module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.Ideals.InverseNormPowerSums
public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorFinsets

@[expose] public section


noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.ReflectedTails

section
variable (F : Type*) [Field F] [NumberField F]
    (k : ℝ → ℂ) (T L : ℝ)
include F k T L
def dualCutoffSummand   (d b : Ideal (𝓞 F))  :=
  if b ≠ ⊥ ∧ L < (Ideal.absNorm b : ℝ)
  then k (T * (Ideal.absNorm b : ℝ) / (Ideal.absNorm d : ℝ)) else 0

def dualCutoffTail   (D : Finset (Ideal (𝓞 F)))
    (a : Ideal (𝓞 F) → ℂ)  :=
  ∑ d ∈ D, a d * (T / (Ideal.absNorm d : ℝ) : ℂ) *
    ∑' b : Ideal (𝓞 F), dualCutoffSummand F k T L d b
end


end DedekindZetaZeroFree.LargeSieve.ReflectedTails

end
