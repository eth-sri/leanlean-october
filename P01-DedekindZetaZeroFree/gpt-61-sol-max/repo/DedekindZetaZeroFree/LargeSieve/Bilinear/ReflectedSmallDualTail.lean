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
    (k : ℝ → ℂ) (T : ℝ)
include F k T
def dualSummand   (d b : Ideal (𝓞 F))  :=
  if b = ⊥ then 0 else k (T * (Ideal.absNorm b : ℝ) / (Ideal.absNorm d : ℝ))

def smallDualTail   (D : Finset (Ideal (𝓞 F)))
    (a : Ideal (𝓞 F) → ℂ)  :=
  ∑ d ∈ D, a d * (T / (Ideal.absNorm d : ℝ) : ℂ) *
    ∑' b : Ideal (𝓞 F), dualSummand F k T d b
end


end DedekindZetaZeroFree.LargeSieve.ReflectedTails

end
