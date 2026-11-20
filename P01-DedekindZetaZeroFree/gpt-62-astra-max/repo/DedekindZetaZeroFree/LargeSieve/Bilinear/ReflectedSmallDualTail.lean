module

public import DedekindZetaZeroFree.Arithmetic.Ideals.InverseNormPowerSums
public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorFinsets

@[expose] public section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.ReflectedTails

variable (F : Type*) [Field F] [NumberField F] (k : ℝ → ℂ) (T : ℝ)

def dualSummand (d b : Ideal (𝓞 F)) : ℂ :=
  if b = ⊥ then 0 else k (T * (Ideal.absNorm b : ℝ) / (Ideal.absNorm d : ℝ))

def smallDualTail (D : Finset (Ideal (𝓞 F)))
    (a : Ideal (𝓞 F) → ℂ) : ℂ :=
  ∑ d ∈ D, a d * (T / (Ideal.absNorm d : ℝ) : ℂ) *
    ∑' b : Ideal (𝓞 F), dualSummand F k T d b

end DedekindZetaZeroFree.LargeSieve.ReflectedTails

end
