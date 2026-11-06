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
    (g : ℝ → ℂ) (T : ℝ)
include F g T
def primalSummand   (d b : Ideal (𝓞 F))  :=
  if b = ⊥ then 0 else g ((Ideal.absNorm d : ℝ) * (Ideal.absNorm b : ℝ) / T)

def primalTail   (D : Finset (Ideal (𝓞 F)))
    (a : Ideal (𝓞 F) → ℂ)  :=
  ∑ d ∈ D, a d * ∑' b : Ideal (𝓞 F), primalSummand F g T d b
end


end DedekindZetaZeroFree.LargeSieve.ReflectedTails

end
