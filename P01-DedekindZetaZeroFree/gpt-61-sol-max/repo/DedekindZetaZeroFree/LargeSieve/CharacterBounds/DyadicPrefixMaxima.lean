module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section


namespace DedekindZetaZeroFree.DetectorMaximalExpressions
noncomputable section
open scoped NumberField Classical

section
variable (F : Type) [Field F] [NumberField F]
include F
def dyadicPrefix  
    (b ω : Ideal (𝓞 F) → ℂ) (N y t : ℝ)  :=
  ∑ᶠ J : Ideal (𝓞 F),
    if J ≠ ⊥ ∧ N < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ y then
      b J * ω J * (Ideal.absNorm J : ℂ) ^ (-Complex.I * (t : ℂ)) else 0





def mass  
    (b : Ideal (𝓞 F) → ℂ) (N : ℝ)  :=
  ∑ᶠ J : Ideal (𝓞 F),
    if J ≠ ⊥ ∧ N < (Ideal.absNorm J : ℝ) ∧ (Ideal.absNorm J : ℝ) ≤ 2 * N then
      ‖b J‖ ^ 2 else 0

def prefixMaximum  
    (b ω : Ideal (𝓞 F) → ℂ) (N t : ℝ)  :=
  sSup {v : ℝ | ∃ y ∈ Set.Icc N (2 * N), v = ‖dyadicPrefix F b ω N y t‖ ^ 2}

def heightMaximum  
    (b ω : Ideal (𝓞 F) → ℂ) (N T : ℝ)  :=
  sSup {v : ℝ | ∃ t ∈ Set.Icc (-T) T, v = prefixMaximum F b ω N t}
end


end
end DedekindZetaZeroFree.DetectorMaximalExpressions
