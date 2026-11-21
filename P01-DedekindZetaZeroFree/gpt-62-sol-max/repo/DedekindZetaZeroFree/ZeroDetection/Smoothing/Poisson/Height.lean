module

public import DedekindZetaZeroFree.ZeroDetection.Smoothing.Poisson.GammaShift

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.DetectorHeight

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.DetectorDef
open scoped Classical
open Filter Topology

variable {F : Type} [Field F] [NumberField F]

def smoothedSum (F : Type) [Field F] [NumberField F] (U : ℝ) {m : Ideal (𝓞 F)}
    (ω : RayClassCharacter F m) (β γ : ℝ) : ℂ :=
  ∑' n : Ideal (𝓞 F),
    ((DetectorDef.a F U n : ℝ) : ℂ) * ω n *
      (Ideal.absNorm n : ℂ) ^ (-((β : ℂ) + (γ : ℂ) * Complex.I)) *
      ((Real.exp (-(Ideal.absNorm n : ℝ) / U ^ DetectorDef.r) : ℝ) : ℂ)

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)



theorem detector_height_numerics (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hρ : 0 < ρ)
    (h1 : ρ < 1 / 10000) (h2 : ρ < 1 / (1000 * (A_F + 1))) :
    -3 / 1250 + A_F * ρ + 1 / 10000 < 0 ∧
      79 / 125 + ρ + 1 / 16000 + 1 / 10000 < 317 /500 := by
  have h2' : ρ * (1000 * (A_F + 1)) < 1 := (lt_div_iff₀ (by linarith)).mp h2
  have hAρ : A_F * ρ < 1 / 1000 := by nlinarith
  constructor
  · linarith
  · linarith





end

end DedekindZetaZeroFree.Quantitative.DetectorHeight
