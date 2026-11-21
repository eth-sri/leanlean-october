module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.WeightedCoefficients
public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.FiniteSupportDigits
public import DedekindZetaZeroFree.CharacterSums.Gauss.Squarefree.PrincipalNormBound

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.CRTAbsoluteSeries
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {F : Type} [Field F] [NumberField F]

abbrev ExteriorIndex (A : SArithmeticData F) :=
  ExteriorSquarefreeIdeal A.cS × A.Exterior × A.Exterior × A.Exterior








section FixedFrequency

variable (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
variable (hCl : Subsingleton (ClassGroup A.R)) (σ : F →+* ℂ)
variable (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
variable (G : A.GaussCorrectionOutput σ η hS)
variable (hD : WeightedFiniteCoefficient.ArithmeticCompatibility A D σ η hS G)
variable (Iu : A.Exterior) (u : A.R) (hu : A.Generates Iu u)
variable (hu_allowed : A.IsAllowed G.B (WeightedFiniteCoefficient.fieldUnit A u hu.1))
variable (hsixthfree : ∀ p : WeightedFiniteCoefficient.ExteriorPrime A,
  idealPrimeExponent p.val.asIdeal Iu.val ≤ 5)
variable (ξ w z : ℂ) (hξ : 4 < ξ.re) (hw : 4 < w.re) (hz : 2 < z.re)


end FixedFrequency

end
end DedekindZetaZeroFree.CRTAbsoluteSeries
