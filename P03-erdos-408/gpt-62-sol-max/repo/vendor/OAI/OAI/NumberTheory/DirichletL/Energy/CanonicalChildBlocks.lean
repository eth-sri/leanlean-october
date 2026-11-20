module

public import OAI.NumberTheory.DirichletL.Energy.CanonicalGaussianContext
public import OAI.NumberTheory.DirichletL.Energy.SeededProfileContext
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
public import OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput

@[expose] public section

namespace OAI.SevenEighths

open scoped Classical SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

/-- Use the supported nonzero child dyads with a width-bounded ray character. -/
abbrev ForCanonicalChildBlocks {ι : Type*} [Fintype ι] (input : Input ι)
    (η : Character) (t K Z a Mcap : ℝ)
    (P : ∀ (C D : Ideal O), Finset (CommonIndex C D) → (Fin 4 → ℤ) → Character → Prop) : Prop :=
    ∀(Scols:Finset (Ideal O))(βsource:Ideal O→ℂ)(C₂ D₂:Ideal O),
    ∀hC₂:Supported C₂,∀hD₂:Supported D₂,primeSupport C₂=primeSupport D₂ →
    ∀(U:Finset (CommonIndex C₂ D₂))(Rwindow:ℝ)(rows:Finset O)(Wkernel:𝓢(ℝ,ℂ))(dyad:Fin 4→ℤ),
    (∀I:Ideal O,βsource I≠0 → a*volume input≤(I.absNorm:ℝ)) →
    physicalBlock η t Scols βsource C₂ D₂ hC₂ hD₂ U Rwindow rows Wkernel K dyad≠0 →
    ∀family:RayCharacter→Character,Family η C₂ D₂ hC₂ hD₂ U family →
    ∀χ:RayCharacter,
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)≤Mcap →
    P C₂ D₂ U dyad (family χ)

end OAI.SevenEighths
