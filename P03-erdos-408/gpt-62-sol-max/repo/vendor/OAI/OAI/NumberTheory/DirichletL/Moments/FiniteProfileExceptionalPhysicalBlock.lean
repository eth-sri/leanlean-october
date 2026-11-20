module

public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalSymmetry
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPairBound
public import OAI.NumberTheory.DirichletL.Moments.CommonWindowColumn
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonHeight
public import OAI.NumberTheory.DirichletL.Moments.LogDyadic
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalCommonSymmetry
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAsymmetricSource
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCount
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalHeight
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalMass
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalGates
public import OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope
public import OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel
public import OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentRowNorm CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair CenteredMomentLogDyadic
open RayFourExpansion CenteredMomentSmooth CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonExceptionalCost
open CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentForcing
open CenteredMomentChildRows ConcretePrimeRowBridge CenteredMomentMobiusRegroup
open CenteredMomentSupportedCorrelation CenteredMomentSupport CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

def sourceBudget {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
    Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
      (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
      2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*
    ((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*
      frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

lemma sourceBudget_nonneg {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ)(hK:0≤K)(hZ:0≤Z)(hCr:0≤Cr):
    0≤sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M:=by
  have hp:=profileMass_nonneg Sprofile s.toData s.toData p p J
  have hf:=frozenProfile_nonneg s
  have hv:0≤volume s.toData:=(volume_pos s.toData).le
  unfold sourceBudget
  positivity

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
