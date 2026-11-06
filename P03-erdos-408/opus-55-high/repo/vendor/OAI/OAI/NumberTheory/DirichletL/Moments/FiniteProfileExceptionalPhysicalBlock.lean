module

public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalPair
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalKernel
public import OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily UniqueFactorizationMonoid
open CenteredMomentCommonRadialData
open CenteredMomentHeckeColumnWindow
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic
open CenteredMomentCommonExceptionalCost
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

def sourceBudget {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal HeckeFamily.O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
    Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
      (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
      2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*
    ((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*
      frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

lemma sourceBudget_nonneg {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal HeckeFamily.O)(U:Finset (CommonIndex C D))
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
