module

public import OAI.NumberTheory.DirichletL.Energy.AllocatedPaid
public import OAI.NumberTheory.DirichletL.Energy.ChildState
public import OAI.NumberTheory.DirichletL.Energy.AllocatedClipped

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalLiveBound
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyAllocatedChildren
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentOriginalRadialComparison CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentRetainedProfile CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

def LiveChild (η:Character)(r:Radial)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(F₁ F₂:Finset (Ideal O))(J:Finset α):Prop:=
  ∃z:O,r.keep z ∧ (r.profile (‖eisEmbedding z‖^2/r.scale)).re≠0 ∧
    child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J≠0

theorem energy_zero_of_not_live (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0<P i)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(F₁ F₂:Finset (Ideal O))(J:Finset α)
    (hF₁:∀I∈F₁,I≠0)(hF₂:∀I∈F₂,I≠0)
    (hn:¬LiveChild η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J):
    allocatedEnergy η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J=0:=by
  rw [←child_radial_eq_energy η r hz D a V₁ V₂ pool β P hP t X₁ X₂ hX₁ hX₂ F₁ F₂ J hF₁ hF₂]
  unfold radialEnergy
  apply (tsum_congr (g:=fun _ : O=>(0:ℝ)) ?_).trans (tsum_zero)
  intro z
  by_cases hk:r.keep z
  · rw [ite_eq_left hk]
    by_cases hφ:(r.profile (‖eisEmbedding z‖^2/r.scale)).re=0
    · rw [hφ,mul_zero]
    · have hc:child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J=0:=by
        by_contra hh
        exact hn ⟨z,hk,hφ,hh⟩
      simp only [hc,norm_zero,zero_pow (by decide:2≠0),zero_mul]
  · rw [ite_eq_right hk]

open CenteredMomentEnergyAllocatedClipped
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyAllocatedPaid
open CenteredMomentEnergyAllocatedProfiles CenteredMomentEnergyAllocatedZero CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentSectorLocalization

end SevenEighths.CenteredMomentEnergyCanonicalLiveBound

end

end OAI
