module
public import OAI.NumberTheory.DirichletL.Descent.FirstPhysicalCommon
public import OAI.NumberTheory.DirichletL.Descent.FirstFreshMeasure
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation MeasureTheory
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

abbrev FirstCommonIndex (ι : Type*) :=
  (RayCharacter × RayCharacter) × (Σ _ : Finset ι, Finset ι × Finset ι)

def firstCommonIndices {ι : Type*} [DecidableEq ι] (F : Finset ι) : Finset (FirstCommonIndex ι) :=
  Finset.univ ×ˢ F.powerset.sigma (fun D => (F\D).powerset ×ˢ (F\D).powerset)

def firstCommonNorms {ι : Type*} (p : ι → Eis) (A₁ A₂ C R : ℝ) (d h : Eis)
    (j : FirstCommonIndex ι) : Fin 9 → ℝ :=
  ![A₁,A₂,C,‖eisEmbedding d‖^2,R,primeProductNorm p j.2.1,
    ‖eisEmbedding h‖^2,primeProductNorm p j.2.2.1,primeProductNorm p j.2.2.2]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstCommonWeight (C₁ C₂ : Finset ι → ℂ) (h : Eis) (j : FirstCommonIndex ι) : ℂ :=
  crossCoeff j.1.1 j.1.2 * supportMobius (fun i => Ideal.span {p i}) j.2.1 *
    rowCoprimeMask (fun i => Ideal.span {p i}) j.2.1 h *
    firstCommonCoefficient p hg C₁ C₂ j.1 j.2.1 j.2.2.1 j.2.2.2 h

theorem firstPhysicalCommonRows_indexed (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : Eis) :
    firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h =
    ∑ j ∈ firstCommonIndices F, firstCommonWeight p hg C₁ C₂ h j *
      firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K (firstCommonNorms p A₁ A₂ C R d h j) := by
  pm_437 firstPhysicalCommonRows firstCommonIndices Finset.sum_product Finset.sum_sigma firstCommonWeight firstCommonNorms Finset.mul_sum
  pm_3728
  pm_3811
  ring

end
end SevenEighths.InverseMoment

end OAI
