module
public import OAI.NumberTheory.DirichletL.Moments.CommonProfile
public import OAI.NumberTheory.DirichletL.Moments.CompleteCommon

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceCommonMask
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentCompleteCommon
variable {ι : Type*} [Fintype ι]

 theorem profile_nonzero_masks
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι)
    (hne : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    IsCoprime (finiteTupleProduct v) R ∧ s∣finiteTupleProduct v := by
  constructor
  · by_contra hn
    exact hne (by simp only [profileCoefficient,hn,ite_false,mul_zero,zero_mul])
  · by_contra hn
    exact hne (by simp only [profileCoefficient,hn,ite_false,mul_zero])
