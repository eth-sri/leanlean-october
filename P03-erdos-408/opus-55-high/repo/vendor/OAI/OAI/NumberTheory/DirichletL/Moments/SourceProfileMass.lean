module

public import OAI.NumberTheory.DirichletL.Moments.SourceMass

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentSourceProfileMass
open CenteredMomentPrimary CenteredMomentRectangle
open CenteredMomentAddedZeroUniform

 theorem primary_mod_one (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {(1:ActualEisensteinCubic.O)}) ℂ) (I : Ideal ActualEisensteinCubic.O) :
    primaryIdealCharacter 1 χ I=1 := by
  rw [primaryIdealCharacter_apply]
  have he : Ideal.Quotient.mk (Ideal.span {(1:ActualEisensteinCubic.O)}) (CompletedGauss.primaryGenerator I)=1 := by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {(1:ActualEisensteinCubic.O)}))]
    apply Ideal.Quotient.eq.mpr
    rw [Ideal.span_singleton_one]
    trivial
  rw [he,map_one]

 theorem idealWeight_mod_one (χ : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {(1:ActualEisensteinCubic.O)}) ℂ) (R I : Ideal ActualEisensteinCubic.O) :
    CenteredMomentRectangle.idealWeight 1 χ R 0 I=(if IsCoprime I R then 1 else 0) := by
  simp only [idealWeight,primary_mod_one,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]

def profileCoefficient {ι : Type*} [Fintype ι]
    (R : Ideal ActualEisensteinCubic.O) (ν : ι → Ideal ActualEisensteinCubic.O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal ActualEisensteinCubic.O) (v : Tuple ι) : ℂ :=
  (∏ j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j))*
    (if IsCoprime (finiteTupleProduct v) R then 1 else 0)*
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*v (Sum.inr 0)) (B₂*v (Sum.inr 1))*
    (if s∣finiteTupleProduct v then 1 else 0)

 theorem profileCoefficient_eq_original {ι : Type*} [Fintype ι]
    (R : Ideal ActualEisensteinCubic.O) (ν : ι → Ideal ActualEisensteinCubic.O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal ActualEisensteinCubic.O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      originalFiniteCoefficient 1 (1 : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {(1:ActualEisensteinCubic.O)}) ℂ) R 0
        ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v := by
  rw [originalFiniteCoefficient,idealWeight_mod_one]
  rfl

end SevenEighths.CenteredMomentSourceProfileMass

end

end OAI
