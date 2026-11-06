module

public import OAI.NumberTheory.DirichletL.Moments.WholeSlotDeletion

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.CenteredMomentSlotNormalization
open HeckeFamily CenteredMomentRetainedEnergy
open CenteredMomentWholeSlotDeletion

lemma sqrt_product_normalizer {ι:Type*} [Fintype ι] (X:ℝ) (P:ι→ℝ)
    (hX:0≤X) (hP:∀i,0≤P i) :
    ((Real.sqrt X:ℂ)⁻¹)*(∏i,(Real.sqrt (P i):ℂ)⁻¹)=
      (Real.sqrt (X*∏i,P i):ℂ)⁻¹ := by
  rw [Real.sqrt_mul hX,Real.sqrt_prod _ (by grind),Complex.ofReal_mul,
    Complex.ofReal_prod,mul_inv_rev,Finset.prod_inv_distrib]
  ring

theorem selectedProduct_univ {ι:Type*} [Fintype ι] [DecidableEq ι]
    (η:Character) (m A z:HeckeFamily.O) (W₁ W₂:ℝ→ℂ)
    (S:ι→Finset (Ideal HeckeFamily.O)) (β:ι→Ideal HeckeFamily.O→ℂ) (P:ι→ℝ)
    (t X₁ X₂:ℝ) (hX:0≤X₁*X₂) (hP:∀i,0≤P i) :
    selectedProduct Finset.univ η m A z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ := by
  unfold selectedProduct normalizedSlot positiveSlotRow
  rw [Finset.prod_mul_distrib]
  have he:=sqrt_product_normalizer (X₁*X₂) P hX hP
  grind

end SevenEighths.CenteredMomentSlotNormalization

end

end OAI
