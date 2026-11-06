module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.HeckeSlots
public import OAI.NumberTheory.DirichletL.Moments.Extraction

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeExpansion
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRectangle CenteredMomentPrimary CenteredMomentTwist CenteredMomentMask


def rowWeight (η : Character) (m A z : ActualEisensteinCubic.O) (t : ℝ) : Ideal ActualEisensteinCubic.O →*₀ ℂ where
  toFun I := (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A*z)) I)*
    (Ideal.absNorm I:ℂ)^(Complex.I*t)
  map_one' := by simp only [map_one,Nat.cast_one,Complex.one_cpow,one_mul]
  map_zero' := by simp only [map_zero,zero_mul,mul_zero]
  map_mul' I J := by
    have hpow : ((Ideal.absNorm I:ℂ)*(Ideal.absNorm J:ℂ))^(Complex.I*t) =
        (Ideal.absNorm I:ℂ)^(Complex.I*t)*(Ideal.absNorm J:ℂ)^(Complex.I*t) := by
      exact_mod_cast Complex.mul_cpow_ofReal_nonneg
        (Nat.cast_nonneg (Ideal.absNorm I) : (0:ℝ) ≤ Ideal.absNorm I)
        (Nat.cast_nonneg (Ideal.absNorm J) : (0:ℝ) ≤ Ideal.absNorm J) (Complex.I*t)
    simp only [map_mul,Nat.cast_mul,hpow]
    ring

section
variable (η : Character) (m A z : ActualEisensteinCubic.O)

theorem rowTwistedSum_eq_weight      t   W   X  :
    rowTwistedSum η m A z W t X =
      ∑' I : Ideal ActualEisensteinCubic.O, rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X) := rfl

theorem rowSlot_eq_weight      S 
     β   t  :
    rowSlot η m A z S β t = ∑ P ∈ S, β P*rowWeight η m A z t P := by
  unfold rowSlot
  apply Finset.sum_congr rfl
  intro P hP
  simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk]
  ring

theorem actual_hecke_rectangle_sum
         t 
     W₁ W₂  (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑' I : Ideal ActualEisensteinCubic.O, ∑' J : Ideal ActualEisensteinCubic.O,
      rowWeight η m A z t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      rowTwistedSum η m A z W₁ t X₁ * rowTwistedSum η m A z W₂ t X₂ -
        rowTwistedSum η m A z W₁ t Y₁ * rowTwistedSum η m A z W₂ t Y₂ := by
  let w := rowWeight η m A z t
  let f₁ := fun I : Ideal ActualEisensteinCubic.O => w I * W₁ ((Ideal.absNorm I : ℝ) / X₁)
  let f₂ := fun J : Ideal ActualEisensteinCubic.O => w J * W₂ ((Ideal.absNorm J : ℝ) / X₂)
  let g₁ := fun I : Ideal ActualEisensteinCubic.O => w I * W₁ ((Ideal.absNorm I : ℝ) / Y₁)
  let g₂ := fun J : Ideal ActualEisensteinCubic.O => w J * W₂ ((Ideal.absNorm J : ℝ) / Y₂)
  have hf₁ : Summable f₁ := annular_ideal_sum_summable w W₁ b₁ X₁ hX₁ hs₁
  have hf₂ : Summable f₂ := annular_ideal_sum_summable w W₂ b₂ X₂ hX₂ hs₂
  have hg₁ : Summable g₁ := annular_ideal_sum_summable w W₁ b₁ Y₁ hY₁ hs₁
  have hg₂ : Summable g₂ := annular_ideal_sum_summable w W₂ b₂ Y₂ hY₂ hs₂
  have hterm (I J : Ideal ActualEisensteinCubic.O) :
      rowWeight η m A z t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        f₁ I * f₂ J - g₁ I * g₂ J := by
    rw [map_mul]
    grind [idealRectangle]
  simp_rw [hterm]
  have hinner (I : Ideal ActualEisensteinCubic.O) : (∑' J : Ideal ActualEisensteinCubic.O, (f₁ I * f₂ J - g₁ I * g₂ J)) =
      f₁ I * (∑' J : Ideal ActualEisensteinCubic.O, f₂ J) - g₁ I * (∑' J : Ideal ActualEisensteinCubic.O, g₂ J) := by
    rw [Summable.tsum_sub (hf₂.mul_left _) (hg₂.mul_left _), tsum_mul_left, tsum_mul_left]
  simp_rw [hinner]
  rw [Summable.tsum_sub (hf₁.mul_right _) (hg₁.mul_right _), tsum_mul_right, tsum_mul_right]
  simp only [rowTwistedSum_eq_weight]
  rfl

end

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section
variable (η : Character) (m A z : ActualEisensteinCubic.O) (S : ι → Finset (Ideal ActualEisensteinCubic.O)) (β : ι → Ideal ActualEisensteinCubic.O → ℂ) (t : ℝ)

theorem live_slot_product      
        :
    (∏ i,rowSlot η m A z (S i) (β i) t) =
      ∑ v : (i : ι) → S i, (∏ i,β i (v i))*rowWeight η m A z t (∏ i,(v i:Ideal ActualEisensteinCubic.O)) := by
  have hs (i : ι) : rowSlot η m A z (S i) (β i) t =
      ∑ P : S i, β i P*rowWeight η m A z t P := by
    rw [rowSlot_eq_weight]
    exact (Finset.sum_coe_sort (S i) (fun P => β i P*rowWeight η m A z t P)).symm
  simp_rw [hs]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [map_prod,← Finset.prod_mul_distrib]

theorem actual_slot_rectangle_sum    
         
     W₁ W₂  (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑ v : (i : ι) → S i, (∏ i,β i (v i))*
      ∑' I : Ideal ActualEisensteinCubic.O, ∑' J : Ideal ActualEisensteinCubic.O,
        rowWeight η m A z t ((∏ i,(v i:Ideal ActualEisensteinCubic.O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
       rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)*
       ∏ i,rowSlot η m A z (S i) (β i) t := by
  have ht (v : (i : ι) → S i) (I J : Ideal ActualEisensteinCubic.O) :
      rowWeight η m A z t ((∏ i,(v i:Ideal ActualEisensteinCubic.O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        rowWeight η m A z t (∏ i,(v i:Ideal ActualEisensteinCubic.O))*
          (rowWeight η m A z t (I*J)*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) := by
    simp only [map_mul]; ring
  simp_rw [ht,tsum_mul_left]
  rw [actual_hecke_rectangle_sum η m A z t W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂,
    live_slot_product]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem common_extracted_slot_rectangle    
         
     W₁ W₂   X₁ X₂ Y₁ Y₂   B₁ B₂  :
    (∑ v : (i : ι) → S i, (∏ i,β i (v i))*
      ∑' I : Ideal ActualEisensteinCubic.O, ∑' J : Ideal ActualEisensteinCubic.O,
        rowWeight η m A z t ((∏ i,(v i:Ideal ActualEisensteinCubic.O))*(B₁*I)*(B₂*J))*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)) =
      rowWeight η m A z t (B₁*B₂)*
        ∑ v : (i : ι) → S i, (∏ i,β i (v i))*
          ∑' I : Ideal ActualEisensteinCubic.O, ∑' J : Ideal ActualEisensteinCubic.O,
            rowWeight η m A z t ((∏ i,(v i:Ideal ActualEisensteinCubic.O))*I*J)*
              idealRectangle W₁ W₂ (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
                (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) I J := by
  have ht (v : (i : ι) → S i) (I J : Ideal ActualEisensteinCubic.O) :
      rowWeight η m A z t ((∏ i,(v i:Ideal ActualEisensteinCubic.O))*(B₁*I)*(B₂*J))*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J) =
      rowWeight η m A z t (B₁*B₂)*
        (rowWeight η m A z t ((∏ i,(v i:Ideal ActualEisensteinCubic.O))*I*J)*
          idealRectangle W₁ W₂ (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
            (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) I J) := by
    rw [CenteredMomentExtraction.idealRectangle_extract]
    simp only [map_mul]
    ring
  simp_rw [ht,tsum_mul_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

end

end SevenEighths.CenteredMomentHeckeExpansion

end

end OAI
