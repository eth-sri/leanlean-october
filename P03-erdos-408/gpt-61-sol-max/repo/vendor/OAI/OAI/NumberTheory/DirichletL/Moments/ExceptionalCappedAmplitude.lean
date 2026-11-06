module

public import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceDegree
public import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalEnergy
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAllocationShell

@[expose] public section

namespace OAI


open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentExceptionalCappedAmplitude
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentCounting CenteredMomentHeckeTwist CenteredMomentTwist CenteredMomentHeight CenteredMomentLattice
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondExceptionalCount
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentForcing CenteredMomentChildRows
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw


theorem rowTwistedSum_absolute  η   m A z   W 
     b M t X  (hb : 0≤b) (hM : 0≤M) (hX : 0<X)
    (hs : Function.support W⊆Set.Iic b) (hW : ∀x,‖W x‖≤M) :
    ‖rowTwistedSum η m A z W t X‖≤(128*b*M)*X := by
  have hh := norm_tsum_ideal_ball
    (fun I : Ideal HeckeFamily.O => (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A*z)) I)*
      (Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)) (b*X) M
    (mul_nonneg hb hX.le) hM (by
      change (idealCoeff η (0:Ideal HeckeFamily.O)*_)*_*_=0
      rw [map_zero,zero_mul,zero_mul,zero_mul]) (by
      intro I
      by_cases hI : I=0
      · subst I; simpa only [map_zero,zero_mul,mul_zero,norm_zero] using hM
      · rw [norm_mul]
        exact (mul_le_mul (row_twisted_coefficient_norm η m A z t I hI) (hW _)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul M)) (by
      intro I hI
      exact (div_le_iff₀ hX).mp (hs (right_ne_zero_of_mul hI)))
  exact hh.trans_eq (by ring)

theorem normalized_rectangle_absolute  η   m A z 
     W₁ W₂   b₁ b₂ M₁ M₂ 
    (hb₁ : 0≤b₁) (hb₂ : 0≤b₂) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (hW₁ : ∀x,‖W₁ x‖≤M₁) (hW₂ : ∀x,‖W₂ x‖≤M₂)
     t X₁ X₂ Y₁ Y₂ T  (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hpX : X₁*X₂=T) (hpY : Y₁*Y₂=T) :
    ‖(Real.sqrt T:ℂ)⁻¹ *
      (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
       rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)‖≤
      (2*(128*b₁*M₁)*(128*b₂*M₂))*Real.sqrt T := by
  have hT : 0<T := hpX ▸ mul_pos hX₁ hX₂
  have hsq : 0<Real.sqrt T := Real.sqrt_pos.2 hT
  have hprod (U V : ℝ) (hU : 0<U) (hV : 0<V) :
      ‖rowTwistedSum η m A z W₁ t U*rowTwistedSum η m A z W₂ t V‖≤
        ((128*b₁*M₁)*(128*b₂*M₂))*(U*V) := by
    rw [norm_mul]
    apply (mul_le_mul (rowTwistedSum_absolute η m A z W₁ b₁ M₁ t U hb₁ hM₁ hU hs₁ hW₁)
      (rowTwistedSum_absolute η m A z W₂ b₂ M₂ t V hb₂ hM₂ hV hs₂ hW₂)
      (norm_nonneg _) (by positivity)).trans_eq
    ring
  have hraw := (norm_sub_le
    (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)
    (rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)).trans
      (add_le_add (hprod X₁ X₂ hX₁ hX₂) (hprod Y₁ Y₂ hY₁ hY₂))
  rw [hpX,hpY] at hraw
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hsq.le]
  apply (mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hsq.le)).trans_eq
  have he := Real.sq_sqrt hT.le
  field_simp
  rw [he]
  ring

theorem max_raw_reduction  Z Rred r  (hZ : 1<Z) (hR : 0<Rred) :
    max 1 (Z^r/Rred)=Z^(max (r-Real.logb Z Rred) 0) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have he : Z^r/Rred=Z^(r-Real.logb Z Rred) := by
    rw [Real.rpow_sub hz,Real.rpow_logb hz hZ.ne' hR]
  rw [he]
  by_cases h : 0≤r-Real.logb Z Rred
  · rw [max_eq_left h,max_eq_right (Real.one_le_rpow hZ.le h)]
  · rw [max_eq_right (le_of_not_ge h),Real.rpow_zero,
      max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hZ.le (le_of_not_ge h))]

end SevenEighths.CenteredMomentExceptionalCappedAmplitude



end OAI
