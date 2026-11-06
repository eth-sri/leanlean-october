module

public import OAI.NumberTheory.DirichletL.MeanSquare.RetainedDensity

@[expose] public section

namespace OAI

noncomputable section


open MulChar AddChar Filter Asymptotics MeasureTheory

open MeasureTheory Real

open Finset Complex

open Filter Real Asymptotics ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Filter Asymptotics

open MeasureTheory Set ActualEisensteinCubic UniqueFactorizationMonoid


namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (columnLog)

end InitialMeanSquare

namespace SecondPassArithmetic

section
open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

lemma firstTail_inverse_scale_bound (K D U:ℝ) (hK:0<K) (hD:0<D) (hU:D≤U):
    ((min 1 (K/D))⁻¹)^2≤(1+U/K)^2 := by
  have hU0:0≤U/K:=div_nonneg (hD.le.trans hU) hK.le
  have hi:(min 1 (K/D))⁻¹≤1+U/K:=by
    by_cases h:1≤K/D
    · rw [min_eq_left h,inv_one];linarith
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h)),inv_div]
      exact (div_le_div_of_nonneg_right hU hK.le).trans (by linarith)
  exact pow_le_pow_left₀ (inv_nonneg.mpr (le_min zero_le_one (div_pos hK hD).le)) hi 2

lemma firstTail_scalar_bound (K D E U₁ U₂ lengthScale B G₁ G₂ P H:ℝ) (A:ℕ)
    (hK:0<K) (hD:0<D) (hE:0<E) (hU₁:0<U₁) (hU₂:0<U₂)
    (hL:0≤lengthScale) (hG₁:0≤G₁) (hG₂:0≤G₂) (hP:0≤P) (hH:0≤H)
    (hDb:D≤lengthScale*B^2) (hEb:E≤B^2) (hU₁b:U₁≤lengthScale) (hU₂b:U₂≤lengthScale):
    (128*U₁)*(128*U₂)*(G₁*G₂*K)*
      (P/((min 1 (K/(D*E*U₁*U₂)))^2*(1+H)^A))≤
    (128*lengthScale)^2*(G₁*G₂*K)*P*(1+lengthScale^3*B^4/K)^2/(1+H)^A := by
  have hden:D*E*U₁*U₂≤lengthScale^3*B^4:=by
    calc
      _ ≤ (lengthScale*B^2)*B^2*lengthScale*lengthScale:=mul_le_mul
        (mul_le_mul (mul_le_mul hDb hEb hE.le (mul_nonneg hL (sq_nonneg _))) hU₁b hU₁.le (by positivity))
        hU₂b hU₂.le (by positivity)
      _ = _:=by ring
  have hi:=firstTail_inverse_scale_bound K (D*E*U₁*U₂) (lengthScale^3*B^4) hK (by positivity) hden
  have hpref:(128*U₁)*(128*U₂)*(G₁*G₂*K)≤(128*lengthScale)^2*(G₁*G₂*K):=by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      _ ≤ (128*lengthScale)*(128*lengthScale):=mul_le_mul (mul_le_mul_of_nonneg_left hU₁b (by norm_num))
        (mul_le_mul_of_nonneg_left hU₂b (by norm_num)) (by positivity) (by positivity)
      _ = _:=by ring
  calc
    _ = ((128*U₁)*(128*U₂)*(G₁*G₂*K))*P*((min 1 (K/(D*E*U₁*U₂)))⁻¹)^2/(1+H)^A:=by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_pow];ring
    _ ≤ _:=by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hpref hP) hi (sq_nonneg _) (by positivity)

variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma cubeCoordinates_radical_bound (b:CubeCoordinates ι) (B:ℝ) (hB:0≤B)
    (hb₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hb₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B):
    primeProductNorm p b.support≤B^2 := by
  have hd:(∏i∈b.support,p i)∣primeProduct p b.support b.leftExponent*primeProduct p b.support b.rightExponent:=by
    rw [←primeProduct_add]
    apply Finset.prod_dvd_prod_of_dvd
    intro i hi
    simpa only [pow_one] using pow_dvd_pow (p i) (b.support_pos i hi)
  have hb0:=mul_ne_zero (primeProduct_ne_zero p hp b.support b.leftExponent)
    (primeProduct_ne_zero p hp b.support b.rightExponent)
  have hn:=element_norm_le_of_dvd hb0 hd
  simp only [map_mul,norm_mul,mul_pow] at hn
  exact hn.trans (by simpa only [pow_two] using mul_le_mul hb₁ hb₂ (sq_nonneg _) hB)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma cubeSourceDivisor_norm_bound (b:CubeCoordinates ι) (C D:Finset ι) (B lengthScale:ℝ)
    (hB:0≤B) (hL:0≤lengthScale) (hCB:Disjoint C b.support)
    (hb₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hb₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B)
    (hC:primeProductNorm p C≤lengthScale)
    (hD:D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit):
    primeProductNorm p D≤lengthScale*B^2 := by
  calc
    _ ≤ primeProductNorm p (C∪b.support):=primeProductNorm_mono p hp
      (hD.trans (Finset.union_subset_union_right (Finset.filter_subset _ _)))
    _ = primeProductNorm p C*primeProductNorm p b.support:=primeProductNorm_union p _ _ hCB
    _ ≤ _:=mul_le_mul hC (cubeCoordinates_radical_bound p hp b B hB hb₁ hb₂)
      (primeProductNorm_pos p hp _).le hL

lemma cubeSourceDivisors_card
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (b:CubeCoordinates ι) (C:Finset ι) (B lengthScale:ℝ) (hB:0<B) (hL:0<lengthScale) (hCB:Disjoint C b.support)
    (hb₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hb₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B)
    (hC:primeProductNorm p C≤lengthScale):
    ((C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.card:ℝ)≤128*(lengthScale*B^2) := by
  let M:=C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit
  have he:boundedPrimeSupports p M (lengthScale*B^2)=M.powerset:=by
    apply Finset.filter_eq_self.mpr
    intro D hD
    exact cubeSourceDivisor_norm_bound p hp b C D B lengthScale hB.le hL.le hCB hb₁ hb₂ hC (Finset.mem_powerset.mp hD)
  rw [←he]
  exact boundedPrimeSupports_card_positive p hp hinj M _ (mul_pos hL (sq_pos_of_pos hB))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceMobiusDivisor_norm_le_one (D:Finset ι):
    ‖(UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)‖≤1 := by
  have hmu : ‖(UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)‖≤1 := by
    unfold UniqueFactorizationMonoid.moebius
    split_ifs <;> simp
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (primeProductNorm_pos p hp D)]
  exact (div_le_div_of_nonneg_right hmu (primeProductNorm_pos p hp D).le).trans
    ((div_le_one (primeProductNorm_pos p hp D)).mpr (primeProductNorm_ge_one p hp D))

end
section

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

end

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

end

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)

variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

end SecondPassArithmetic

end

end OAI
