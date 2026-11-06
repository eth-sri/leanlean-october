module
public import OAI.NumberTheory.DirichletL.Reflection.UniformTail
public import OAI.NumberTheory.DirichletL.Reflection.TruncatedSource
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def familyRawScale (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (X QK QP : ℝ) : ℝ :=
  actualKernelCoefficient F s 0 X/(QK^2*QP^2)

section
variable (F : PrimeFamily φ)
include F
lemma familyRawScale_pos
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (X QK QP : ℝ) (hX : 0<X) (hQK : 0<QK) (hQP : 0<QP) : 0<familyRawScale F s X QK QP :=
  div_pos (actualKernelCoefficient_pos F s hc 0 X hX) (mul_pos (sq_pos_of_pos hQK) (sq_pos_of_pos hQP))

lemma literalRawScale_reflected (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (X : ℝ) :
    literalRawScale (F.reflected K hK S) s X=
      actualKernelCoefficient F s 0 X/((Ideal.absNorm K:ℝ)^2*(Ideal.absNorm (∏ i,S.ideal i):ℝ)^2) := by
  have hh := actual_theta_kernel_argument F K hK S s 0 X 1 1
  pm_314 map_one Nat.cast_one one_pow mul_one ramifiedScale pow_zero literalRawScale hh

lemma familyRawScale_le_literal (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (X QK QP : ℝ) (hX : 0<X)
    (hKr : (Ideal.absNorm K:ℝ)≤QK) (hPr : (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP) :
    familyRawScale F s X QK QP≤literalRawScale (F.reflected K hK S) s X := by
  rw [literalRawScale_reflected]
  have hk : (0:ℝ)<Ideal.absNorm K := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hK.1)
  have hp : (0:ℝ)<Ideal.absNorm (∏ i,S.ideal i) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (S.ideal i))))
  apply div_le_div_of_nonneg_left (actualKernelCoefficient_pos F s hc 0 X hX).le (by positivity)
  exact mul_le_mul (pow_le_pow_left₀ hk.le hKr 2) (pow_le_pow_left₀ hp.le hPr 2) (sq_nonneg _) (sq_nonneg _)

lemma reflected_norm_le_centers (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (QK QP : ℝ) (hKr : (Ideal.absNorm K:ℝ)≤QK)
    (hPr : (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP) :
    (Ideal.absNorm (∏ i,(F.reflected K hK S).ideal i):ℝ)≤
      (Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP := by
  rw [F.reflected_product]
  simp only [map_mul,Nat.cast_mul]
  have hk : 0≤QK := le_trans (Nat.cast_nonneg _) hKr
  exact mul_le_mul (mul_le_mul_of_nonneg_left hKr (Nat.cast_nonneg _)) hPr
    (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hk)
end

theorem original_family_dyadic_tail (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
      (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ)
      (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ i, ringChar (Eis⧸(F.reflected K hK S).ideal i)≠2) →
    ∀ jF : φ→ℕ, (∀ i, jF i<6) → ∀ (u : Eisˣ) (θ X T QK QP : ℝ),
      0<X → 0<T → 0<QK → 0<QP →
      (Ideal.absNorm K:ℝ)≤QK → (Ideal.absNorm (∏ i,S.ideal i):ℝ)≤QP →
      ‖∑' i : ℕ×ℕ×ℕ, if i∉retainedDyads (familyRawScale F s X QK QP) (16*T) then
        literalDyadicBlock (F.reflected K hK S) D s hc (reflectedExponent jF)
          (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X u i else 0‖≤
        C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
          T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹ := by
  pm_3267 literal_dyadic_tail_uniform_height_type_uniform
  intro φ σ _ _ F K hK S D s hc hN hbase hchar jF hj u θ X T QK QP hX hT hQK hQP hKr hPr
  pm_3266
  pm_3264
  have hh := hbound (F.reflected K hK S) D s hc hN hbase hchar (reflectedExponent jF) hj'
    (slotIndices φ (PrimeIndex K) σ) u θ X T hX hT
    (fun i => i∉retainedDyads (familyRawScale F s X QK QP) (16*T)) hcut
  pm_3265
end
end SevenEighths.InverseReflectedPhase

end OAI
