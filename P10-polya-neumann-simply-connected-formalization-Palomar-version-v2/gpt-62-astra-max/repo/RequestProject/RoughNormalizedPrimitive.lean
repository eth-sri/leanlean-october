module

public import RequestProject.BoundaryFourier
public import RequestProject.FiniteFourierChartRemainder
public import RequestProject.LocalConformalPrincipalFactorization

/-!
# The genuine periodic primitive of a normalized negative-half-order load

The input is an arbitrary normalized Fourier vector. Its load coefficients
are `Lambda^(1/2) y`, not necessarily the Fourier coefficients of an L2
function. Removing the constant load produces an actual BoundaryL2
primitive with half a Sobolev derivative. Its derivative identity is proved
coefficientwise, including frequency zero, and in weak Fourier pairing.

No endpoint value is assigned to this critical half-order primitive.
For a finite Fourier chart, regularity of its positive primitive implies
half-order regularity of the actual chart output and input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace ComplexConjugate

section

variable (y : L2Z) (n : ℤ)

include n in
/-- The phase of the inverse tangential derivative, with a harmless value
at zero; the inverse-absolute-frequency operator removes that mode. -/
def roughPrimitivePhase : ℂ :=
  if 0 < n then -Complex.I else Complex.I

theorem norm_roughPrimitivePhase : ‖roughPrimitivePhase n‖ = 1 := by
  unfold roughPrimitivePhase
  split_ifs <;> simp

def roughPrimitivePhaseOperator : FourierOp :=
  diagOp roughPrimitivePhase 1 (fun n => (norm_roughPrimitivePhase n).le)

def roughNormalizedPrimitiveCore : FourierOp :=
  roughPrimitivePhaseOperator.comp normalizedInverseAbsOperator

@[simp] theorem roughNormalizedPrimitiveCore_apply :
    roughNormalizedPrimitiveCore y n =
      roughPrimitivePhase n * normalizedInverseAbsSymbol n * y n := by
  simp [roughNormalizedPrimitiveCore, roughPrimitivePhaseOperator]
  ring

/-- Actual Fourier synthesis of the mean-zero periodic primitive. -/
def roughNormalizedPrimitiveFourier : FourierOp :=
  (sobolevSmoothing halfOrder (by norm_num)).comp roughNormalizedPrimitiveCore

/-- An actual ordinary-measure boundary L2 element, even for a rough load. -/
def roughNormalizedPrimitive : L2Z →L[ℂ] BoundaryL2 :=
  boundaryFourier.symm.toLinearIsometry.toContinuousLinearMap.comp
    roughNormalizedPrimitiveFourier

@[simp] theorem boundaryFourier_roughNormalizedPrimitive :
    boundaryFourier (roughNormalizedPrimitive y) = roughNormalizedPrimitiveFourier y := boundaryFourier.apply_symm_apply _

theorem roughNormalizedPrimitiveFourier_apply :
    roughNormalizedPrimitiveFourier y n =
      ((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) *
        (roughPrimitivePhase n * normalizedInverseAbsSymbol n * y n) := by
  change fromL2 halfOrder (roughNormalizedPrimitiveCore y) n = _
  simp [fromL2]

include y in
/-- Genuine negative-half-order load coefficients, in unitary Fourier
normalization. This definition makes no ordinary L2 load assertion. -/
def roughNormalizedLoadCoeff : ℤ → ℂ := fromL2 (-halfOrder) y

theorem roughNormalizedLoadCoeff_apply :
    roughNormalizedLoadCoeff y n = (Real.sqrt (sobWeight n) : ℂ) * y n := by
  unfold roughNormalizedLoadCoeff fromL2
  rw [neg_neg, ← Real.sqrt_eq_rpow]

end

section

variable (y t : L2Z) (hfin : (Function.support (((1 - posProj) y : L2Z) : ℤ → ℂ)).Finite)
    (ht : IsSobolevSeq 1 (t : ℤ → ℂ))
    (hp : IsSobolevSeq 1 (posProj (boundaryFourier (roughNormalizedPrimitive y)) : ℤ → ℂ))
    (n : ℤ) (hn : n ≠ 0)

private theorem rough_frequency_phase :
    (Complex.I * (n : ℂ)) * roughPrimitivePhase n = ((|(n : ℝ)| : ℝ) : ℂ) := by
  by_cases hn : 0 < n
  · 
    rw [roughPrimitivePhase, if_pos hn, abs_of_pos (by exact_mod_cast hn), Complex.ofReal_intCast]
    calc
      _ =
          -(Complex.I * Complex.I) * n := by ring
      _ = _ := by simp
  · 
    rw [roughPrimitivePhase, if_neg hn, abs_of_nonpos (by exact_mod_cast (le_of_not_gt hn)), Complex.ofReal_neg,
      Complex.ofReal_intCast]
    calc
      _ =
          (Complex.I * Complex.I) * n := by ring
      _ = _ := by simp

include hn in
private theorem rough_primitive_core_derivative :
    (Complex.I * (n : ℂ)) *
      (roughPrimitivePhase n * normalizedInverseAbsSymbol n) = (sobWeight n : ℂ) := by
  
  rw [← mul_assoc, rough_frequency_phase, normalizedInverseAbsSymbol, if_neg hn,
    Complex.ofReal_div]
  apply mul_div_cancel₀ _
  simp [*]

private theorem rough_weight_half :
    sobWeight n ^ (-halfOrder) * sobWeight n = sobWeight n ^ halfOrder := by
  conv_lhs => rhs; rw [← Real.rpow_one (sobWeight n)]
  rw [← Real.rpow_add (sobWeight_pos n)]
  norm_num

include hn in
/-- The true derivative coefficients at every nonzero frequency. -/
theorem roughNormalizedPrimitive_derivative_ne_zero :
    (Complex.I * (n : ℂ)) * boundaryFourier (roughNormalizedPrimitive y) n =
      roughNormalizedLoadCoeff y n := by
  rw [boundaryFourier_roughNormalizedPrimitive, roughNormalizedPrimitiveFourier_apply]
  calc
    _ = (sobWeight n ^ (-halfOrder) : ℝ) *
        ((Complex.I * n) *
          (roughPrimitivePhase n * normalizedInverseAbsSymbol n)) * y n := by ring
    _ = (sobWeight n ^ (-halfOrder) : ℝ) * (sobWeight n) * y n := by
      rw [rough_primitive_core_derivative n hn]
    _ = _ := by
      rw [← Complex.ofReal_mul, rough_weight_half]
      simp [roughNormalizedLoadCoeff, fromL2]

/-- The constant load is separate: a periodic primitive differentiates to
the load minus its actual constant Fourier coefficient. -/
theorem roughNormalizedPrimitive_derivative :
    (Complex.I * (n : ℂ)) * boundaryFourier (roughNormalizedPrimitive y) n =
      roughNormalizedLoadCoeff (y - zeroModeProjection y) n := by
  by_cases hn : n = 0
  · subst n
    simp [roughNormalizedLoadCoeff, fromL2]
  · rw [roughNormalizedPrimitive_derivative_ne_zero y n hn]
    simp [roughNormalizedLoadCoeff, fromL2, if_neg hn, sub_zero]

include ht in
theorem rough_test_derivative_memℓp :
    Memℓp (fun n : ℤ => (Complex.I * (n : ℂ)) * t n) 2 := by
  refine memℓp_two_iff_summable.mpr ?_
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) ht
  simp
  exact pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_right (by simp [sobWeight])
      (norm_nonneg _)) 2

include ht in
/-- The actual L2 Fourier derivative of a genuinely H1 test sequence. -/
def roughFourierTestDerivative : L2Z :=
  ⟨fun n => (Complex.I * (n : ℂ)) * t n, rough_test_derivative_memℓp t ht⟩

@[simp] theorem roughFourierTestDerivative_apply :
    roughFourierTestDerivative t ht n = (Complex.I * (n : ℂ)) * t n := rfl

/-- A true weak derivative identity, tested against every H1 Fourier
vector. Both pairings are actual L2 inner products, and the mean load
remains separate. No regularity of the rough input is assumed. -/
theorem roughNormalizedPrimitive_weak_pairing :
    ⟪roughFourierTestDerivative t ht,
      boundaryFourier (roughNormalizedPrimitive y)⟫_ℂ =
      -⟪sobVec halfOrder (t : ℤ → ℂ)
        ((sobNormSq_mono (by norm_num : halfOrder ≤ 1) ht).1),
          y - zeroModeProjection y⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, ← tsum_neg]
  apply tsum_congr
  intro n
  simp only [RCLike.inner_apply', roughFourierTestDerivative_apply, sobVec_apply]
  
  
  have he : roughNormalizedLoadCoeff (y - zeroModeProjection y) n =
      (sobWeight n ^ halfOrder : ℝ) * (y - zeroModeProjection y) n := by
    simp [roughNormalizedLoadCoeff, fromL2]
  simp only [map_mul, Complex.conj_I, map_intCast, Complex.conj_ofReal]
  calc
    _ = -(conj _ * ((Complex.I * n) *
        boundaryFourier _ n)) := by ring
    _ = -(conj _ *
        ((sobWeight n ^ halfOrder : ℝ) * (y - zeroModeProjection y) n)) := by
      rw [(roughNormalizedPrimitive_derivative y n), he]
    _ = _ := by ring

include hp in
/-- A regular positive primitive controls the positive normalized load.
No regularity of its unknown negative sector is assumed. -/
theorem roughNormalizedLoad_pos_half_of_primitive_pos_one :
    IsSobolevSeq halfOrder (posProj y : ℤ → ℂ) := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hp
  by_cases hn : 0 < n
  · have he := congrArg norm (roughNormalizedPrimitive_derivative_ne_zero y n hn.ne')
    rw [roughNormalizedLoadCoeff_apply, norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_intCast, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] at he
    simp only [posProj, diagOp_apply, if_pos hn, one_mul, Real.rpow_one]
    rw [← Real.sqrt_eq_rpow, ← he]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right (by simp [sobWeight])
        (norm_nonneg _)) 2
  · simp only [posProj, diagOp_apply, if_neg hn, zero_mul, norm_zero, mul_zero]
    exact le_rfl

include hfin hp in
/-- When the other Fourier sector has finite support, positive primitive
regularity proves half-order regularity of the full normalized input. -/
theorem roughNormalizedLoad_half_of_primitive_pos_one :
    IsSobolevSeq halfOrder (y : ℤ → ℂ) := by
  
  
  have heq : posProj y + (1 - posProj) y = y := by
    simp
  
  rw [← heq]
  exact (fourierSobolevSubmodule halfOrder).add_mem (roughNormalizedLoad_pos_half_of_primitive_pos_one y hp) (isSobolevSeq_of_finite_fourier_support halfOrder hfin)

end

private theorem rough_nonpositive_part_support {b : L2Z}
    (hb : (Function.support (b : ℤ → ℂ)).Finite) :
    (Function.support (((1 - posProj) b : L2Z) : ℤ → ℂ)).Finite := by
  refine hb.subset ?_
  intro n hn
  by_contra hb0
  
  exact hn (by simp [posProj, (not_not.mp hb0)])

/-- The genuine finite Fourier chart has only finitely many nonpositive
output coefficients, regardless of the regularity of its input. -/
theorem finiteFourierChart_nonpositive_part_finite {d : ℕ}
    (u : Fin d → nonpositiveFourierSubspaceᗮ) (v : Fin d → L2Z)
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    (z : nonpositiveFourierSubspaceᗮ) :
    (Function.support
      (((1 - posProj) (finiteFourierChart u v z) : L2Z) : ℤ → ℂ)).Finite := by
  have hfin : finiteFourierChart u v z - (z : L2Z) ∈ finiteFourierSubmodule := by
    simp only [finiteFourierChart, ContinuousLinearMap.add_apply, Submodule.subtypeL_apply,
      add_sub_cancel_left]
    rw [ContinuousLinearMap.sum_apply]
    apply Submodule.sum_mem
    intro r _
    exact finiteFourierSubmodule.smul_mem _ (hv r)
  have hzpos : posProj z = z := by
    rw [← nonpositive_orthogonal_starProjection]
    exact Submodule.starProjection_mem_subspace_eq_self z
  have hzero : (1 - posProj) z = 0 := by
    simp [hzpos, sub_self]
  have heq : (1 - posProj) (finiteFourierChart u v z) =
      (1 - posProj) (finiteFourierChart u v z - z) := by
    rw [map_sub, hzero, sub_zero]
  rw [heq]
  exact rough_nonpositive_part_support hfin

/-- The rough chart bootstrap has a genuine, checkable primitive premise.
It does not assume that the normalized load is already half regular. -/
theorem finiteFourierChart_half_of_rough_primitive_pos_one {d : ℕ}
    (u : Fin d → nonpositiveFourierSubspaceᗮ) (v : Fin d → L2Z)
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    (z : nonpositiveFourierSubspaceᗮ)
    (hp : IsSobolevSeq 1
      (posProj (boundaryFourier (roughNormalizedPrimitive (finiteFourierChart u v z))) :
        ℤ → ℂ)) :
    IsSobolevSeq halfOrder (finiteFourierChart u v z : ℤ → ℂ) ∧
      IsSobolevSeq halfOrder ((z : L2Z) : ℤ → ℂ) := by
  have hy := roughNormalizedLoad_half_of_primitive_pos_one _
    (finiteFourierChart_nonpositive_part_finite u v hv z) hp
  refine ⟨hy, ?_⟩
  
  have heq : z = finiteFourierChart u v z -
      (finiteFourierChart u v z - z) := by abel
  
  rw [heq]
  exact (fourierSobolevSubmodule (1 / 2)).sub_mem hy (finiteFourierChart_correction_sobolev u v hv _ z)

end PolyaNeumann

end
