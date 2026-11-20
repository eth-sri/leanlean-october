module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskWeakModes
public import RequestProject.DiskAreaBessel
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import RequestProject.PlanarNotation

/-!
# The genuine antiholomorphic H¹ extension on the disk

The construction uses the actual compactly supported harmonic test vectors.
Their H¹ Gram matrix includes both area mass and gradient energy, including
the constant mode. Orthogonal synthesis completes their finite sums in the
physical H¹ space; applying the continuous half trace recovers exactly the
nonpositive Fourier projection. No harmonic extension theorem is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real Filter
open scoped ComplexConjugate InnerProductSpace Topology ENNReal

abbrev DiskHardyCoefficients := lp (fun _ : ℕ => ℂ) 2

section

variable (m : ℕ)
include m

/-- The full physical H¹ mass of the mode `conj(z)^m`. -/
def diskAntiholomorphicH1Weight : ℝ :=
  π / ((m + 1 : ℕ) : ℝ) + anglePeriod * (m : ℝ)

theorem diskAntiholomorphicH1Weight_pos :
    0 < diskAntiholomorphicH1Weight m := by
  unfold diskAntiholomorphicH1Weight
  positivity

theorem hardy_value_antiholomorphicTest :
    h1Value unitDisk (diskAntiholomorphicH1Test m) =
      diskAntiholomorphicArea m :=
  (by measurability)

private theorem hardy_gradient_antiholomorphicTest (n : ℕ) :
    (∑ i : Fin 2,
      ⟪h1Gradient unitDisk i (diskAntiholomorphicH1Test m),
        h1Gradient unitDisk i (diskAntiholomorphicH1Test n)⟫_ℂ) =
      if m = n then (anglePeriod : ℂ) * (m : ℂ) else 0 := by
  
  exact inner_diskAntiholomorphicGradient m n

end

/-- The true H¹ Gram matrix; the zero mode has weight `π`. -/
theorem inner_diskAntiholomorphicH1Test (m n : ℕ) :
    ⟪diskAntiholomorphicH1Test m, diskAntiholomorphicH1Test n⟫_ℂ =
      if m = n then (diskAntiholomorphicH1Weight m : ℂ) else 0 := by
  rw [h1_inner, hardy_value_antiholomorphicTest,
    hardy_value_antiholomorphicTest, inner_diskAntiholomorphicArea,
    hardy_gradient_antiholomorphicTest]
  by_cases hmn : m = n
  · simp [hmn, diskAntiholomorphicH1Weight]
  · simp [hmn]

private theorem hardy_sqrt_inverse_normalizes {w : ℝ} (hw : 0 < w) :
    conj ((Real.sqrt w : ℂ)⁻¹) *
      ((Real.sqrt w : ℂ)⁻¹ * (w : ℂ)) = 1 := by
  have hs  := (Real.sqrt_pos.mpr hw).ne'
  have hr : (Real.sqrt w)⁻¹ * ((Real.sqrt w)⁻¹ * w) = 1 := by
    grind
  simp
  exact_mod_cast hr

private theorem hardy_orthonormal_of_gram
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : ℕ → H) (w : ℕ → ℝ) (hw : ∀ m, 0 < w m)
    (hgram : ∀ m n, ⟪v m, v n⟫_ℂ =
      if m = n then (w m : ℂ) else 0) :
    Orthonormal ℂ (fun m => (Real.sqrt (w m) : ℂ)⁻¹ • v m) := by
  classical
  rw [orthonormal_iff_ite]
  intro m n
  by_cases hmn : m = n
  · subst n
    simp only [inner_smul_left, inner_smul_right, hgram, ite_true]
    calc
      _ = conj ((Real.sqrt (w m) : ℂ)⁻¹) *
          ((Real.sqrt (w m) : ℂ)⁻¹ * (w m)) := by ring
      _ = 1 := hardy_sqrt_inverse_normalizes (hw m)
  · simp [inner_smul_left, inner_smul_right, hgram, hmn]

/-- Unit vectors in actual disk H¹, with the constant mode retained. -/
def diskUnitAntiholomorphicH1Test (m : ℕ) : NeumannH1 unitDisk :=
  (Real.sqrt (diskAntiholomorphicH1Weight m) : ℂ)⁻¹ •
    diskAntiholomorphicH1Test m

theorem orthonormal_diskUnitAntiholomorphicH1Test :
    Orthonormal ℂ diskUnitAntiholomorphicH1Test :=
  hardy_orthonormal_of_gram diskAntiholomorphicH1Test
    diskAntiholomorphicH1Weight diskAntiholomorphicH1Weight_pos
    inner_diskAntiholomorphicH1Test

section

variable (m : ℕ)
include m

/-- The half-trace amplitude of an unscaled antiholomorphic monomial. -/
def diskHardyTraceScale : ℝ :=
  Real.sqrt (sobWeight (-(m : ℤ))) * Real.sqrt anglePeriod

theorem diskHardyTraceScale_pos : 0 < diskHardyTraceScale m := mul_pos (Real.sqrt_pos.mpr (sobWeight_pos _))
    ((by positivity))

theorem sobWeight_neg_nat :
    sobWeight (-(m : ℤ)) = ((m + 1 : ℕ) : ℝ) := by
  simp [sobWeight] <;> ring

theorem diskHardyTraceScale_sq :
    diskHardyTraceScale m ^ 2 = anglePeriod * ((m + 1 : ℕ) : ℝ) := by
  rw [diskHardyTraceScale, mul_pow, Real.sq_sqrt (sobWeight_pos _).le,
    Real.sq_sqrt (by positivity : 0 ≤ anglePeriod), sobWeight_neg_nat]
  ring

theorem diskAntiholomorphicH1Weight_le_traceScale_sq :
    diskAntiholomorphicH1Weight m ≤ diskHardyTraceScale m ^ 2 := by
  have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by simp
  have hdiv : π / ((m + 1 : ℕ) : ℝ) ≤ π := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  rw [diskAntiholomorphicH1Weight, diskHardyTraceScale_sq]
  push_cast at hm hdiv ⊢
  nlinarith [Real.pi_pos]

/-- The ratio between unit H¹ coordinates and normalized trace coordinates. -/
def diskHardySynthesisWeight : ℝ :=
  Real.sqrt (diskAntiholomorphicH1Weight m) / diskHardyTraceScale m

theorem diskHardySynthesisWeight_nonneg :
    0 ≤ diskHardySynthesisWeight m := div_nonneg (Real.sqrt_nonneg _) (diskHardyTraceScale_pos _).le

theorem diskHardySynthesisWeight_le_one :
    diskHardySynthesisWeight m ≤ 1 := by
  rw [diskHardySynthesisWeight, div_le_one (diskHardyTraceScale_pos m)]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (diskHardyTraceScale_pos m).le).mp
  rw [Real.sq_sqrt (diskAntiholomorphicH1Weight_pos m).le]
  exact diskAntiholomorphicH1Weight_le_traceScale_sq m

end

private theorem hardy_nat_memℓp_two_iff_summable {f : ℕ → ℂ} :
    Memℓp f 2 ↔ Summable (fun m => ‖f m‖ ^ 2) := by
  rw [memℓp_gen_iff (by norm_num)]
  simp

private theorem hardy_negative_index_injective :
    Function.Injective (fun m : ℕ => -(m : ℤ)) := by
  intro m n h
  exact_mod_cast neg_injective h

section

variable (w : ℕ → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1) (b x : L2Z)
    (hx : HasSum (fun m : ℕ => b (-(m : ℤ)) • stdBasisZ (-(m : ℤ))) x) (n : ℤ) (m : ℕ)

include hw in
theorem hardy_weighted_coefficients_memℓp :
    Memℓp (fun m => w m * b (-(m : ℤ))) 2 := by
  refine hardy_nat_memℓp_two_iff_summable.mpr ?_
  have hs : Summable (fun m : ℕ => ‖b (-(m : ℤ))‖ ^ 2) :=
    (summable_norm_sq_L2Z b).comp_injective hardy_negative_index_injective
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun m => ?_) hs
  rw [norm_mul, mul_pow]
  calc
    _ ≤ 1 ^ 2 * ‖b (-m)‖ ^ 2 := by gcongr; exact hw m
    _ = _ := by ring

include hw in
def hardyWeightedCoefficientsLin : L2Z →ₗ[ℂ] DiskHardyCoefficients where
  toFun b := ⟨fun m => w m * b (-(m : ℤ)), hardy_weighted_coefficients_memℓp w hw b⟩
  map_add' b c := by
    ext m
    simp [mul_add, Pi.add_apply]
    rfl
  map_smul' a b := by
    ext m
    simp [lp.coeFn_smul, smul_eq_mul] <;> ring

private theorem hardy_weighted_coefficients_norm_le :
    ‖hardyWeightedCoefficientsLin w hw b‖ ≤ ‖b‖ := by
  have hsq : ‖hardyWeightedCoefficientsLin w hw b‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    have hn : ‖hardyWeightedCoefficientsLin w hw b‖ ^ 2 =
        ∑' m : ℕ, ‖w m * b (-(m : ℤ))‖ ^ 2 := by
      have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
        (hardyWeightedCoefficientsLin w hw b)
      simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
      exact h
    rw [hn, norm_sq_L2Z]
    calc
      _ ≤ ∑' m : ℕ, ‖b (-m)‖ ^ 2 := by
        refine (hardy_nat_memℓp_two_iff_summable.mp
          (lp.memℓp (hardyWeightedCoefficientsLin w hw b))).tsum_le_tsum
          (fun m => ?_) ((summable_norm_sq_L2Z b).comp_injective
            hardy_negative_index_injective)
        
        rw [norm_mul, mul_pow]
        calc
          _ ≤ 1 ^ 2 * ‖b (-m)‖ ^ 2 := by gcongr; exact hw m
          _ = _ := by ring
      _ ≤ _ := tsum_comp_le_tsum_of_inj (summable_norm_sq_L2Z b)
        ((by norm_num)) hardy_negative_index_injective
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

include hw in
def hardyWeightedCoefficients : L2Z →L[ℂ] DiskHardyCoefficients :=
  (hardyWeightedCoefficientsLin w hw).mkContinuous 1
    (fun b => by simpa using hardy_weighted_coefficients_norm_le w hw b)

theorem hardy_synthesis_weight_bound :
    ‖(diskHardySynthesisWeight m : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_of_nonneg (diskHardySynthesisWeight_nonneg m)]
  exact diskHardySynthesisWeight_le_one m

/-- The actual square-summable coordinates used by H¹ orthogonal synthesis. -/
def diskHardyCoefficientMap : L2Z →L[ℂ] DiskHardyCoefficients :=
  hardyWeightedCoefficients (fun m => (diskHardySynthesisWeight m : ℂ))
    hardy_synthesis_weight_bound

theorem diskHardyCoefficientMap_apply :
    diskHardyCoefficientMap b m =
      (diskHardySynthesisWeight m : ℂ) * b (-(m : ℤ)) := rfl

def hardySynthesisIsometry :
    DiskHardyCoefficients →ₗᵢ[ℂ] NeumannH1 unitDisk :=
  orthonormal_diskUnitAntiholomorphicH1Test.orthogonalFamily.linearIsometry

/-- Harmonic extension of the nonpositive normalized Fourier data, into the
actual weak-gradient H¹ space on the disk. -/
def diskHardyExtension : L2Z →L[ℂ] NeumannH1 unitDisk :=
  hardySynthesisIsometry.toContinuousLinearMap.comp diskHardyCoefficientMap

private theorem hardy_raw_synthesis_scalar (a : ℂ) :
    ((diskHardySynthesisWeight m : ℂ) * a) *
        (Real.sqrt (diskAntiholomorphicH1Weight m) : ℂ)⁻¹ =
      a / (diskHardyTraceScale m : ℂ) := by
  have hs : (Real.sqrt (diskAntiholomorphicH1Weight m) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (diskAntiholomorphicH1Weight_pos m)).ne'
  rw [diskHardySynthesisWeight, Complex.ofReal_div, div_eq_mul_inv, div_eq_mul_inv]
  grind

/-- Convergence of smooth harmonic partial sums in genuine H¹. The ordinary
boundary coefficient is the normalized coefficient divided by
`sqrt(2π) * sqrt(λ)`, including frequency zero. -/
theorem diskHardyExtension_hasSum :
    HasSum (fun m : ℕ => (b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ)) •
      diskAntiholomorphicH1Test m) (diskHardyExtension b) := by
  have hs := orthonormal_diskUnitAntiholomorphicH1Test.orthogonalFamily.hasSum_linearIsometry
    (diskHardyCoefficientMap b)
  change HasSum (fun m =>
    (diskHardyCoefficientMap b m) • diskUnitAntiholomorphicH1Test m)
    (diskHardyExtension b) at hs
  convert hs using 1
  simp [diskHardyCoefficientMap_apply, diskUnitAntiholomorphicH1Test, smul_smul, hardy_raw_synthesis_scalar]

private theorem hardy_trace_term :
    diskHalfTrace ((b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ)) •
      diskAntiholomorphicH1Test m) =
        b (-(m : ℤ)) • stdBasisZ (-(m : ℤ)) := by
  have ht : (diskHardyTraceScale m : ℂ) ≠ 0 := by
    exact_mod_cast (diskHardyTraceScale_pos m).ne'
  rw [map_smul, diskHalfTrace_antiholomorphicTest, smul_smul]
  have hc : (Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) *
      fourierScale = (diskHardyTraceScale m : ℂ) := by
    simp [diskHardyTraceScale, Complex.ofReal_mul]
  rw [hc, div_mul_cancel₀ _ ht]

theorem diskHardyExtension_halfTrace_hasSum :
    HasSum (fun m : ℕ => b (-(m : ℤ)) • stdBasisZ (-(m : ℤ)))
      (diskHalfTrace (diskHardyExtension b)) := by
  simpa only [hardy_trace_term] using diskHalfTrace.hasSum (diskHardyExtension_hasSum b)

theorem hardy_inner_stdBasisZ (b : L2Z) :
    ⟪stdBasisZ n, b⟫_ℂ = b n := by
  simp [stdBasisZ_apply, lp.inner_single_left]

include hx in
private theorem hardy_nonpositive_series_coordinate : x n = if 0 < n then 0 else b n := by
  classical
  have hcoord := (innerSL ℂ (stdBasisZ n)).hasSum hx
  have hbasis (m : ℕ) :
      (innerSL ℂ (stdBasisZ n)) (b (-m) • stdBasisZ (-m)) =
        if n = -m then b (-m) else 0 := by
    simp only [innerSL_apply_apply, inner_smul_right,
      orthonormal_iff_ite.mp stdBasisZ.orthonormal]
    simp
  simp [hbasis, hardy_inner_stdBasisZ] at hcoord
  rw [← hcoord.tsum_eq]
  by_cases hn : 0 < n
  · simp [hn, ite_true]
    have hz : (fun m : ℕ => if n = -(m : ℤ) then b (-(m : ℤ)) else 0) =
        (fun _ : ℕ => (0 : ℂ)) := by
      funext m
      have hnm : n ≠ -(m : ℤ) := by omega
      simp [hnm]
    simp [hz]
  · simp [hn, ite_false]
    
    let k  := Int.toNat (-n)
    have hk : n = -(k : ℤ) := by
      omega
    simp [*]

/-- The extension has precisely the nonpositive normalized half trace. -/
theorem diskHalfTrace_diskHardyExtension_apply :
    diskHalfTrace (diskHardyExtension b) n = if 0 < n then 0 else b n :=
  hardy_nonpositive_series_coordinate b _ (diskHardyExtension_halfTrace_hasSum b) n

theorem diskHalfTrace_diskHardyExtension :
    diskHalfTrace (diskHardyExtension b) = (1 - posProj) b := by
  ext n
  rw [diskHalfTrace_diskHardyExtension_apply]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    lp.coeFn_sub, Pi.sub_apply, posProj, diagOp_apply]
  split_ifs <;> simp

/-- A bounded genuine H¹ right inverse on the nonpositive Fourier subspace. -/
theorem diskHalfTrace_diskHardyExtension_eq_of_nonpositive
    (hb : ∀ n : ℤ, 0 < n → b n = 0) :
    diskHalfTrace (diskHardyExtension b) = b := by
  ext n
  rw [diskHalfTrace_diskHardyExtension_apply]
  grind

private theorem hardy_antiholomorphic_gradient_components :
    diskAntiholomorphicGradient m 0 =
      Complex.I • diskAntiholomorphicGradient m 1 := by
  apply Lp.ext
  filter_upwards [diskAntiholomorphicGradient_ae m 0,
    diskAntiholomorphicGradient_ae m 1,
    Lp.coeFn_smul Complex.I (diskAntiholomorphicGradient m 1)] with z hx hy hsmul
  rw [hx, hsmul]
  change dirD (diskAntiholomorphicMode m) (coordDir 0) z =
    Complex.I * ((diskAntiholomorphicGradient m 1 : ℂ → ℂ) z)
  rw [hy]
  simp only [dirD_diskAntiholomorphicMode,
    show coordDir 0 = (1 : ℂ) from rfl,
    show coordDir 1 = Complex.I from rfl,
    map_one, Complex.conj_I, mul_one]
  ring_nf
  simp

theorem hardy_gradient_component_antiholomorphicTest (i : Fin 2) :
    h1Gradient unitDisk i (diskAntiholomorphicH1Test m) =
      diskAntiholomorphicGradient m i := rfl

theorem diskAntiholomorphicH1Test_cauchyRiemann :
    h1Gradient unitDisk 0 (diskAntiholomorphicH1Test m) =
      Complex.I • h1Gradient unitDisk 1 (diskAntiholomorphicH1Test m) := hardy_antiholomorphic_gradient_components m

/-- The weak antiholomorphic derivative, without an inessential scalar factor. -/
def diskAntiholomorphicDefect :
    NeumannH1 unitDisk →L[ℂ] L2 unitDisk :=
  h1Gradient unitDisk 0 -
    Complex.I • h1Gradient unitDisk 1

private theorem hardy_antiholomorphic_defect_test :
    diskAntiholomorphicDefect (diskAntiholomorphicH1Test m) = 0 := by
  simp [diskAntiholomorphicDefect, diskAntiholomorphicH1Test_cauchyRiemann, sub_self]

theorem diskAntiholomorphicDefect_diskHardyExtension :
    diskAntiholomorphicDefect (diskHardyExtension b) = 0 := by
  have hs := diskAntiholomorphicDefect.hasSum (diskHardyExtension_hasSum b)
  have hs0 : HasSum (fun _ : ℕ => (0 : L2 unitDisk))
      (diskAntiholomorphicDefect (diskHardyExtension b)) := by
    simpa only [map_smul, hardy_antiholomorphic_defect_test, smul_zero] using hs
  exact hs0.unique hasSum_zero

/-- The completed H¹ vector is genuinely weakly antiholomorphic. -/
theorem diskHardyExtension_cauchyRiemann :
    h1Gradient unitDisk 0 (diskHardyExtension b) =
      Complex.I • h1Gradient unitDisk 1 (diskHardyExtension b) := by
  apply sub_eq_zero.mp
  exact diskAntiholomorphicDefect_diskHardyExtension b

end

end PolyaNeumann
