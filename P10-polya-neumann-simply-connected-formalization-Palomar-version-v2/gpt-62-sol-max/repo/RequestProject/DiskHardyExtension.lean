module

public import RequestProject.DiskWeakModes
public import RequestProject.DiskAreaBessel
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

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
def diskAntiholomorphicH1Weight  : ℝ :=
  π / ((m + 1 : ℕ) : ℝ) + 2 * π * (m : ℝ)

theorem diskAntiholomorphicH1Weight_pos  :
    0 < diskAntiholomorphicH1Weight m := by
  unfold diskAntiholomorphicH1Weight
  positivity

private theorem hardy_value_antiholomorphicTest  :
    h1Value (ball (0 : ℂ) 1) (diskAntiholomorphicH1Test m) =
      diskAntiholomorphicArea m :=
  h1Value_smoothTraceH1 (ball (0 : ℂ) 1)
    ⟨diskHarmonicCutoff (diskAntiholomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)⟩

end

private theorem hardy_gradient_antiholomorphicTest (m n : ℕ) :
    (∑ i : Fin 2,
      ⟪h1Gradient (ball (0 : ℂ) 1) i (diskAntiholomorphicH1Test m),
        h1Gradient (ball (0 : ℂ) 1) i (diskAntiholomorphicH1Test n)⟫_ℂ) =
      if m = n then (2 * π : ℂ) * (m : ℂ) else 0 := inner_diskAntiholomorphicGradient m n

/-- The true H¹ Gram matrix; the zero mode has weight `π`. -/
theorem inner_diskAntiholomorphicH1Test (m n : ℕ) :
    ⟪diskAntiholomorphicH1Test m, diskAntiholomorphicH1Test n⟫_ℂ =
      if m = n then (diskAntiholomorphicH1Weight m : ℂ) else 0 := by
  rw [h1_inner, hardy_value_antiholomorphicTest,
    hardy_value_antiholomorphicTest, inner_diskAntiholomorphicArea,
    hardy_gradient_antiholomorphicTest]
  by_cases hmn : m = n
  simp [hmn, diskAntiholomorphicH1Weight]
  simp_all

private theorem hardy_sqrt_inverse_normalizes {w : ℝ} (hw : 0 < w) :
    conj ((Real.sqrt w : ℂ)⁻¹) *
      ((Real.sqrt w : ℂ)⁻¹ * (w : ℂ)) = 1 := by
  have hs := (Real.sqrt_pos.mpr hw).ne'
  have hr : (Real.sqrt w)⁻¹ * ((Real.sqrt w)⁻¹ * w) = 1 := by
    grind
  simp  
  norm_cast

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
          ((Real.sqrt (w m) : ℂ)⁻¹ * (w m : ℂ)) := by ring
      _ = 1 := hardy_sqrt_inverse_normalizes (hw m)
  simp [inner_smul_left, inner_smul_right, hgram, hmn]

/-- Unit vectors in actual disk H¹, with the constant mode retained. -/
def diskUnitAntiholomorphicH1Test (m : ℕ) : NeumannH1 (ball (0 : ℂ) 1) :=
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
def diskHardyTraceScale  : ℝ :=
  Real.sqrt (sobWeight (-(m : ℤ))) * Real.sqrt (2 * π)

theorem diskHardyTraceScale_pos  : 0 < diskHardyTraceScale m := by
  exact mul_pos (Real.sqrt_pos.mpr (sobWeight_pos _))
    (Real.sqrt_pos.mpr (by positivity))

theorem diskHardyTraceScale_sq  :
    diskHardyTraceScale m ^ 2 = 2 * π * ((m + 1 : ℕ) : ℝ) := by
  rw [diskHardyTraceScale, mul_pow, Real.sq_sqrt (sobWeight_pos _).le,
    Real.sq_sqrt (by positivity : 0 ≤ 2 * π), sobWeight_neg_nat]
  ring

theorem diskAntiholomorphicH1Weight_le_traceScale_sq  :
    diskAntiholomorphicH1Weight m ≤ diskHardyTraceScale m ^ 2 := by
  have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by simp
  have hdiv : π / ((m + 1 : ℕ) : ℝ) ≤ π := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  rw [diskAntiholomorphicH1Weight, diskHardyTraceScale_sq]
  push_cast at hm hdiv ⊢
  nlinarith [Real.pi_pos]

/-- The ratio between unit H¹ coordinates and normalized trace coordinates. -/
def diskHardySynthesisWeight  : ℝ :=
  Real.sqrt (diskAntiholomorphicH1Weight m) / diskHardyTraceScale m

theorem diskHardySynthesisWeight_nonneg  :
    0 ≤ diskHardySynthesisWeight m := div_nonneg (Real.sqrt_nonneg _) (diskHardyTraceScale_pos _).le

theorem diskHardySynthesisWeight_le_one  :
    diskHardySynthesisWeight m ≤ 1 := by
  rw [diskHardySynthesisWeight, div_le_one (diskHardyTraceScale_pos m)]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (diskHardyTraceScale_pos m).le).mp
  rw [Real.sq_sqrt (diskAntiholomorphicH1Weight_pos m).le]
  exact diskAntiholomorphicH1Weight_le_traceScale_sq m

end

private theorem hardy_nat_memℓp_two_iff_summable {f : ℕ → ℂ} :
    Memℓp f 2 ↔ Summable (fun m => ‖f m‖ ^ 2) := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp

private theorem hardy_negative_index_injective :
    Function.Injective (fun m : ℕ => -(m : ℤ)) := by
  intro m n h
  simp_all

section

variable (w : ℕ → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1)
include w hw

theorem hardy_weighted_coefficients_memℓp
     (b : L2Z) :
    Memℓp (fun m => w m * b (-(m : ℤ))) 2 := by
  refine hardy_nat_memℓp_two_iff_summable.mpr ?_
  have hs : Summable (fun m : ℕ => ‖b (-(m : ℤ))‖ ^ 2) :=
    (summable_norm_sq_L2Z b).comp_injective hardy_negative_index_injective
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun m => ?_) hs
  rw [norm_mul, mul_pow]
  calc
    _ ≤ 1 ^ 2 * ‖b (-(m : ℤ))‖ ^ 2 := by gcongr; tauto
    _ = _ := by ring

def hardyWeightedCoefficientsLin
     : L2Z →ₗ[ℂ] DiskHardyCoefficients where
  toFun b := ⟨fun m => w m * b (-(m : ℤ)), hardy_weighted_coefficients_memℓp w hw b⟩
  map_add' b c := by
    ext m
    simp [mul_add]
    rfl
  map_smul' a b := by
    ext m
    simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    ring

private theorem hardy_weighted_coefficients_norm_le
     (b : L2Z) :
    ‖hardyWeightedCoefficientsLin w hw b‖ ≤ ‖b‖ := by
  have hsq : ‖hardyWeightedCoefficientsLin w hw b‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    have hn : ‖hardyWeightedCoefficientsLin w hw b‖ ^ 2 =
        ∑' m : ℕ, ‖w m * b (-(m : ℤ))‖ ^ 2 := by
      have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
        (hardyWeightedCoefficientsLin w hw b)
      simp  [ENNReal.toReal_ofNat, Real.rpow_two] at h
      assumption
    rw [hn, norm_sq_L2Z]
    calc
      _ ≤ ∑' m : ℕ, ‖b (-(m : ℤ))‖ ^ 2 := by
        refine (hardy_nat_memℓp_two_iff_summable.mp
          (lp.memℓp (hardyWeightedCoefficientsLin w hw b))).tsum_le_tsum
          (fun m => ?_) ((summable_norm_sq_L2Z b).comp_injective
            hardy_negative_index_injective)
        change ‖w m * b (-(m : ℤ))‖ ^ 2 ≤ _
        rw [norm_mul, mul_pow]
        calc
          _ ≤ 1 ^ 2 * ‖b (-(m : ℤ))‖ ^ 2 := by gcongr; tauto
          _ = _ := by ring
      _ ≤ _ := tsum_comp_le_tsum_of_inj (summable_norm_sq_L2Z b)
        (fun n => sq_nonneg ‖b n‖) hardy_negative_index_injective
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

def hardyWeightedCoefficients
     : L2Z →L[ℂ] DiskHardyCoefficients :=
  (hardyWeightedCoefficientsLin w hw).mkContinuous 1
    (fun b => by simpa using hardy_weighted_coefficients_norm_le w hw b)

end

theorem hardy_synthesis_weight_bound (m : ℕ) :
    ‖(diskHardySynthesisWeight m : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_of_nonneg (diskHardySynthesisWeight_nonneg m)]
  exact diskHardySynthesisWeight_le_one m

/-- The actual square-summable coordinates used by H¹ orthogonal synthesis. -/
def diskHardyCoefficientMap : L2Z →L[ℂ] DiskHardyCoefficients :=
  hardyWeightedCoefficients (fun m => (diskHardySynthesisWeight m : ℂ))
    hardy_synthesis_weight_bound

theorem diskHardyCoefficientMap_apply (b : L2Z) (m : ℕ) :
    diskHardyCoefficientMap b m =
      (diskHardySynthesisWeight m : ℂ) * b (-(m : ℤ)) := rfl

def hardySynthesisIsometry :
    DiskHardyCoefficients →ₗᵢ[ℂ] NeumannH1 (ball (0 : ℂ) 1) :=
  orthonormal_diskUnitAntiholomorphicH1Test.orthogonalFamily.linearIsometry

/-- Harmonic extension of the nonpositive normalized Fourier data, into the
actual weak-gradient H¹ space on the disk. -/
def diskHardyExtension : L2Z →L[ℂ] NeumannH1 (ball (0 : ℂ) 1) :=
  hardySynthesisIsometry.toContinuousLinearMap.comp diskHardyCoefficientMap

private theorem hardy_raw_synthesis_scalar (m : ℕ) (a : ℂ) :
    ((diskHardySynthesisWeight m : ℂ) * a) *
        (Real.sqrt (diskAntiholomorphicH1Weight m) : ℂ)⁻¹ =
      a / (diskHardyTraceScale m : ℂ) := by
  have hs : (Real.sqrt (diskAntiholomorphicH1Weight m) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (diskAntiholomorphicH1Weight_pos m)).ne'
  grind [diskHardySynthesisWeight, Complex.ofReal_div, div_eq_mul_inv, one_mul]

section

variable (b : L2Z)
include b

/-- Convergence of smooth harmonic partial sums in genuine H¹. The ordinary
boundary coefficient is the normalized coefficient divided by
`sqrt(2π) * sqrt(λ)`, including frequency zero. -/
theorem diskHardyExtension_hasSum  :
    HasSum (fun m : ℕ => (b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ)) •
      diskAntiholomorphicH1Test m) (diskHardyExtension b) := by
  have hs := (orthonormal_diskUnitAntiholomorphicH1Test.orthogonalFamily).hasSum_linearIsometry
    (diskHardyCoefficientMap b)
  change HasSum (fun m =>
    (diskHardyCoefficientMap b m) • diskUnitAntiholomorphicH1Test m)
    (diskHardyExtension b) at hs
  convert hs using 1
  funext m
  rw [diskHardyCoefficientMap_apply, diskUnitAntiholomorphicH1Test, smul_smul,
    hardy_raw_synthesis_scalar]

private theorem hardy_trace_term  (m : ℕ) :
    diskHalfTrace ((b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ)) •
      diskAntiholomorphicH1Test m) =
        b (-(m : ℤ)) • stdBasisZ (-(m : ℤ)) := by
  have ht : (diskHardyTraceScale m : ℂ) ≠ 0 := by
    exact_mod_cast (diskHardyTraceScale_pos m).ne'
  rw [map_smul, diskHalfTrace_antiholomorphicTest, smul_smul]
  have hc : (Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) *
      (Real.sqrt (2 * π) : ℂ) = (diskHardyTraceScale m : ℂ) := by
    norm_cast
  simp_all

theorem diskHardyExtension_halfTrace_hasSum  :
    HasSum (fun m : ℕ => b (-(m : ℤ)) • stdBasisZ (-(m : ℤ)))
      (diskHalfTrace (diskHardyExtension b)) := by
  simpa only [hardy_trace_term] using diskHalfTrace.hasSum (diskHardyExtension_hasSum b)

end

private theorem hardy_nonpositive_series_coordinate
    (b x : L2Z)
    (hx : HasSum (fun m : ℕ => b (-(m : ℤ)) • stdBasisZ (-(m : ℤ))) x)
    (n : ℤ) : x n = if 0 < n then 0 else b n := by
  classical
  have hcoord := (innerSL ℂ (stdBasisZ n)).hasSum hx
  have hbasis (m : ℕ) :
      (innerSL ℂ (stdBasisZ n)) (b (-(m : ℤ)) • stdBasisZ (-(m : ℤ))) =
        if n = -(m : ℤ) then b (-(m : ℤ)) else 0 := by
    simp only [innerSL_apply_apply, inner_smul_right,
      orthonormal_iff_ite.mp stdBasisZ.orthonormal]
    simp
  simp  [hbasis, innerSL_apply_apply, inner_stdBasisZ] at hcoord
  rw [← hcoord.tsum_eq]
  by_cases hn : 0 < n
  · simp  [hn]
    have hz : (fun m : ℕ => if n = -(m : ℤ) then b (-(m : ℤ)) else 0) =
        (fun _ : ℕ => (0 : ℂ)) := by
      funext m
      have hnm : n ≠ -(m : ℤ) := by omega
      simp_all
    rw [hz]
    simp
  · simp  [hn]
    have hn0 : 0 ≤ -n := by omega
    let k := Int.toNat (-n)
    have hk : n = -(k : ℤ) := by
      omega
    rw [tsum_eq_single k]
    · simp [← hk]
    · intro m hm
      have hnm : n ≠ -(m : ℤ) := by omega
      simp_all

section

variable (b : L2Z)
include b

/-- The extension has precisely the nonpositive normalized half trace. -/
theorem diskHalfTrace_diskHardyExtension_apply  (n : ℤ) :
    diskHalfTrace (diskHardyExtension b) n = if 0 < n then 0 else b n :=
  hardy_nonpositive_series_coordinate b _ (diskHardyExtension_halfTrace_hasSum b) n

theorem diskHalfTrace_diskHardyExtension  :
    diskHalfTrace (diskHardyExtension b) = (1 - posProj) b := by
  ext n
  rw [diskHalfTrace_diskHardyExtension_apply]
  simp only [ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply, posProj, diagOp_apply]
  grind

/-- A bounded genuine H¹ right inverse on the nonpositive Fourier subspace. -/
theorem diskHalfTrace_diskHardyExtension_eq_of_nonpositive 
    (hb : ∀ n : ℤ, 0 < n → b n = 0) :
    diskHalfTrace (diskHardyExtension b) = b := by
  ext n
  rw [diskHalfTrace_diskHardyExtension_apply]
  simp_all

end

section

variable (m : ℕ)
include m

private theorem hardy_antiholomorphic_gradient_components  :
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


theorem diskAntiholomorphicH1Test_cauchyRiemann  :
    h1Gradient (ball (0 : ℂ) 1) 0 (diskAntiholomorphicH1Test m) =
      Complex.I • h1Gradient (ball (0 : ℂ) 1) 1 (diskAntiholomorphicH1Test m) := hardy_antiholomorphic_gradient_components m

end

/-- The weak antiholomorphic derivative, without an inessential scalar factor. -/
def diskAntiholomorphicDefect :
    NeumannH1 (ball (0 : ℂ) 1) →L[ℂ] L2 (ball (0 : ℂ) 1) :=
  h1Gradient (ball (0 : ℂ) 1) 0 -
    Complex.I • h1Gradient (ball (0 : ℂ) 1) 1

private theorem hardy_antiholomorphic_defect_test (m : ℕ) :
    diskAntiholomorphicDefect (diskAntiholomorphicH1Test m) = 0 := by simp [diskAntiholomorphicDefect, diskAntiholomorphicH1Test_cauchyRiemann]

theorem diskAntiholomorphicDefect_diskHardyExtension (b : L2Z) :
    diskAntiholomorphicDefect (diskHardyExtension b) = 0 := by
  have hs := diskAntiholomorphicDefect.hasSum (diskHardyExtension_hasSum b)
  have hs0 : HasSum (fun _ : ℕ => (0 : L2 (ball (0 : ℂ) 1)))
      (diskAntiholomorphicDefect (diskHardyExtension b)) := by
    simpa only [map_smul, hardy_antiholomorphic_defect_test, smul_zero] using hs
  exact hs0.unique hasSum_zero

/-- The completed H¹ vector is genuinely weakly antiholomorphic. -/
theorem diskHardyExtension_cauchyRiemann (b : L2Z) :
    h1Gradient (ball (0 : ℂ) 1) 0 (diskHardyExtension b) =
      Complex.I • h1Gradient (ball (0 : ℂ) 1) 1 (diskHardyExtension b) := by
  apply sub_eq_zero.mp
  exact diskAntiholomorphicDefect_diskHardyExtension b

end PolyaNeumann
