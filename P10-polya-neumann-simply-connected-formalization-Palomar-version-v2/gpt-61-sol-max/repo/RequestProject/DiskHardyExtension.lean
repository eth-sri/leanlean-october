module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real Filter
open scoped ComplexConjugate InnerProductSpace ENNReal

abbrev DiskHardyCoefficients := lp (fun _ : ℕ => ℂ) 2

/-- The full physical H¹ mass of the mode `conj(z)^m`. -/
def diskAntiholomorphicH1Weight m  :=
  π / ((m + 1 : ℕ) : ℝ) + 2 * π * (m : ℝ)

section
variable (m : ℕ)

include m in
theorem diskAntiholomorphicH1Weight_pos :
    0 < diskAntiholomorphicH1Weight m := by
  unfold diskAntiholomorphicH1Weight
  positivity

include m in
theorem h1Value_diskAntiholomorphicH1Test :
    h1Value unitDisk (diskAntiholomorphicH1Test m) =
      diskAntiholomorphicArea m :=
  h1Value_smoothTraceH1 unitDisk
    ⟨diskHarmonicCutoff (diskAntiholomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)⟩

private theorem hardy_gradient_antiholomorphicTest m n :
    (∑ i : Coord,
      ⟪h1Gradient unitDisk i (diskAntiholomorphicH1Test m),
        h1Gradient unitDisk i (diskAntiholomorphicH1Test n)⟫_ℂ) =
      if m = n then (2 * π : ℂ) * (m : ℂ) else 0 := by
  have h := inner_diskAntiholomorphicGradient m n
  assumption

/-- The true H¹ Gram matrix; the zero mode has weight `π`. -/
theorem inner_diskAntiholomorphicH1Test m n :
    ⟪diskAntiholomorphicH1Test m, diskAntiholomorphicH1Test n⟫_ℂ =
      if m = n then (diskAntiholomorphicH1Weight m : ℂ) else 0 := by
  rw [h1_inner, h1Value_diskAntiholomorphicH1Test,
    h1Value_diskAntiholomorphicH1Test, inner_diskAntiholomorphicArea,
    hardy_gradient_antiholomorphicTest]
  by_cases hmn : m = n
  · simp_all [diskAntiholomorphicH1Weight]
  · simp [hmn]

private theorem hardy_sqrt_inverse_normalizes  (hw : 0 < w) :
    conj ((Real.sqrt w : ℂ)⁻¹) *
      ((Real.sqrt w : ℂ)⁻¹ * (w : ℂ)) = 1 := by
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
  · simp only [inner_smul_left, inner_smul_right]
    grind only [hardy_sqrt_inverse_normalizes]
  · simp [inner_smul_left, inner_smul_right, hgram, hmn]

/-- Unit vectors in actual disk H¹, with the constant mode retained. -/
def diskUnitAntiholomorphicH1Test m  :=
  (Real.sqrt (diskAntiholomorphicH1Weight m) : ℂ)⁻¹ •
    diskAntiholomorphicH1Test m

theorem orthonormal_diskUnitAntiholomorphicH1Test :
    Orthonormal ℂ diskUnitAntiholomorphicH1Test :=
  hardy_orthonormal_of_gram diskAntiholomorphicH1Test
    diskAntiholomorphicH1Weight diskAntiholomorphicH1Weight_pos
    inner_diskAntiholomorphicH1Test

/-- The half-trace amplitude of an unscaled antiholomorphic monomial. -/
def diskHardyTraceScale (m : ℕ)  :=
  Real.sqrt (sobWeight (-(m : ℤ))) * Real.sqrt circlePeriod

section
include m

theorem diskHardyTraceScale_pos : 0 < diskHardyTraceScale m := mul_pos (Real.sqrt_pos.mpr (sobWeight_pos _))
    (Real.sqrt_pos.mpr (by positivity))

theorem common_hardy_sobWeight_neg_nat :
    sobWeight (-(m : ℤ)) = ((m + 1 : ℕ) : ℝ) := by
  simp_all [PolyaNeumann.sobWeight] <;> bound

theorem diskHardyTraceScale_sq :
    diskHardyTraceScale m ^ 2 = 2 * π * ((m + 1 : ℕ) : ℝ) := by
  rw [diskHardyTraceScale, mul_pow, Real.sq_sqrt (sobWeight_pos _).le,
    Real.sq_sqrt (by positivity), common_hardy_sobWeight_neg_nat]
  ring

theorem diskAntiholomorphicH1Weight_le_traceScale_sq :
    diskAntiholomorphicH1Weight m ≤ diskHardyTraceScale m ^ 2 := by
  have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by norm_num
  have hdiv : π / ((m + 1 : ℕ) : ℝ) ≤ π := by
    bound
  grind [diskAntiholomorphicH1Weight, diskHardyTraceScale_sq, PolyaNeumann.diskAntiholomorphicH1Weight, PolyaNeumann.diskHardyTraceScale]

end


/-- The ratio between unit H¹ coordinates and normalized trace coordinates. -/
def diskHardySynthesisWeight m  :=
  Real.sqrt (diskAntiholomorphicH1Weight m) / diskHardyTraceScale m

include m in
theorem diskHardySynthesisWeight_nonneg :
    0 ≤ diskHardySynthesisWeight m := by
  exact div_nonneg (Real.sqrt_nonneg _) (diskHardyTraceScale_pos _).le

include m in
theorem diskHardySynthesisWeight_le_one :
    diskHardySynthesisWeight m ≤ 1 := by
  rw [diskHardySynthesisWeight, div_le_one (diskHardyTraceScale_pos m)]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (diskHardyTraceScale_pos m).le).mp
  grind [diskAntiholomorphicH1Weight_pos, diskAntiholomorphicH1Weight_le_traceScale_sq, PolyaNeumann.diskAntiholomorphicH1Weight, PolyaNeumann.diskHardyTraceScale]

private theorem hardy_nat_memℓp_two_iff_summable {f : ComplexSeq} :
    Memℓp f 2 ↔ Summable (fun m => ‖f m‖ ^ 2) := by
  rw [memℓp_gen_iff (by norm_num)]
  simp

private theorem hardy_negative_index_injective :
    Function.Injective (fun m : ℕ => -(m : ℤ)) := by
  simp_all [Function.Injective]

section
variable (w : ComplexSeq) (hw : ∀ m, ‖w m‖ ≤ 1) (b : L2Z)

include w hw b in
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

def hardyWeightedCoefficientsLin
    (w : ComplexSeq) (hw : ∀ m, ‖w m‖ ≤ 1) : L2Z →ₗ[ℂ] DiskHardyCoefficients where
  toFun b := ⟨fun m => w m * b (-(m : ℤ)), hardy_weighted_coefficients_memℓp w hw b⟩
  map_add' b c := by
    simp [mul_add]
    rfl
  map_smul' a b := by
    ext <;> simp_all <;> ring

include w hw b in
private theorem hardy_weighted_coefficients_norm_le :
    ‖hardyWeightedCoefficientsLin w hw b‖ ≤ ‖b‖ := by
  have hsq : ‖hardyWeightedCoefficientsLin w hw b‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    have hn : ‖hardyWeightedCoefficientsLin w hw b‖ ^ 2 =
        ∑' m : ℕ, ‖w m * b (-(m : ℤ))‖ ^ 2 := by
      have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
        (hardyWeightedCoefficientsLin w hw b)
      assumption_mod_cast
    rw [hn, norm_sq_L2Z]
    calc
      _ ≤ ∑' m : ℕ, ‖b (-m)‖ ^ 2 := by
        refine (hardy_nat_memℓp_two_iff_summable.mp
          (lp.memℓp (hardyWeightedCoefficientsLin w hw b))).tsum_le_tsum
          (fun m => ?_) ((summable_norm_sq_L2Z b).comp_injective
            hardy_negative_index_injective)
        change ‖w m * b (-m)‖ ^ 2 ≤ _
        rw [norm_mul, mul_pow]
        calc
          _ ≤ 1 ^ 2 * ‖b (-m)‖ ^ 2 := by gcongr; exact hw m
          _ = _ := by ring
      _ ≤ _ := tsum_comp_le_tsum_of_inj (summable_norm_sq_L2Z b)
        (fun n => sq_nonneg ‖b n‖) hardy_negative_index_injective
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

end


def hardyWeightedCoefficients
    (w : ComplexSeq) (hw : ∀ m, ‖w m‖ ≤ 1) : L2Z →L[ℂ] DiskHardyCoefficients :=
  (hardyWeightedCoefficientsLin w hw).mkContinuous 1
    (fun b => by simpa using hardy_weighted_coefficients_norm_le w hw b)

include m in
theorem hardy_synthesis_weight_bound :
    ‖(diskHardySynthesisWeight m : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_of_nonneg (diskHardySynthesisWeight_nonneg m)]
  exact diskHardySynthesisWeight_le_one m

/-- The actual square-summable coordinates used by H¹ orthogonal synthesis. -/
def diskHardyCoefficientMap : L2Z →L[ℂ] DiskHardyCoefficients :=
  hardyWeightedCoefficients (fun m => (diskHardySynthesisWeight m : ℂ))
    hardy_synthesis_weight_bound

theorem diskHardyCoefficientMap_apply b m :
    diskHardyCoefficientMap b m =
      (diskHardySynthesisWeight m : ℂ) * b (-(m : ℤ)) := rfl

def hardySynthesisIsometry :
    DiskHardyCoefficients →ₗᵢ[ℂ] NeumannH1 unitDisk :=
  orthonormal_diskUnitAntiholomorphicH1Test.orthogonalFamily.linearIsometry

/-- Harmonic extension of the nonpositive normalized Fourier data, into the
actual weak-gradient H¹ space on the disk. -/
def diskHardyExtension : L2Z →L[ℂ] NeumannH1 unitDisk :=
  hardySynthesisIsometry.toContinuousLinearMap.comp diskHardyCoefficientMap

include m in
private theorem hardy_raw_synthesis_scalar a :
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
theorem diskHardyExtension_hasSum (b : L2Z) :
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

private theorem hardy_trace_term (b : L2Z) (m : ℕ) :
    diskHalfTrace ((b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ)) •
      diskAntiholomorphicH1Test m) =
        b (-(m : ℤ)) • stdBasisZ (-(m : ℤ)) := by
  have ht : (diskHardyTraceScale m : ℂ) ≠ 0 := by
    exact_mod_cast (diskHardyTraceScale_pos m).ne'
  rw [map_smul, diskHalfTrace_antiholomorphicTest, smul_smul]
  have hc : (Real.sqrt (sobWeight (-(m : ℤ))) : ℂ) *
      (Real.sqrt circlePeriod : ℂ) = (diskHardyTraceScale m : ℂ) := by
    simp  [diskHardyTraceScale]
  rw [hc, div_mul_cancel₀ _ ht]

theorem diskHardyExtension_halfTrace_hasSum (b : L2Z) :
    HasSum (fun m : ℕ => b (-(m : ℤ)) • stdBasisZ (-(m : ℤ)))
      (diskHalfTrace (diskHardyExtension b)) := by
  simpa only [hardy_trace_term] using diskHalfTrace.hasSum (diskHardyExtension_hasSum b)

theorem common_hardy_inner_stdBasisZ n b :
    ⟪stdBasisZ n, b⟫_ℂ = b n := by
  rw [stdBasisZ_apply, lp.inner_single_left]
  simp

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
    split_ifs <;> simp
  simp  [hbasis, common_hardy_inner_stdBasisZ] at hcoord
  rw [← hcoord.tsum_eq]
  by_cases hn : 0 < n
  · simp  [hn]
    have hz : (fun m : ℕ => if n = -(m : ℤ) then b (-(m : ℤ)) else 0) =
        (fun _ : ℕ => (0 : ℂ)) := by
      funext m
      have hnm : n ≠ -(m : ℤ) := by omega
      simp [hnm]
    rw [hz]
    simp
  · simp only [hn, ite_false]
    have hn0 : 0 ≤ -n := by omega
    let k  := Int.toNat (-n)
    have hk : n = -(k : ℤ) := by
      omega
    rw [tsum_eq_single k]
    · simp [← hk]
    · intro m hm
      have hnm : n ≠ -(m : ℤ) := by omega
      simp [hnm]

/-- The extension has precisely the nonpositive normalized half trace. -/
theorem diskHalfTrace_diskHardyExtension_apply b n :
    diskHalfTrace (diskHardyExtension b) n = if 0 < n then 0 else b n :=
  hardy_nonpositive_series_coordinate b _ (diskHardyExtension_halfTrace_hasSum b) n

theorem diskHalfTrace_diskHardyExtension b :
    diskHalfTrace (diskHardyExtension b) = (1 - posProj) b := by
  ext n
  rw [diskHalfTrace_diskHardyExtension_apply]
  simp  [posProj]
  split_ifs <;> simp

/-- A bounded genuine H¹ right inverse on the nonpositive Fourier subspace. -/
theorem diskHalfTrace_diskHardyExtension_eq_of_nonpositive b
    (hb : ∀ n : ℤ, 0 < n → b n = 0) :
    diskHalfTrace (diskHardyExtension b) = b := by
  ext n
  rw [diskHalfTrace_diskHardyExtension_apply]
  simp_all

section
include m

private theorem hardy_antiholomorphic_gradient_components :
    diskAntiholomorphicGradient m 0 =
      Complex.I • diskAntiholomorphicGradient m 1 := by
  apply Lp.ext
  filter_upwards [diskAntiholomorphicGradient_ae m 0,
    diskAntiholomorphicGradient_ae m 1,
    Lp.coeFn_smul Complex.I (diskAntiholomorphicGradient m 1)] with z hx hy hsmul
  rw [hx, hsmul]
  change dirD (diskAntiholomorphicMode m) (coordDir 0) z =
    Complex.I * ((diskAntiholomorphicGradient m 1) z)
  rw [hy]
  simp  [dirD_diskAntiholomorphicMode, show coordDir 0 = (1 : ℂ) from rfl, show coordDir 1 = Complex.I from rfl]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem common_hardy_gradient_component_antiholomorphicTest i :
    h1Gradient unitDisk i (diskAntiholomorphicH1Test m) =
      diskAntiholomorphicGradient m i := rfl

theorem diskAntiholomorphicH1Test_cauchyRiemann :
    h1Gradient unitDisk 0 (diskAntiholomorphicH1Test m) =
      Complex.I • h1Gradient unitDisk 1 (diskAntiholomorphicH1Test m) := by
  simp_all [common_hardy_gradient_component_antiholomorphicTest, hardy_antiholomorphic_gradient_components]

end


/-- The weak antiholomorphic derivative, without an inessential scalar factor. -/
def diskAntiholomorphicDefect :
    NeumannH1 unitDisk →L[ℂ] L2 unitDisk :=
  h1Gradient unitDisk 0 -
    Complex.I • h1Gradient unitDisk 1

include m in
private theorem hardy_antiholomorphic_defect_test :
    diskAntiholomorphicDefect (diskAntiholomorphicH1Test m) = 0 := by
  simp_all [diskAntiholomorphicDefect, diskAntiholomorphicH1Test_cauchyRiemann]

end


theorem diskAntiholomorphicDefect_diskHardyExtension b :
    diskAntiholomorphicDefect (diskHardyExtension b) = 0 := by
  have hs := diskAntiholomorphicDefect.hasSum (diskHardyExtension_hasSum b)
  have hs0 : HasSum (fun _ : ℕ => (0 : L2 unitDisk))
      (diskAntiholomorphicDefect (diskHardyExtension b)) := by
    simp_all [hardy_antiholomorphic_defect_test]
  exact hs0.unique hasSum_zero

/-- The completed H¹ vector is genuinely weakly antiholomorphic. -/
theorem diskHardyExtension_cauchyRiemann b :
    h1Gradient unitDisk 0 (diskHardyExtension b) =
      Complex.I • h1Gradient unitDisk 1 (diskHardyExtension b) := by
  apply sub_eq_zero.mp
  exact diskAntiholomorphicDefect_diskHardyExtension b

end PolyaNeumann
