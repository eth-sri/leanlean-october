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


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real Filter
open scoped ComplexConjugate InnerProductSpace Topology ENNReal

abbrev DiskHardyCoefficients := lp (fun _ : ℕ => ℂ) 2

/-- The full physical H¹ mass of the mode `conj(z)^m`. -/
def diskAntiholomorphicH1Weight (m : ℕ) : ℝ :=
  π / ((m + 1 : ℕ) : ℝ) + 2 * π * (m : ℝ)

theorem diskAntiholomorphicH1Weight_pos (m : ℕ) :
    0 < diskAntiholomorphicH1Weight m := by
  unfold diskAntiholomorphicH1Weight
  positivity

private theorem hardy_value_antiholomorphicTest m :
    h1Value (ball (0 : ℂ) 1) (diskAntiholomorphicH1Test m) =
      diskAntiholomorphicArea m :=
  h1Value_smoothTraceH1 (ball (0 : ℂ) 1)
    ⟨diskHarmonicCutoff (diskAntiholomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)⟩

theorem inner_diskAntiholomorphicH1Test (m n : ℕ) :
    ⟪diskAntiholomorphicH1Test m, diskAntiholomorphicH1Test n⟫_ℂ =
      if m = n then (diskAntiholomorphicH1Weight m : ℂ) else 0 := by
  rw [h1_inner, hardy_value_antiholomorphicTest,
    hardy_value_antiholomorphicTest, inner_diskAntiholomorphicArea,
    have h_inl m n : (∑ i : Fin 2, ⟪h1Gradient (ball (0 : ℂ) 1) i (diskAntiholomorphicH1Test m), h1Gradient (ball (0 : ℂ) 1) i (diskAntiholomorphicH1Test n)⟫_ℂ) = if m = n then (2 * π : ℂ) * (m : ℂ) else 0 := by
      have h := inner_diskAntiholomorphicGradient m n
      rw [← diskH1Gradient_antiholomorphicTest m,
        ← diskH1Gradient_antiholomorphicTest n, PiLp.inner_apply] at h
      exact h
    h_inl]
  by_cases hmn : m = n
  · simp only [hmn, ite_true, diskAntiholomorphicH1Weight]
    push_cast
    ring
  · simp [hmn]

private theorem hardy_sqrt_inverse_normalizes  (hw : 0 < w) :
    conj ((Real.sqrt w : ℂ)⁻¹) *
      ((Real.sqrt w : ℂ)⁻¹ * (w : ℂ)) = 1 := by
  simp [map_inv₀]
  exact_mod_cast (by
    calc
      _ = (Real.sqrt w)⁻¹ *
          ((Real.sqrt w)⁻¹ * (Real.sqrt w * Real.sqrt w)) := by rw [show Real.sqrt w * Real.sqrt w = w by
            simpa [pow_two] using Real.sq_sqrt hw.le]
      _ = 1 := by field_simp [(Real.sqrt_pos.mpr hw).ne'])

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
local notation "Φ0" => ball 0 1

def diskUnitAntiholomorphicH1Test (m : ℕ) : NeumannH1 (Φ0) :=
  (Real.sqrt (diskAntiholomorphicH1Weight m) : ℂ)⁻¹ •
    diskAntiholomorphicH1Test m

theorem orthonormal_diskUnitAntiholomorphicH1Test :
    Orthonormal ℂ diskUnitAntiholomorphicH1Test :=
  hardy_orthonormal_of_gram diskAntiholomorphicH1Test
    diskAntiholomorphicH1Weight diskAntiholomorphicH1Weight_pos
    inner_diskAntiholomorphicH1Test

/-- The half-trace amplitude of an unscaled antiholomorphic monomial. -/
def diskHardyTraceScale (m : ℕ) : ℝ :=
  Real.sqrt (sobWeight (-(m : ℤ))) * Real.sqrt (2 * π)

theorem diskHardyTraceScale_pos m : 0 < diskHardyTraceScale m := by
  exact mul_pos (Real.sqrt_pos.mpr (sobWeight_pos _))
    (Real.sqrt_pos.mpr (by positivity))

private theorem hardy_sobWeight_neg_nat (m : ℕ) :
    sobWeight (-(m : ℤ)) = ((m + 1 : ℕ) : ℝ) := by
  simp [sobWeight, abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  ring

theorem diskHardyTraceScale_sq (m : ℕ) :
    diskHardyTraceScale m ^ 2 = 2 * π * ((m + 1 : ℕ) : ℝ) := by
  rw [diskHardyTraceScale, mul_pow, Real.sq_sqrt (sobWeight_pos _).le,
    Real.sq_sqrt (by positivity : 0 ≤ 2 * π), hardy_sobWeight_neg_nat]
  ring

/-- The ratio between unit H¹ coordinates and normalized trace coordinates. -/
def diskHardySynthesisWeight (m : ℕ) : ℝ :=
  Real.sqrt (diskAntiholomorphicH1Weight m) / diskHardyTraceScale m

private theorem hardy_nat_memℓp_two_iff_summable {f : ℕ → ℂ} :
    Memℓp f 2 ↔ Summable (fun m => ‖f m‖ ^ 2) := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp

private theorem hardy_negative_index_injective :
    Function.Injective (fun m : ℕ => -(m : ℤ)) := by
  intro m n h
  change -(m : ℤ) = -(n : ℤ) at h
  exact_mod_cast neg_injective h

def hardyWeightedCoefficientsLin
    (w : ℕ → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1) : L2Z →ₗ[ℂ] DiskHardyCoefficients where
  toFun b := ⟨fun m => w m * b (-(m : ℤ)), (show Memℓp (fun m => w m * b (-(m : ℤ))) 2 by
    refine hardy_nat_memℓp_two_iff_summable.mpr ?_
    have hs : Summable (fun m : ℕ => ‖b (-(m : ℤ))‖ ^ 2) :=
      (summable_norm_sq_L2Z b).comp_injective hardy_negative_index_injective
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun m => ?_) hs
    rw [norm_mul, mul_pow]
    calc
      _ ≤ 1 ^ 2 * ‖b (-m)‖ ^ 2 := by gcongr; exact hw m
      _ = _ := by ring)⟩
  map_add' b c := by
    ext m
    simp [mul_add]
    rfl
  map_smul' a b := by
    ext m
    simp
    ring

def hardyWeightedCoefficients
    (w : ℕ → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1) : L2Z →L[ℂ] DiskHardyCoefficients :=
  (hardyWeightedCoefficientsLin w hw).mkContinuous 1
    (fun b => by simpa using (show ‖hardyWeightedCoefficientsLin w hw b‖ ≤ ‖b‖ by
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
        have hn : ‖hardyWeightedCoefficientsLin w hw b‖ ^ 2 =
            ∑' m : ℕ, ‖w m * b (-m)‖ ^ 2 := by
          have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
            (hardyWeightedCoefficientsLin w hw b)
          simp at h
          exact h
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
            (fun n => sq_nonneg ‖b n‖) hardy_negative_index_injective)))

theorem hardy_synthesis_weight_bound (m : ℕ) :
    ‖(diskHardySynthesisWeight m : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_of_nonneg (by
    unfold diskHardySynthesisWeight
    exact div_nonneg (Real.sqrt_nonneg _) (diskHardyTraceScale_pos _).le)]
  exact (by
    rw [diskHardySynthesisWeight, div_le_one (diskHardyTraceScale_pos m)]
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (diskHardyTraceScale_pos m).le).mp
    rw [Real.sq_sqrt (diskAntiholomorphicH1Weight_pos m).le]
    exact (by
      have hm : 1 ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      have hdiv : π / ((m + 1 : ℕ) : ℝ) ≤ π := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [Real.pi_pos]
      rw [diskAntiholomorphicH1Weight, diskHardyTraceScale_sq]
      push_cast at hm hdiv ⊢
      nlinarith [Real.pi_pos]))

/-- The actual square-summable coordinates used by H¹ orthogonal synthesis. -/
def diskHardyCoefficientMap : L2Z →L[ℂ] DiskHardyCoefficients :=
  hardyWeightedCoefficients (fun m => (diskHardySynthesisWeight m : ℂ))
    hardy_synthesis_weight_bound

theorem diskHardyCoefficientMap_apply (b : L2Z) m :
    diskHardyCoefficientMap b m =
      (diskHardySynthesisWeight m : ℂ) * b (-(m : ℤ)) := rfl

def hardySynthesisIsometry :
    DiskHardyCoefficients →ₗᵢ[ℂ] NeumannH1 (Φ0) :=
  orthonormal_diskUnitAntiholomorphicH1Test.orthogonalFamily.linearIsometry

/-- Harmonic extension of the nonpositive normalized Fourier data, into the
actual weak-gradient H¹ space on the disk. -/
def diskHardyExtension : L2Z →L[ℂ] NeumannH1 (Φ0) :=
  hardySynthesisIsometry.toContinuousLinearMap.comp diskHardyCoefficientMap

theorem diskHardyExtension_hasSum b :
    HasSum (fun m : ℕ => (b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ)) •
      diskAntiholomorphicH1Test m) (diskHardyExtension b) := by
  have hs := orthonormal_diskUnitAntiholomorphicH1Test.orthogonalFamily.hasSum_linearIsometry
    (diskHardyCoefficientMap b)
  change HasSum (fun m =>
    diskHardyCoefficientMap b m • diskUnitAntiholomorphicH1Test m)
    (diskHardyExtension b) at hs
  convert hs using 1
  funext m
  have h_inl m a : (diskHardySynthesisWeight m : ℂ) * a * (Real.sqrt (diskAntiholomorphicH1Weight m) : ℂ)⁻¹ = a / (diskHardyTraceScale m : ℂ) := by
    rw [diskHardySynthesisWeight, Complex.ofReal_div, div_eq_mul_inv, div_eq_mul_inv]
    calc
      _ = ((Real.sqrt (diskAntiholomorphicH1Weight m)) *
          (Real.sqrt (diskAntiholomorphicH1Weight m) : ℂ)⁻¹) *
          (a * (diskHardyTraceScale m : ℂ)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (by
        exact_mod_cast (Real.sqrt_pos.mpr (diskAntiholomorphicH1Weight_pos m)).ne'), one_mul]
  rw [diskHardyCoefficientMap_apply, diskUnitAntiholomorphicH1Test, smul_smul,
    h_inl]

private theorem hardy_trace_term (b : L2Z) (m : ℕ) :
    diskHalfTrace ((b (-(m : ℤ)) / (diskHardyTraceScale m : ℂ)) •
      diskAntiholomorphicH1Test m) =
        b (-(m : ℤ)) • stdBasisZ (-(m : ℤ)) := by
  rw [map_smul, diskHalfTrace_antiholomorphicTest, smul_smul]
  rw [show (Real.sqrt (sobWeight (-m)) : ℂ) * Real.sqrt (2 * π) = (diskHardyTraceScale m) by
    simp [diskHardyTraceScale], div_mul_cancel₀ _ (show (diskHardyTraceScale m : ℂ) ≠ 0 by
    exact_mod_cast (diskHardyTraceScale_pos m).ne')]

private theorem hardy_nonpositive_series_coordinate
    (b x : L2Z)
    (hx : HasSum (fun m : ℕ => b (-m) • stdBasisZ (-(m : ℤ))) x)
    n : x n = if 0 < n then 0 else b n := by
  classical
  have hcoord := (innerSL ℂ (stdBasisZ n)).hasSum hx
  have hbasis (m : ℕ) :
      (innerSL ℂ (stdBasisZ n)) (b (-(m : ℤ)) • stdBasisZ (-(m : ℤ))) =
        if n = -(m : ℤ) then b (-(m : ℤ)) else 0 := by
    simp only [innerSL_apply_apply, inner_smul_right,
      orthonormal_iff_ite.mp stdBasisZ.orthonormal]
    split_ifs <;> simp
  have h_inl n b : ⟪stdBasisZ n, b⟫_ℂ = b n := by
    rw [stdBasisZ_apply, lp.inner_single_left]
    simp
  simp only [hbasis, innerSL_apply_apply, h_inl] at hcoord
  rw [← hcoord.tsum_eq]
  by_cases hn : 0 < n
  · simp [hn]
    rw [show (fun m : ℕ => if n = -(m : ℤ) then b (-(m : ℤ)) else 0) = (fun _ => 0) by
      funext m
      have hnm : n ≠ -(m : ℤ) := by omega
      simp [hnm]]
    simp
  · simp [hn]
    have hn0 : 0 ≤ -n := by omega
    let k := Int.toNat (-n)
    rw [tsum_eq_single k]
    · simp [← (show n = -k by
      omega)]
    · intro m hm
      simp [show n ≠ -m by omega]

/-- The extension has precisely the nonpositive normalized half trace. -/
theorem diskHalfTrace_diskHardyExtension_apply (b : L2Z) (n : ℤ) :
    diskHalfTrace (diskHardyExtension b) n = if 0 < n then 0 else b n :=
  hardy_nonpositive_series_coordinate b _ (show HasSum (fun m : ℕ => b (-(m : ℤ)) • stdBasisZ (-(m : ℤ))) (diskHalfTrace (diskHardyExtension b)) by
    simpa only [hardy_trace_term] using diskHalfTrace.hasSum (diskHardyExtension_hasSum b)) n

theorem diskHalfTrace_diskHardyExtension b :
    diskHalfTrace (diskHardyExtension b) = (1 - posProj) b := by
  ext n
  rw [diskHalfTrace_diskHardyExtension_apply]
  simp [posProj]
  split_ifs <;> simp

/-- A bounded genuine H¹ right inverse on the nonpositive Fourier subspace. -/
theorem diskHalfTrace_diskHardyExtension_eq_of_nonpositive b
    (hb : ∀ n : ℤ, 0 < n → b n = 0) :
    diskHalfTrace (diskHardyExtension b) = b := by
  ext n
  rw [diskHalfTrace_diskHardyExtension_apply]
  by_cases hn : 0 < n
  · simp [hn, hb n hn]
  · simp [hn]

private theorem hardy_gradient_component_antiholomorphicTest m i :
    h1Gradient (ball (0 : ℂ) 1) i (diskAntiholomorphicH1Test m) =
      diskAntiholomorphicGradient m i := by
  simpa [diskH1Gradient, PiLp.toLp_apply] using congrArg (fun G => G i) (diskH1Gradient_antiholomorphicTest m)

theorem diskAntiholomorphicH1Test_cauchyRiemann m :
    h1Gradient (ball (0 : ℂ) 1) 0 (diskAntiholomorphicH1Test m) =
      Complex.I • h1Gradient (ball (0 : ℂ) 1) 1 (diskAntiholomorphicH1Test m) := by
  rw [hardy_gradient_component_antiholomorphicTest,
    hardy_gradient_component_antiholomorphicTest]
  exact (by
    apply Lp.ext
    filter_upwards [diskAntiholomorphicGradient_ae m 0,
      diskAntiholomorphicGradient_ae m 1,
      Lp.coeFn_smul Complex.I (diskAntiholomorphicGradient m 1)] with z hx hy hsmul
    rw [hx, hsmul]
    change dirD (diskAntiholomorphicMode m) (coordDir 0) z =
      Complex.I * (diskAntiholomorphicGradient m 1) z
    rw [hy]
    simp [dirD_diskAntiholomorphicMode, show coordDir 0 = 1 from rfl, show coordDir 1 = Complex.I from rfl]
    ring_nf
    rw [Complex.I_sq]
    ring)

/-- The weak antiholomorphic derivative, without an inessential scalar factor. -/
def diskAntiholomorphicDefect :
    NeumannH1 (Φ0) →L[ℂ] L2 (Φ0) :=
  h1Gradient (Φ0) 0 -
    Complex.I • h1Gradient (Φ0) 1

theorem diskHardyExtension_cauchyRiemann b :
    h1Gradient (ball (0 : ℂ) 1) 0 (diskHardyExtension b) =
      Complex.I • h1Gradient (ball (0 : ℂ) 1) 1 (diskHardyExtension b) := by
  apply sub_eq_zero.mp
  exact (by
    exact (show HasSum (fun _ : ℕ => (0 : L2 (ball (0 : ℂ) 1))) (diskAntiholomorphicDefect (diskHardyExtension b)) by
      have h_inl m : diskAntiholomorphicDefect (diskAntiholomorphicH1Test m) = 0 := by simp [diskAntiholomorphicDefect, diskAntiholomorphicH1Test_cauchyRiemann]
      simpa [h_inl] using (diskAntiholomorphicDefect.hasSum (diskHardyExtension_hasSum b))).unique hasSum_zero)

end PolyaNeumann
