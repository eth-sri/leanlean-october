module

public import RequestProject.DiskHardyExtension

/-!
# The actual weak derivative of a smoothed disk Hardy extension

One extra order of boundary smoothing turns the weak derivative of the
antiholomorphic H¹ extension into the value of another genuine H¹ extension.
The derivative data are constructed as a bounded weighted Fourier shift.
The proof differentiates the convergent physical H¹ series, removes its
constant term, and reindexes the remaining actual monomial derivatives.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real Filter
open scoped ComplexConjugate InnerProductSpace Topology

/-- The normalized derivative weight at output frequency `-k`. -/
def diskHardyDerivativeWeight (k : ℕ) : ℝ :=
  (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) *
    Real.sqrt (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))

theorem diskHardyDerivativeWeight_le_one (k : ℕ) :
    diskHardyDerivativeWeight k ≤ 1 := by
  have hr0 : 0 ≤ (k + 1 : ℕ) / (k + 2 : ℕ) := by positivity
  have hr1 : ((k + 1 : ℕ) : ℝ) / (k + 2 : ℕ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast Nat.le_add_right (k + 1) 1
  unfold diskHardyDerivativeWeight
  calc
    _ ≤ 1 * 1 := mul_le_mul hr1 (by
      simpa using Real.sqrt_le_sqrt hr1) (Real.sqrt_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- Positive output modes are zero. The nonpositive output `n` takes its
input from `n-1`, so output zero comes from input frequency `-1`. -/
def diskHardyDerivativeSymbol (n : ℤ) : ℂ :=
  if 0 < n then 0 else (diskHardyDerivativeWeight (Int.toNat (-n)) : ℂ)

theorem norm_diskHardyDerivativeSymbol_le_one n :
    ‖diskHardyDerivativeSymbol n‖ ≤ 1 := by
  unfold diskHardyDerivativeSymbol
  split_ifs
  · norm_num
  · rw [Complex.norm_of_nonneg (by
    unfold diskHardyDerivativeWeight
    positivity)]
    exact diskHardyDerivativeWeight_le_one _

private theorem derivative_shift_injective :
    Function.Injective (fun n : ℤ => n - 1) := by
  intro m n h
  change m - 1 = n - 1 at h
  omega

def derivativeShiftLin : L2Z →ₗ[ℂ] L2Z where
  toFun b := ⟨fun n => b (n - 1), (show Memℓp (fun n : ℤ => b (n - 1)) 2 by
    exact memℓp_two_iff_summable.mpr
      ((summable_norm_sq_L2Z b).comp_injective derivative_shift_injective))⟩
  map_add' b c := by ext n; simp; rfl
  map_smul' a b := by ext n; simp

/-- The genuine bounded derivative-data operator. -/
def diskHardyDerivativeData : L2Z →L[ℂ] L2Z :=
  (diagOp diskHardyDerivativeSymbol 1 norm_diskHardyDerivativeSymbol_le_one).comp
    (derivativeShiftLin.mkContinuous 1 (fun b => by simpa using (show ‖derivativeShiftLin b‖ ≤ ‖b‖ by
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
        rw [norm_sq_L2Z, norm_sq_L2Z]
        exact tsum_comp_le_tsum_of_inj (summable_norm_sq_L2Z b)
          (fun n => sq_nonneg ‖b n‖) derivative_shift_injective))))

theorem diskHardyDerivativeData_apply b n :
    diskHardyDerivativeData b n = diskHardyDerivativeSymbol n * b (n - 1) := rfl

theorem diskHardyDerivativeData_apply_pos b  (hn : 0 < n) :
    diskHardyDerivativeData b n = 0 := by
  simp [diskHardyDerivativeData_apply, diskHardyDerivativeSymbol, hn]

theorem diskHardyDerivativeData_apply_neg (b : L2Z) (k : ℕ) :
    diskHardyDerivativeData b (-(k : ℤ)) =
      (diskHardyDerivativeWeight k : ℂ) * b (-((k + 1 : ℕ) : ℤ)) := by
  have hn : ¬ (0 : ℤ) < -k := by omega
  simp [diskHardyDerivativeData_apply, diskHardyDerivativeSymbol, show -(k : ℤ) - 1 = -(k + 1 : ℕ) by omega]

private theorem derivative_sobWeight_neg_nat (m : ℕ) :
    sobWeight (-(m : ℤ)) = ((m + 1 : ℕ) : ℝ) := by
  simp [sobWeight, abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  ring

private theorem derivative_sqrt_ratio_scale  (ha : 0 < a)
    b (hb : 0 < b) (hc : 0 < c) :
    a / b * Real.sqrt (a / b) / (Real.sqrt a * c) =
      a / b / (Real.sqrt b * c) := by
  rw [Real.sqrt_div ha.le]
  field_simp [(Real.sqrt_pos.mpr ha).ne', (Real.sqrt_pos.mpr hb).ne', hb.ne', hc.ne']

local notation "Φ0" => ball 0 1

private theorem derivative_mode_value m :
    h1Value (Φ0) (diskAntiholomorphicH1Test m) =
      diskAntiholomorphicArea m :=
  h1Value_smoothTraceH1 (Φ0)
    ⟨diskHarmonicCutoff (diskAntiholomorphicMode m),
      diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)⟩

private theorem derivative_mode_gradient_component m i :
    h1Gradient (Φ0) i (diskAntiholomorphicH1Test m) =
      diskAntiholomorphicGradient m i := by
  simpa [diskH1Gradient, PiLp.toLp_apply] using congrArg (fun G => G i) (diskH1Gradient_antiholomorphicTest m)

/-- Actual weak `x` derivative of a nonconstant disk mode. -/
theorem diskAntiholomorphicH1Test_gradient_succ k :
    h1Gradient (Φ0) 0 (diskAntiholomorphicH1Test (k + 1)) =
      ((k + 1 : ℕ) : ℂ) • diskAntiholomorphicArea k := by
  rw [derivative_mode_gradient_component]
  apply Lp.ext
  filter_upwards [diskAntiholomorphicGradient_ae (k + 1) 0,
    diskAntiholomorphicArea_ae k,
    Lp.coeFn_smul ((k + 1 : ℕ) : ℂ) (diskAntiholomorphicArea k)] with z hg ha hsmul
  rw [hg, hsmul]
  change dirD (diskAntiholomorphicMode (k + 1)) (coordDir 0) z =
    (k + 1 : ℕ) * (diskAntiholomorphicArea k) z
  rw [ha]
  simp [dirD_diskAntiholomorphicMode, show coordDir 0 = 1 from rfl]

private theorem derivative_hasSum_tail
    {H : Type*} [NormedAddCommGroup H] (f : ℕ → H) x
    (hzero : f 0 = 0) (hs : HasSum f x) : HasSum (fun k => f (k + 1)) x := by
  apply (hasSum_nat_add_iff 1).mpr
  simpa [Finset.sum_range_one, hzero] using hs

/-- The smoothed Hardy extension has a weak derivative which is itself
the value of an actual H¹ Hardy extension. -/
theorem diskHardyExtension_smoothing_gradient (b : L2Z) :
    h1Gradient (Φ0) 0
        (diskHardyExtension (sobolevSmoothing 1 (by norm_num) b)) =
      h1Value (Φ0) (diskHardyExtension (diskHardyDerivativeData b)) := by
  let f : ℕ → L2 (Φ0) := fun m =>
    (sobolevSmoothing 1 (by norm_num) b (-m) /
      (diskHardyTraceScale m)) •
        h1Gradient (Φ0) 0 (diskAntiholomorphicH1Test m)
  have hs : HasSum f
      (h1Gradient (Φ0) 0
        (diskHardyExtension (sobolevSmoothing 1 (by norm_num) b))) := by
    simpa only [map_smul] using
      (h1Gradient (Φ0) 0).hasSum
        (diskHardyExtension_hasSum (sobolevSmoothing 1 (by norm_num) b))
  have ht' : HasSum (fun k : ℕ =>
      (diskHardyDerivativeData b (-(k : ℤ)) / (diskHardyTraceScale k)) •
        diskAntiholomorphicArea k)
      (h1Gradient (ball (0 : ℂ) 1) 0
        (diskHardyExtension (sobolevSmoothing 1 (by norm_num) b))) := by
    convert (derivative_hasSum_tail f _ (by
      simp only [f, show h1Gradient (Φ0) 0 (diskAntiholomorphicH1Test 0) = 0 by
        rw [derivative_mode_gradient_component]
        apply Lp.ext
        filter_upwards [diskAntiholomorphicGradient_ae 0 0,
          Lp.coeFn_zero ℂ 2 (volume.restrict (Φ0))] with z hz hzero
        rw [hz, hzero]
        simp [dirD_diskAntiholomorphicMode], smul_zero]) hs) using 1
    funext k
    have h_inl b k : (sobolevSmoothing 1 (by norm_num) b (-((k + 1 : ℕ) : ℤ)) / (diskHardyTraceScale (k + 1) : ℂ)) * ((k + 1 : ℕ) : ℂ) = diskHardyDerivativeData b (-(k : ℤ)) / (diskHardyTraceScale k : ℂ) := by
      have h_inl b n : sobolevSmoothing 1 (by norm_num) b n = (sobWeight n : ℂ)⁻¹ * b n := by simp [sobolevSmoothing, Real.rpow_neg_one]
      rw [h_inl, derivative_sobWeight_neg_nat,
        diskHardyDerivativeData_apply_neg]
      simp [Nat.add_assoc, Nat.reduceAdd]
      calc
        _ = (((k + 1 : ℕ) / (k + 2 : ℕ)) /
            (diskHardyTraceScale (k + 1))) * b (-(k + 1 : ℕ)) := by
          simp [div_eq_mul_inv]
          ring
        _ = (diskHardyDerivativeWeight k) / (diskHardyTraceScale k) *
            b (-((k + 1 : ℕ) : ℤ)) := by rw [show (diskHardyDerivativeWeight k : ℂ) / diskHardyTraceScale k = (k + 1 : ℕ) / (k + 2 : ℕ) / (diskHardyTraceScale (k + 1)) by
              simpa using
                congrArg (fun r : ℝ => (r : ℂ)) (show diskHardyDerivativeWeight k / diskHardyTraceScale k = (k + 1 : ℕ) / (k + 2 : ℕ) / diskHardyTraceScale (k + 1) by
                  simpa only [diskHardyDerivativeWeight, diskHardyTraceScale,
                    derivative_sobWeight_neg_nat, Nat.add_assoc, Nat.reduceAdd] using
                      derivative_sqrt_ratio_scale (by positivity : 0 < ((k + 1 : ℕ) : ℝ))
                        ((k + 2 : ℕ) : ℝ) (by positivity) (Real.sqrt_pos.mpr (by positivity : 0 < 2 * π)))]
        _ = _ := by simp [div_eq_mul_inv]; ring
    simp only [f, diskAntiholomorphicH1Test_gradient_succ, smul_smul,
      h_inl]
  exact ht'.unique (by
    simpa only [map_smul, derivative_mode_value] using ((h1Value (Φ0)).hasSum (diskHardyExtension_hasSum (diskHardyDerivativeData b))))

end PolyaNeumann
