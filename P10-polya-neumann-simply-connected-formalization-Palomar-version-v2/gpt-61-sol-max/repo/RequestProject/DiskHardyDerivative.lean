module

public import RequestProject.PlanarGeometry

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

/-- The normalized derivative weight at output frequency `-k`. -/
def diskHardyDerivativeWeight k  :=
  (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) *
    Real.sqrt (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))

theorem diskHardyDerivativeWeight_nonneg k :
    0 ≤ diskHardyDerivativeWeight k := by
  unfold diskHardyDerivativeWeight
  positivity

theorem diskHardyDerivativeWeight_le_one k :
    diskHardyDerivativeWeight k ≤ 1 := by
  have hr0 : 0 ≤ (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) := by positivity
  have hr1 : (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) ≤ 1 := by
    bound
  have hs : Real.sqrt (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hr1
  unfold diskHardyDerivativeWeight
  nlinarith

/-- Positive output modes are zero. The nonpositive output `n` takes its
input from `n-1`, so output zero comes from input frequency `-1`. -/
def diskHardyDerivativeSymbol n  :=
  if 0 < n then 0 else (diskHardyDerivativeWeight (Int.toNat (-n)) : ℂ)

theorem norm_diskHardyDerivativeSymbol_le_one n :
    ‖diskHardyDerivativeSymbol n‖ ≤ 1 := by
  unfold diskHardyDerivativeSymbol
  split_ifs
  · norm_num
  · rw [Complex.norm_of_nonneg (diskHardyDerivativeWeight_nonneg _)]
    exact diskHardyDerivativeWeight_le_one _

private theorem derivative_shift_injective :
    Function.Injective (fun n : ℤ => n - 1) := by
  simp_all [Function.Injective]

theorem derivative_shift_memℓp (b : L2Z) :
    Memℓp (fun n : ℤ => b (n - 1)) 2 := memℓp_two_iff_summable.mpr
    ((summable_norm_sq_L2Z b).comp_injective derivative_shift_injective)

def derivativeShiftLin : L2Z →ₗ[ℂ] L2Z where
  toFun b := ⟨fun n => b (n - 1), derivative_shift_memℓp b⟩
  map_add' b c := by rfl
  map_smul' a b := by ext n; simp

private theorem derivative_shift_norm_le b :
    ‖derivativeShiftLin b‖ ≤ ‖b‖ := by
  have hs : ‖derivativeShiftLin b‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    rw [norm_sq_L2Z, norm_sq_L2Z]
    exact tsum_comp_le_tsum_of_inj (summable_norm_sq_L2Z b)
      (fun n => sq_nonneg ‖b n‖) derivative_shift_injective
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

def derivativeShift : L2Z →L[ℂ] L2Z :=
  derivativeShiftLin.mkContinuous 1 (fun b => by simpa using derivative_shift_norm_le b)

/-- The genuine bounded derivative-data operator. -/
def diskHardyDerivativeData  :=
  (diagOp diskHardyDerivativeSymbol 1 norm_diskHardyDerivativeSymbol_le_one).comp
    derivativeShift

theorem diskHardyDerivativeData_apply b n :
    diskHardyDerivativeData b n = diskHardyDerivativeSymbol n * b (n - 1) := rfl

theorem diskHardyDerivativeData_apply_pos b  (hn : 0 < n) :
    diskHardyDerivativeData b n = 0 := by
  simp_all [diskHardyDerivativeData_apply, diskHardyDerivativeSymbol]

theorem diskHardyDerivativeData_apply_neg b (k : ℕ) :
    diskHardyDerivativeData b (-(k : ℤ)) =
      (diskHardyDerivativeWeight k : ℂ) * b (-((k + 1 : ℕ) : ℤ)) := by
  have hn : ¬ (0 : ℤ) < -(k : ℤ) := by omega
  have hi : -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) := by omega
  simp_all [diskHardyDerivativeData_apply, diskHardyDerivativeSymbol]

theorem common_derivative_smoothing_one_apply b n :
    sobolevSmoothing 1 (by norm_num) b n = (sobWeight n : ℂ)⁻¹ * b n := by
  simp  [sobolevSmoothing, Real.rpow_neg_one]

private theorem derivative_sqrt_ratio_scale  (ha : 0 < a)
    b (hb : 0 < b) (hc : 0 < c) :
    (a / b * Real.sqrt (a / b)) / (Real.sqrt a * c) =
      (a / b) / (Real.sqrt b * c) := by
  rw [Real.sqrt_div ha.le]
  grind

private theorem derivative_weight_over_traceScale k :
    diskHardyDerivativeWeight k / diskHardyTraceScale k =
      (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) /
        diskHardyTraceScale (k + 1) := by
  simpa only [diskHardyDerivativeWeight, diskHardyTraceScale, common_hardy_sobWeight_neg_nat] using
      derivative_sqrt_ratio_scale (by positivity)
        ((k + 2 : ℕ)) (by positivity) (Real.sqrt_pos.mpr (by positivity))

private theorem derivative_series_scalar b k :
    (sobolevSmoothing 1 (by norm_num) b (-((k + 1 : ℕ) : ℤ)) /
      (diskHardyTraceScale (k + 1) : ℂ)) * ((k + 1 : ℕ) : ℂ) =
        diskHardyDerivativeData b (-(k : ℤ)) / (diskHardyTraceScale k : ℂ) := by
  have hc : (diskHardyDerivativeWeight k : ℂ) / (diskHardyTraceScale k : ℂ) =
      (((k + 1 : ℕ) : ℂ) / ((k + 2 : ℕ) : ℂ)) /
        (diskHardyTraceScale (k + 1) : ℂ) := by
    simpa   using
      congrArg (fun r : ℝ => (r : ℂ)) (derivative_weight_over_traceScale k)
  rw [common_derivative_smoothing_one_apply, common_hardy_sobWeight_neg_nat,
    diskHardyDerivativeData_apply_neg]
  simp  
  grind

/-- Actual weak `x` derivative of the constant disk mode. -/
theorem diskAntiholomorphicH1Test_gradient_zero :
    h1Gradient unitDisk 0 (diskAntiholomorphicH1Test 0) = 0 := by
  rw [common_hardy_gradient_component_antiholomorphicTest]
  apply Lp.ext
  filter_upwards [diskAntiholomorphicGradient_ae 0 0,
    Lp.coeFn_zero ℂ 2 (volume.restrict (ball 0 1))] with z hz hzero
  rw [hz, hzero]
  simp  [dirD_diskAntiholomorphicMode]

/-- Actual weak `x` derivative of a nonconstant disk mode. -/
theorem diskAntiholomorphicH1Test_gradient_succ k :
    h1Gradient unitDisk 0 (diskAntiholomorphicH1Test (k + 1)) =
      ((k + 1 : ℕ) : ℂ) • diskAntiholomorphicArea k := by
  rw [common_hardy_gradient_component_antiholomorphicTest]
  apply Lp.ext
  filter_upwards [diskAntiholomorphicGradient_ae (k + 1) 0,
    diskAntiholomorphicArea_ae k,
    Lp.coeFn_smul ((k + 1 : ℕ) : ℂ) (diskAntiholomorphicArea k)] with z hg ha hsmul
  rw [hg, hsmul]
  change dirD (diskAntiholomorphicMode (k + 1)) (coordDir 0) z =
    ((k + 1 : ℕ)) * ((diskAntiholomorphicArea k) z)
  rw [ha]
  simp  [dirD_diskAntiholomorphicMode, show coordDir 0 = (1 : ℂ) from rfl]

private theorem derivative_hasSum_tail
    {H : Type*} [NormedAddCommGroup H] f (x : H)
    (hzero : f 0 = 0) (hs : HasSum f x) : HasSum (fun k => f (k + 1)) x := by
  apply (hasSum_nat_add_iff 1).mpr
  simp_all

/-- The smoothed Hardy extension has a weak derivative which is itself
the value of an actual H¹ Hardy extension. -/
theorem diskHardyExtension_smoothing_gradient b :
    h1Gradient unitDisk 0
        (diskHardyExtension (sobolevSmoothing 1 (by norm_num) b)) =
      h1Value unitDisk (diskHardyExtension (diskHardyDerivativeData b)) := by
  let f : ℕ → L2 unitDisk := fun m =>
    (sobolevSmoothing 1 (by norm_num) b (-m) /
      (diskHardyTraceScale m)) •
        h1Gradient (ball 0 1) 0 (diskAntiholomorphicH1Test m)
  have hs : HasSum f
      (h1Gradient unitDisk 0
        (diskHardyExtension (sobolevSmoothing 1 (by norm_num) b))) := by
    simpa only [map_smul] using
      (h1Gradient (ball 0 1) 0).hasSum
        (diskHardyExtension_hasSum (sobolevSmoothing 1 (by norm_num) b))
  have hz : f 0 = 0 := by
    simp  [f, diskAntiholomorphicH1Test_gradient_zero]
  have ht := derivative_hasSum_tail f _ hz hs
  have hv := (h1Value (ball 0 1)).hasSum
    (diskHardyExtension_hasSum (diskHardyDerivativeData b))
  refine (ht.congr_fun (fun k => ?_)).unique hv
  symm
  simp only [f, diskAntiholomorphicH1Test_gradient_succ, smul_smul, map_smul,
    h1Value_diskAntiholomorphicH1Test,
    derivative_series_scalar]

end PolyaNeumann
