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

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real Filter
open scoped ComplexConjugate InnerProductSpace Topology

section

variable (k : ℕ)
include k

/-- The normalized derivative weight at output frequency `-k`. -/
def diskHardyDerivativeWeight  : ℝ :=
  (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) *
    Real.sqrt (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ))

theorem diskHardyDerivativeWeight_nonneg  :
    0 ≤ diskHardyDerivativeWeight k := by
  unfold diskHardyDerivativeWeight
  positivity

theorem diskHardyDerivativeWeight_le_one  :
    diskHardyDerivativeWeight k ≤ 1 := by
  have hr0 : 0 ≤ (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) := by positivity
  have hr1 : (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    simp
  have hs : Real.sqrt (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) ≤ 1 := by
    simp_all
  unfold diskHardyDerivativeWeight
  nlinarith

end

/-- Positive output modes are zero. The nonpositive output `n` takes its
input from `n-1`, so output zero comes from input frequency `-1`. -/
def diskHardyDerivativeSymbol (n : ℤ) : ℂ :=
  if 0 < n then 0 else (diskHardyDerivativeWeight (Int.toNat (-n)) : ℂ)

theorem norm_diskHardyDerivativeSymbol_le_one (n : ℤ) :
    ‖diskHardyDerivativeSymbol n‖ ≤ 1 := by
  unfold diskHardyDerivativeSymbol
  split_ifs
  simp
  · rw [Complex.norm_of_nonneg (diskHardyDerivativeWeight_nonneg _)]
    exact diskHardyDerivativeWeight_le_one _

private theorem derivative_shift_injective :
    Function.Injective (fun n : ℤ => n - 1) := by
  intro m n h
  simp_all

theorem derivative_shift_memℓp (b : L2Z) :
    Memℓp (fun n : ℤ => b (n - 1)) 2 := by
  exact memℓp_two_iff_summable.mpr
    ((summable_norm_sq_L2Z b).comp_injective derivative_shift_injective)

def derivativeShiftLin : L2Z →ₗ[ℂ] L2Z where
  toFun b := ⟨fun n => b (n - 1), derivative_shift_memℓp b⟩
  map_add' b c := by rfl
  map_smul' a b := by rfl

private theorem derivative_shift_norm_le (b : L2Z) :
    ‖derivativeShiftLin b‖ ≤ ‖b‖ := by
  have hs : ‖derivativeShiftLin b‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    rw [norm_sq_L2Z, norm_sq_L2Z]
    exact tsum_comp_le_tsum_of_inj (summable_norm_sq_L2Z b)
      (fun n => sq_nonneg ‖b n‖) derivative_shift_injective
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

def derivativeShift : L2Z →L[ℂ] L2Z :=
  derivativeShiftLin.mkContinuous 1 (fun b => by simpa using derivative_shift_norm_le b)

/-- The genuine bounded derivative-data operator. -/
def diskHardyDerivativeData : L2Z →L[ℂ] L2Z :=
  (diagOp diskHardyDerivativeSymbol 1 norm_diskHardyDerivativeSymbol_le_one).comp
    derivativeShift

section

variable (b : L2Z)
include b

theorem diskHardyDerivativeData_apply  (n : ℤ) :
    diskHardyDerivativeData b n = diskHardyDerivativeSymbol n * b (n - 1) := rfl

theorem diskHardyDerivativeData_apply_pos  {n : ℤ} (hn : 0 < n) :
    diskHardyDerivativeData b n = 0 := by
  simp_all [diskHardyDerivativeData_apply, diskHardyDerivativeSymbol, ite_true, zero_mul]

theorem diskHardyDerivativeData_apply_neg  (k : ℕ) :
    diskHardyDerivativeData b (-(k : ℤ)) =
      (diskHardyDerivativeWeight k : ℂ) * b (-((k + 1 : ℕ) : ℤ)) := by
  have hn : ¬ (0 : ℤ) < -(k : ℤ) := by omega
  have hi : -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) := by omega
  simp  [diskHardyDerivativeData_apply, diskHardyDerivativeSymbol, hn,
    ite_false, neg_neg, Int.toNat_natCast, hi]

end

private theorem derivative_sqrt_ratio_scale {a c : ℝ} (ha : 0 < a)
    (b : ℝ) (hb : 0 < b) (hc : 0 < c) :
    (a / b * Real.sqrt (a / b)) / (Real.sqrt a * c) =
      (a / b) / (Real.sqrt b * c) := by
  rw [Real.sqrt_div ha.le]
  grind

private theorem derivative_weight_over_traceScale (k : ℕ) :
    diskHardyDerivativeWeight k / diskHardyTraceScale k =
      (((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) /
        diskHardyTraceScale (k + 1) := by
  simpa only [diskHardyDerivativeWeight, diskHardyTraceScale,
    sobWeight_neg_nat, Nat.add_assoc, Nat.reduceAdd] using
      derivative_sqrt_ratio_scale (by positivity : 0 < ((k + 1 : ℕ) : ℝ))
        ((k + 2 : ℕ) : ℝ) (by positivity) (Real.sqrt_pos.mpr (by positivity : 0 < 2 * π))

private theorem derivative_series_scalar (b : L2Z) (k : ℕ) :
    (sobolevSmoothing 1 (by norm_num) b (-((k + 1 : ℕ) : ℤ)) /
      (diskHardyTraceScale (k + 1) : ℂ)) * ((k + 1 : ℕ) : ℂ) =
        diskHardyDerivativeData b (-(k : ℤ)) / (diskHardyTraceScale k : ℂ) := by
  have hc : (diskHardyDerivativeWeight k : ℂ) / (diskHardyTraceScale k : ℂ) =
      (((k + 1 : ℕ) : ℂ) / ((k + 2 : ℕ) : ℂ)) /
        (diskHardyTraceScale (k + 1) : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast] using
      congrArg (fun r : ℝ => (r : ℂ)) (derivative_weight_over_traceScale k)
  rw [sobolevSmoothing_one_apply, sobWeight_neg_nat,
    diskHardyDerivativeData_apply_neg]
  simp only [Complex.ofReal_natCast]
  grind


private theorem derivative_mode_gradient_component (m : ℕ) (i : Fin 2) :
    h1Gradient (ball (0 : ℂ) 1) i (diskAntiholomorphicH1Test m) =
      diskAntiholomorphicGradient m i := by rfl

/-- Actual weak `x` derivative of the constant disk mode. -/
theorem diskAntiholomorphicH1Test_gradient_zero :
    h1Gradient (ball (0 : ℂ) 1) 0 (diskAntiholomorphicH1Test 0) = 0 := by
  rw [derivative_mode_gradient_component]
  apply Lp.ext
  filter_upwards [diskAntiholomorphicGradient_ae 0 0,
    Lp.coeFn_zero ℂ 2 (volume.restrict (ball (0 : ℂ) 1))] with z hz hzero
  rw [hz, hzero]
  simp  [dirD_diskAntiholomorphicMode]

/-- Actual weak `x` derivative of a nonconstant disk mode. -/
theorem diskAntiholomorphicH1Test_gradient_succ (k : ℕ) :
    h1Gradient (ball (0 : ℂ) 1) 0 (diskAntiholomorphicH1Test (k + 1)) =
      ((k + 1 : ℕ) : ℂ) • diskAntiholomorphicArea k := by
  rw [derivative_mode_gradient_component]
  apply Lp.ext
  filter_upwards [diskAntiholomorphicGradient_ae (k + 1) 0,
    diskAntiholomorphicArea_ae k,
    Lp.coeFn_smul ((k + 1 : ℕ) : ℂ) (diskAntiholomorphicArea k)] with z hg ha hsmul
  rw [hg, hsmul]
  change dirD (diskAntiholomorphicMode (k + 1)) (coordDir 0) z =
    ((k + 1 : ℕ) : ℂ) * ((diskAntiholomorphicArea k : ℂ → ℂ) z)
  rw [ha]
  simp  [dirD_diskAntiholomorphicMode, show coordDir 0 = (1 : ℂ) from rfl, mul_one]

private theorem derivative_hasSum_tail
    {H : Type*} [NormedAddCommGroup H] (f : ℕ → H) (x : H)
    (hzero : f 0 = 0) (hs : HasSum f x) : HasSum (fun k => f (k + 1)) x := by
  apply (hasSum_nat_add_iff 1).mpr
  simp_all

/-- The smoothed Hardy extension has a weak derivative which is itself
the value of an actual H¹ Hardy extension. -/
theorem diskHardyExtension_smoothing_gradient (b : L2Z) :
    h1Gradient (ball (0 : ℂ) 1) 0
        (diskHardyExtension (sobolevSmoothing 1 (by norm_num) b)) =
      h1Value (ball (0 : ℂ) 1) (diskHardyExtension (diskHardyDerivativeData b)) := by
  let f : ℕ → L2 (ball (0 : ℂ) 1) := fun m =>
    (sobolevSmoothing 1 (by norm_num) b (-(m : ℤ)) /
      (diskHardyTraceScale m : ℂ)) •
        h1Gradient (ball (0 : ℂ) 1) 0 (diskAntiholomorphicH1Test m)
  have hs : HasSum f
      (h1Gradient (ball (0 : ℂ) 1) 0
        (diskHardyExtension (sobolevSmoothing 1 (by norm_num) b))) := by
    simpa only [map_smul] using
      (h1Gradient (ball (0 : ℂ) 1) 0).hasSum
        (diskHardyExtension_hasSum (sobolevSmoothing 1 (by norm_num) b))
  have hz : f 0 = 0 := by
    simp  [f, diskAntiholomorphicH1Test_gradient_zero]
  have ht := derivative_hasSum_tail f _ hz hs
  have hv := (h1Value (ball (0 : ℂ) 1)).hasSum
    (diskHardyExtension_hasSum (diskHardyDerivativeData b))
  have ht' : HasSum (fun k : ℕ =>
      (diskHardyDerivativeData b (-(k : ℤ)) / (diskHardyTraceScale k : ℂ)) •
        diskAntiholomorphicArea k)
      (h1Gradient (ball (0 : ℂ) 1) 0
        (diskHardyExtension (sobolevSmoothing 1 (by norm_num) b))) := by
    convert ht using 1
    funext k
    simp only [f, diskAntiholomorphicH1Test_gradient_succ, smul_smul,
      derivative_series_scalar]
  have hv' : HasSum (fun k : ℕ =>
      (diskHardyDerivativeData b (-(k : ℤ)) / (diskHardyTraceScale k : ℂ)) •
        diskAntiholomorphicArea k)
      (h1Value (ball (0 : ℂ) 1) (diskHardyExtension (diskHardyDerivativeData b))) := by
    assumption
  exact ht'.unique hv'

end PolyaNeumann
