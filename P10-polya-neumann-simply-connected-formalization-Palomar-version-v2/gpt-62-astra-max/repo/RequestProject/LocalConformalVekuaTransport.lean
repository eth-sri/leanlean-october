module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.PhysicalDrivenRowsReconstruction
public import RequestProject.LocalConformalVekuaConormalBridge
public import RequestProject.NeumannResonanceDimension
public import RequestProject.LocalConformalHardySubspace
public import RequestProject.PhysicalDrivenHardyRegularity
public import RequestProject.PhysicalDrivenKernelConormal
public import RequestProject.PeriodicFourierDerivative
public import RequestProject.LocalConformalBoundaryLipschitz
public import Mathlib.Analysis.Calculus.SmoothSeries
public import RequestProject.PlanarNotation

/-!
# Genuine Vekua trace rows in the transport Hilbert space

The rows in this file are the actual averaged coordinate traces of the
physical Vekua map on the actual Hardy primitive powers. The genuine
Volterra trace HasSum gives factorial decay in the row index, rather than
an exponential bound insufficient for Ell². This constructs a true
Ell²-valued boundary vector, with its exact sqrt(2) zeroth scale, initial
value and periodic endpoint.

Conormal-kernel regularity is derived from the existing actual smoothing
identity. The true tangential recurrences and Fourier inversion give the
homogeneous Ell² transport equation in that kernel. Its actual periodic
endpoint and a nonzero basepoint cut then prove reference-energy
injectivity, without a nonresonance or assumed regularity premise.

The forward driven equation for a general nonzero coordinate load and
its endpoint/observation identity remain separate. No initial conformal
map existence is asserted here.

This module is part of the verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open Set MeasureTheory Filter Metric
open scoped Topology ComplexConjugate

section

variable (γ : ℝ → ℂ) (E : ℂ) (h : ℝ → ℂ) (n j : ℕ) (θ : ℝ)

include E h j n γ θ in
/-- The actual interval-integral series defining row n of a Vekua trace. -/
def volterraVekuaTraceRowTerm : ℂ :=
  physicalVekuaCoeff E j * (γ θ - γ 0) ^ j *
    volterraPrimitiveIterate (fun s => conj (deriv γ s)) h (j + n) θ

include E h n γ θ in
def volterraVekuaTraceRow : ℂ :=
  ∑' j : ℕ, volterraVekuaTraceRowTerm γ E h n j θ

private theorem transport_norm_physicalVekuaCoeff :
    ‖physicalVekuaCoeff E j‖ = (‖E‖ / 4) ^ j / (j.factorial : ℝ) := by
  simp [physicalVekuaCoeff]

private theorem volterraVekuaTraceRowTerm_bound
    {γ h : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (hh : Continuous h) (E : ℂ)
    {M H R : ℝ} (hM0 : 0 ≤ M) (hH0 : 0 ≤ H) (hR0 : 0 ≤ R)
    (hM : ∀ θ ∈ angleInterval, ‖conj (deriv γ θ)‖ ≤ M)
    (hH : ∀ θ ∈ angleInterval, ‖h θ‖ ≤ H)
    (hR : ∀ θ ∈ angleInterval, ‖γ θ - γ 0‖ ≤ R)
    (n j : ℕ) {θ : ℝ} (hθ : θ ∈ angleInterval) :
    ‖volterraVekuaTraceRowTerm γ E h n j θ‖ ≤
      (H * (M * anglePeriod) ^ n / (n.factorial : ℝ)) *
        ((‖E‖ / 4 * R * (M * anglePeriod)) ^ j / (j.factorial : ℝ)) := by
  have ha : Continuous (fun s => conj (deriv γ s)) :=
    Complex.continuous_conj.comp hγ.continuous_deriv_one
  have hJ := volterraPrimitiveIterate_bound_uniform ha hh hM0 hH0
    hM hH (j + n) θ hθ
  have hfact : (n.factorial : ℝ) ≤ ((j + n).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ j + n)
  simp [volterraVekuaTraceRowTerm, norm_mul, norm_pow, transport_norm_physicalVekuaCoeff]
  calc
    _ ≤ ((‖E‖ / 4) ^ j / j.factorial) * R ^ j *
        (H * (M * anglePeriod) ^ (j + n) / (j + n).factorial) := by
      gcongr <;> exact hR θ hθ
    _ ≤ ((‖E‖ / 4) ^ j / j.factorial) * R ^ j *
        (H * (M * anglePeriod) ^ (j + n) / n.factorial) := by
      gcongr
    _ = _ := by
      simp [pow_add, mul_pow]
      ring

theorem volterraVekuaTraceRowTerm_continuous
    {γ h : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (hh : Continuous h)
    (E : ℂ) (n j : ℕ) : Continuous (volterraVekuaTraceRowTerm γ E h n j) := (continuous_const.mul ((hγ.continuous.sub continuous_const).pow j)).mul
    (continuous_volterraPrimitiveIterate
      (Complex.continuous_conj.comp hγ.continuous_deriv_one) hh (j + n))

/-- Actual row-index factorial decay on the whole parameter interval. -/
theorem exists_volterraVekuaTraceRow_factorial_bound
    {γ h : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (hh : Continuous h) (E : ℂ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      (∀ n θ, θ ∈ angleInterval →
        ‖volterraVekuaTraceRow γ E h n θ‖ ≤ C * B ^ n / (n.factorial : ℝ)) ∧
      (∀ n, ContinuousOn (volterraVekuaTraceRow γ E h n) angleInterval) := by
  have hzero : 0 ∈ angleInterval := ⟨le_rfl, Real.two_pi_pos.le⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn
  obtain ⟨H, hH⟩ := isCompact_Icc.exists_bound_of_continuousOn hh.continuousOn
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hγ.continuous.sub continuous_const).continuousOn
  have hM0  := (norm_nonneg _).trans (hM 0 hzero)
  have hH0  := (norm_nonneg _).trans (hH 0 hzero)
  have hR0  := (norm_nonneg _).trans (hR 0 hzero)
  let B := M * anglePeriod
  let r := ‖E‖ / 4 * R * B
  let S  := ∑' j : ℕ, r ^ j / j.factorial
  
  
  
  
  have hmaj (n : ℕ) : Summable (fun j : ℕ =>
      (H * B ^ n / (n.factorial : ℝ)) * (r ^ j / (j.factorial : ℝ))) :=
    (Real.summable_pow_div_factorial r).mul_left _
  have hbd (n j : ℕ) (θ : ℝ) (hθ : θ ∈ angleInterval)  :=
    volterraVekuaTraceRowTerm_bound hγ hh E hM0 hH0 hR0 hM hH hR n j hθ
  refine ⟨H * S, B, mul_nonneg hH0 (tsum_nonneg fun _ => by positivity), (by positivity), ?_, ?_⟩
  · intro n θ hθ
    have hn  :=
      Summable.of_nonneg_of_le ((by norm_num)) (fun j => hbd n j θ hθ) (hmaj n)
    calc
      _ ≤ _ := norm_tsum_le_tsum_norm hn
      _ ≤ _ := Summable.tsum_le_tsum (fun j => hbd n j θ hθ) hn (hmaj n)
      _ = _ := by simp [tsum_mul_left] <;> ring
  · intro n
    
    apply (HasSumUniformlyOn.of_norm_le_summable (hmaj n) (hbd n)).tendstoUniformlyOn.continuousOn
    exact (Eventually.of_forall fun s : Finset ℕ => continuousOn_finset_sum s
      (fun j _ => (volterraVekuaTraceRowTerm_continuous hγ hh E n j).continuousOn)).frequently

theorem volterraVekuaTraceRow_zero_origin (E : ℂ) :
    volterraVekuaTraceRow γ E h 0 0 = h 0 := by
  unfold volterraVekuaTraceRow
  rw [tsum_eq_single 0]
  · simp [volterraVekuaTraceRowTerm, physicalVekuaCoeff, volterraPrimitiveIterate]
  · intro j hj
    simp [volterraVekuaTraceRowTerm, hj]

theorem volterraVekuaTraceRow_succ_origin (E : ℂ) (n : ℕ) :
    volterraVekuaTraceRow γ E h (n + 1) 0 = 0 := by
  
  calc
    _ = ∑' _ : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro j
      by_cases hj : j = 0
      · simp [volterraVekuaTraceRowTerm, volterraPrimitiveIterate]
      · simp [volterraVekuaTraceRowTerm, hj]
    _ = 0 := tsum_zero

end

/-- A genuine summable majorant for every term, with factorial decay in
the row index as well as in the series index. -/
theorem exists_volterraVekuaTraceRowTerm_majorant
    {γ h : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (hh : Continuous h) (E : ℂ) :
    ∃ A B r : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ r ∧
      ∀ n j θ, θ ∈ angleInterval →
        ‖volterraVekuaTraceRowTerm γ E h n j θ‖ ≤
          (A * B ^ n / (n.factorial : ℝ)) * (r ^ j / (j.factorial : ℝ)) := by
  have hzero : 0 ∈ angleInterval := ⟨le_rfl, Real.two_pi_pos.le⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn
  obtain ⟨H, hH⟩ := isCompact_Icc.exists_bound_of_continuousOn hh.continuousOn
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hγ.continuous.sub continuous_const).continuousOn
  have hM0  := (norm_nonneg _).trans (hM 0 hzero)
  have hH0  := (norm_nonneg _).trans (hH 0 hzero)
  have hR0  := (norm_nonneg _).trans (hR 0 hzero)
  refine ⟨H, M * anglePeriod, ‖E‖ / 4 * R * (M * anglePeriod),
    hH0, by positivity, by positivity, ?_⟩
  intro n j θ hθ
  exact volterraVekuaTraceRowTerm_bound hγ hh E hM0 hH0 hR0 hM hH hR n j hθ

private theorem volterraVekuaTraceRowTerm_hasDerivAt_succ_succ
    {γ h : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (hh : Continuous h)
    (E : ℂ) (n j : ℕ) (θ : ℝ) :
    HasDerivAt (volterraVekuaTraceRowTerm γ E h (n + 1) (j + 1))
      (conj (deriv γ θ) * volterraVekuaTraceRowTerm γ E h n (j + 1) θ +
        (-E / 4) * deriv γ θ * volterraVekuaTraceRowTerm γ E h (n + 2) j θ) θ := by
  have ha : Continuous (fun s => conj (deriv γ s)) :=
    Complex.continuous_conj.comp hγ.continuous_deriv_one
  have hJ := hasDerivAt_volterraPrimitiveIterate_succ ha hh ((j + 1) + n) θ
  have hprev : ((j + 1) + n) + 1 = (j + 1) + (n + 1) := by omega
  rw [hprev] at hJ
  
  have hidx : (j + 1) + (n + 1) = j + (n + 2) := by omega
  have he : physicalVekuaCoeff E (j + 1) *
      ((((j + 1 : ℕ) : ℂ) * (γ θ - γ 0) ^ j * deriv γ θ) *
          volterraPrimitiveIterate (fun s => conj (deriv γ s)) h (j + (n + 2)) θ +
        (γ θ - γ 0) ^ (j + 1) * (conj (deriv γ θ) *
          volterraPrimitiveIterate (fun s => conj (deriv γ s)) h ((j + 1) + n) θ)) =
      conj (deriv γ θ) * volterraVekuaTraceRowTerm γ E h n (j + 1) θ +
        (-E / 4) * deriv γ θ * volterraVekuaTraceRowTerm γ E h (n + 2) j θ := by
    simp only [volterraVekuaTraceRowTerm]
    calc
      _ = (physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) *
          deriv γ θ * (γ θ - γ 0) ^ j *
            volterraPrimitiveIterate (fun s => conj (deriv γ s)) h (j + (n + 2)) θ +
          conj (deriv γ θ) * (physicalVekuaCoeff E (j + 1) * (γ θ - γ 0) ^ (j + 1) *
            volterraPrimitiveIterate (fun s => conj (deriv γ s)) h ((j + 1) + n) θ) := by
          ring
      _ = _ := by rw [physicalVekuaCoeff_succ]; ring
  convert ((((hγ.differentiable_one θ).hasDerivAt.sub_const (γ 0)).pow (j + 1)).mul hJ).const_mul (physicalVekuaCoeff E (j + 1)) using 1
  · funext x
    simp [volterraVekuaTraceRowTerm] <;> ring
  · simpa [Nat.add_sub_cancel, hidx] using he.symm

/-- The positive row recurrence is the derivative of the actual Volterra
series. A summable derivative majorant justifies the differentiation. -/
theorem volterraVekuaTraceRow_hasDerivAt_succ
    {γ h : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (hh : Continuous h)
    (E : ℂ) (n : ℕ) {θ : ℝ} (hθ : θ ∈ angleInterior) :
    HasDerivAt (volterraVekuaTraceRow γ E h (n + 1))
      ((-E / 4) * deriv γ θ * volterraVekuaTraceRow γ E h (n + 2) θ +
        conj (deriv γ θ) * volterraVekuaTraceRow γ E h n θ) θ := by
  obtain ⟨A, B, r, hA, hB, hr, hbd⟩ := exists_volterraVekuaTraceRowTerm_majorant hγ hh E
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hγ.continuous_deriv_one.continuousOn
  have hM0  := (norm_nonneg _).trans (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  let k  := fun l => A * B ^ l / l.factorial
  
  have hs (l : ℕ) {x : ℝ} (hx : x ∈ angleInterval) :
      Summable (volterraVekuaTraceRowTerm γ E h l · x) := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le ((by norm_num))
      (fun j => hbd l j x hx) ((Real.summable_pow_div_factorial r).mul_left (k l))
  let d  := fun j x =>
    conj (deriv γ x) * volterraVekuaTraceRowTerm γ E h n (j + 1) x +
      (-E / 4) * deriv γ x * volterraVekuaTraceRowTerm γ E h (n + 2) j x
  let u  := fun j =>
    (M * k n * r + ‖-E / 4‖ * M * k (n + 2)) * (r ^ j / j.factorial)
  
  have hd (j : ℕ) (x : ℝ) (_hx : x ∈ angleInterior)  :=
    volterraVekuaTraceRowTerm_hasDerivAt_succ_succ hγ hh E n j x
  have hdb (j : ℕ) (x : ℝ) (hx : x ∈ angleInterior) : ‖d j x‖ ≤ u j := by
    have hxcc := Ioo_subset_Icc_self hx
    have ha : ‖conj (deriv γ x)‖ ≤ M := by simpa only [Complex.norm_conj] using hM x hxcc
    have hfact : (j.factorial : ℝ) ≤ ((j + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega : j ≤ j + 1)
    dsimp only [d]
    calc
      _ ≤ _ := norm_add_le _ _
      _ ≤ M * (k n * (r ^ (j + 1) / (j + 1).factorial)) +
          ‖-E / 4‖ * M * (k (n + 2) * (r ^ j / j.factorial)) := by
        simp only [norm_mul]
        apply add_le_add
        · exact (by bound)
        · exact mul_le_mul ((by bound))
            (hbd (n + 2) j x hxcc) (norm_nonneg _) (by positivity)
      _ ≤ M * (k n * (r ^ (j + 1) / j.factorial)) +
          ‖-E / 4‖ * M * (k (n + 2) * (r ^ j / j.factorial)) := by
        gcongr
      _ = _ := by ring
  have hxcc := Ioo_subset_Icc_self hθ
  have hds := hasDerivAt_tsum_of_isPreconnected ((Real.summable_pow_div_factorial r).mul_left _) isOpen_Ioo (convex_Ioo _ _).isPreconnected
    hd hdb hθ ((summable_nat_add_iff 1).2 (hs (n + 1) hxcc)) hθ
  have ha : Continuous (fun s => conj (deriv γ s)) :=
    Complex.continuous_conj.comp hγ.continuous_deriv_one
  have hd0 : HasDerivAt (volterraVekuaTraceRowTerm γ E h (n + 1) 0)
      (conj (deriv γ θ) * volterraVekuaTraceRowTerm γ E h n 0 θ) θ := by
    convert hasDerivAt_volterraPrimitiveIterate_succ ha hh n θ using 1
    · funext x
      simp [volterraVekuaTraceRowTerm, physicalVekuaCoeff]
    · simp [volterraVekuaTraceRowTerm, physicalVekuaCoeff]
  
  have hder := (hd0.add hds).congr_of_eventuallyEq (by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
    exact (hs (n + 1) (Ioo_subset_Icc_self hx)).tsum_eq_zero_add)
  have hdSum : (∑' j : ℕ, d j θ) =
      conj (deriv γ θ) * (∑' j : ℕ, volterraVekuaTraceRowTerm γ E h n (j + 1) θ) +
        (-E / 4) * deriv γ θ * volterraVekuaTraceRow γ E h (n + 2) θ := by
    dsimp only [d, volterraVekuaTraceRow]
    rw [Summable.tsum_add (((summable_nat_add_iff 1).2 (hs n hxcc)).mul_left _)
      ((hs (n + 2) hxcc).mul_left _), tsum_mul_left, tsum_mul_left]
  apply hder.congr_deriv
  rw [hdSum]
  have hn := (hs n hxcc).tsum_eq_zero_add
  change volterraVekuaTraceRow γ E h n θ = _ at hn
  rw [hn]
  ring

/-- A true conormal kernel gains regularity from NC−I smoothing. -/
theorem normalizedConormal_kernel_raw_H1
    {β a g : ℤ → ℂ} (hβ : IsWL1 halfOrder β)
    (ha : IsWL1 halfOrder a) (hg : IsWL1 halfOrder g)
    (E : ℂ) (b : L2Z) (hb : normalizedConormal hβ ha hg E b = 0) :
    IsSobolevSeq 1 (fromL2 halfOrder b) := by
  have he := congrArg (fun A : FourierOp => A b)
    (normalizedConormal_sub_one_eq hβ ha hg E)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply, hb, zero_sub] at he
  have hr : b = sobolevSmoothing 1 zero_le_one (b - conormalRemOp (by norm_num) hβ ha hg E b) := by
    have h := congrArg Neg.neg he
    simpa only [← map_neg, neg_sub, neg_neg] using h
  rw [hr, fromL2_half_smoothing_one]
  exact (sobNormSq_mono (by norm_num)
    (isSobolevSeq_fromL2 (halfOrder + 1) _)).1

section PhysicalCoordinates

section

variable (Φ : DiskCoordinates) (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 halfOrder b)) (n : ℕ) (θ : ℝ)
include E b Φ

include n θ in
/-- These are actual normalized Vekua traces, reconstructed in ordinary
averaged coordinates. No formal row or derivative is substituted. -/
def DiskCoordinates.vekuaTraceRow : ℂ :=
  hardyFourierTrace (normalizedHardyAverage (Φ.vekuaBoundary E ((Φ.hardyPrimitive ^ n) b))) θ

include hb1 hbn in
/-- Every actual coordinate trace row equals its true interval-integral
series, for the full nonpositive input including frequency zero. -/
theorem localConformalVekuaTraceRow_eq_volterra :
    Φ.vekuaTraceRow E b n θ =
      volterraVekuaTraceRow Φ.boundary E
        (hardyFourierTrace (normalizedHardyAverage b)) n θ := by
  have hpn := localConformalHardyPrimitive_pow_nonpositive Φ Φ.holomorphic b hbn n
  have hp1 := kernel_conormal_primitive_raw_H1 Φ b hb1 n
  have havg : IsSobolevSeq 1 (normalizedHardyAverage b) := isSobolevSeq_smul _ hb1
  have hfun : hardyFourierTrace (normalizedHardyAverage ((Φ.hardyPrimitive ^ n) b)) =
      volterraPrimitiveIterate (fun s => conj (deriv Φ.boundary s))
        (hardyFourierTrace (normalizedHardyAverage b)) n := by
    funext s
    exact localConformalHardyPrimitive_pow_volterra_of_H1 Φ Φ.holomorphic b hbn havg n s
  have hs := localConformalVekuaBoundary_average_volterra_hasSum_of_H1 Φ E ((Φ.hardyPrimitive ^ n) b) hpn hp1 θ
  rw [hfun] at hs
  simp only [starRingEnd_apply] at hs
  change Φ.vekuaTraceRow E b n θ = _
  simpa only [DiskCoordinates.vekuaTraceRow, volterraVekuaTraceRow,
    volterraVekuaTraceRowTerm, physicalCircleTrace, circleMap_zero,
    starRingEnd_apply, Complex.exp_zero, Complex.ofReal_zero, Complex.ofReal_one, zero_add,
    zero_mul, one_mul, mul_one, volterraPrimitiveIterate_iterate] using hs.tsum_eq.symm

theorem localConformalVekuaTraceRow_periodic :
    Function.Periodic
      (Φ.vekuaTraceRow E b n)
      anglePeriod := hardyFourierTrace_periodic _

include hb1 hbn in
/-- Genuine positive-row tangential differentiation of the full-input
physical Vekua traces, proved through their actual Volterra series. -/
theorem localConformalVekuaTraceRow_hasDerivAt_succ {θ : ℝ} (hθ : θ ∈ angleInterior) :
    HasDerivAt
      (Φ.vekuaTraceRow E b (n + 1))
      ((-E / 4) * deriv Φ.boundary θ *
          Φ.vekuaTraceRow E b (n + 2) θ +
        conj (deriv Φ.boundary θ) *
          Φ.vekuaTraceRow E b n θ) θ := by
  have hfun (k : ℕ) :
      Φ.vekuaTraceRow E b k =
        volterraVekuaTraceRow Φ.boundary E
          (hardyFourierTrace (normalizedHardyAverage b)) k := by
    funext x
    exact localConformalVekuaTraceRow_eq_volterra Φ E b hbn hb1 k x
  rw [hfun (n + 1), hfun (n + 2), hfun n]
  have havg : IsSobolevSeq 1 (normalizedHardyAverage b) := isSobolevSeq_smul _ hb1
  exact volterraVekuaTraceRow_hasDerivAt_succ
    Φ.boundaryC1
    (continuous_hardyFourierTrace (sq_tsum_norm_le (s := 0) (by norm_num)
      (by simpa using havg)).1) E n hθ

include hb1 hbn in
/-- The factorial decay is a bound on the actual Vekua trace rows. -/
theorem exists_localConformalVekuaTraceRow_factorial_bound :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ n θ, θ ∈ angleInterval →
        ‖Φ.vekuaTraceRow E b n θ‖ ≤ A * B ^ n / (n.factorial : ℝ)) ∧
      (∀ n, ContinuousOn
        (Φ.vekuaTraceRow E b n) angleInterval) := by
  have hγ  :=
    Φ.boundaryC1
  have havg : IsSobolevSeq 1 (normalizedHardyAverage b) := isSobolevSeq_smul _ hb1
  have hh  :=
    continuous_hardyFourierTrace
      (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using havg)).1
  obtain ⟨A, B, hA, hB, hbd, hc⟩ := exists_volterraVekuaTraceRow_factorial_bound hγ hh E
  refine ⟨A, B, hA, hB, ?_, ?_⟩
  · intro n θ hθ
    rw [localConformalVekuaTraceRow_eq_volterra Φ E b hbn hb1]
    exact hbd n θ hθ
  · intro n
    have heq : Φ.vekuaTraceRow E b n = volterraVekuaTraceRow Φ.boundary E
          (hardyFourierTrace (normalizedHardyAverage b)) n := by
      funext θ
      exact localConformalVekuaTraceRow_eq_volterra Φ E b hbn hb1 n θ
    simp [*]

include hb1 hbn in
theorem localConformalVekuaTraceRow_zero_origin :
    Φ.vekuaTraceRow E b 0 0 = hardyFourierTrace (normalizedHardyAverage b) 0 := by
  rw [localConformalVekuaTraceRow_eq_volterra Φ E b hbn hb1, volterraVekuaTraceRow_zero_origin]

include hb1 hbn in
theorem localConformalVekuaTraceRow_succ_origin :
    Φ.vekuaTraceRow E b (n + 1) 0 = 0 := by
  rw [localConformalVekuaTraceRow_eq_volterra Φ E b hbn hb1, volterraVekuaTraceRow_succ_origin]

end

section

variable (Φ : DiskCoordinates) (E : ℝ) (hE : 0 ≤ E) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (hb1 : IsSobolevSeq 1 (fromL2 halfOrder b)) (n : ℕ)
    (θ : ℝ)

include E b n Φ θ in
/-- Physical transport coordinates retain y₀=U₀/√2 and yₙ=qⁿUₙ. -/
def DiskCoordinates.vekuaTransportCoordinate : ℂ :=
  if n = 0 then
    Φ.vekuaTraceRow (E : ℂ) b 0 θ / vacuumWeight
  else physicalDrivenQ E ^ n *
    Φ.vekuaTraceRow (E : ℂ) b n θ

include hb1 hbn in
/-- Genuine factorial majorants for the scaled Ell² coordinates. -/
theorem exists_localConformalVekuaTransportCoordinate_factorial_bound :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ n θ, θ ∈ angleInterval →
        ‖Φ.vekuaTransportCoordinate E b n θ‖ ≤ A * B ^ n / (n.factorial : ℝ)) ∧
      (∀ n, ContinuousOn
        (Φ.vekuaTransportCoordinate E b n) angleInterval) := by
  obtain ⟨A, B, hA, hB, hbd, hc⟩ := exists_localConformalVekuaTraceRow_factorial_bound
    Φ (E : ℂ) b hbn hb1
  refine ⟨A, ‖physicalDrivenQ E‖ * B, hA, mul_nonneg (norm_nonneg _) hB, ?_, ?_⟩
  · intro n θ hθ
    by_cases hn : n = 0
    · subst n
      simp only [DiskCoordinates.vekuaTransportCoordinate, if_true, pow_zero,
        Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
      have hs : (0 : ℝ) < Real.sqrt 2 := (by positivity)
      have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := by
        simp
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
      apply (div_le_iff₀ hs).2
      have hb0 : ‖Φ.vekuaTraceRow (E : ℂ) b 0 θ‖ ≤ A := by simpa using hbd 0 θ hθ
      nlinarith
    · rw [DiskCoordinates.vekuaTransportCoordinate, if_neg hn, norm_mul, norm_pow]
      calc
        _ ≤ ‖physicalDrivenQ E‖ ^ n * (A * B ^ n / n.factorial) :=
          (by bound)
        _ = _ := by ring
  · intro n
    unfold DiskCoordinates.vekuaTransportCoordinate
    by_cases hn : n = 0
    · simp [hn]
      exact (hc 0).div_const _
    · simp [hn]
      fun_prop

include hb1 hbn in
/-- The coordinates form a genuinely absolutely summable sequence. -/
theorem summable_norm_localConformalVekuaTransportCoordinate
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    Summable (fun n : ℕ => ‖Φ.vekuaTransportCoordinate E b n θ‖) := by
  obtain ⟨A, B, hA, hB, hbd, hc⟩ := exists_localConformalVekuaTransportCoordinate_factorial_bound
    Φ E b hbn hb1
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hbd n θ hθ)
    (summable_volterraPrimitive_majorant A B)

include E b Φ θ in
/-- An actual Ell² vector, synthesized from the true coordinate traces. -/
def DiskCoordinates.vekuaTransportVector : Ell2 :=
  ∑' n : ℕ, Φ.vekuaTransportCoordinate E b n θ • basisVec n

private theorem vekuaTransport_norm_basisVec : ‖basisVec n‖ = 1 := by
  simp [basisVec]

include hb1 hbn in
theorem localConformalVekuaTransportVector_hasSum
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    HasSum (fun n : ℕ => Φ.vekuaTransportCoordinate E b n θ • basisVec n)
      (Φ.vekuaTransportVector E b θ) := by
  apply Summable.hasSum
  apply Summable.of_norm
  simpa [norm_smul, vekuaTransport_norm_basisVec] using summable_norm_localConformalVekuaTransportCoordinate Φ E b hbn hb1 hθ

include hb1 hbn in
/-- Every coordinate of the actual Ell² synthesis is the intended row. -/
theorem localConformalVekuaTransportVector_coord
    {θ : ℝ} (hθ : θ ∈ angleInterval) (n : ℕ) :
    (Φ.vekuaTransportVector E b θ : ℕ → ℂ) n =
      Φ.vekuaTransportCoordinate E b n θ := by
  have hs := (localConformalVekuaTransportVector_hasSum Φ E b hbn hb1 hθ).summable
  have hm := (innerSL ℂ (basisVec n)).map_tsum hs
  simp only [innerSL_apply_apply, inner_smul_right, inner_basisVec, basisVec_coord,
    mul_ite, mul_one, mul_zero] at hm
  let c  := fun z => Φ.vekuaTransportCoordinate E b z θ
  have hsum : (∑' z : ℕ, if n = z then c z else 0) = c n := by
    simp
  have hm' := hm
  exact hm'.trans hsum

include hb1 hbn in
theorem localConformalVekuaTransportVector_continuousOn :
    ContinuousOn (Φ.vekuaTransportVector E b) angleInterval := by
  obtain ⟨A, B, hA, hB, hbd, hc⟩ := exists_localConformalVekuaTransportCoordinate_factorial_bound
    Φ E b hbn hb1
  have hu : HasSumUniformlyOn
      (fun n θ => Φ.vekuaTransportCoordinate E b n θ • basisVec n)
      (Φ.vekuaTransportVector E b)
      angleInterval := by
    apply HasSumUniformlyOn.of_norm_le_summable (summable_volterraPrimitive_majorant A B)
    intro n θ hθ
    simpa [norm_smul, vekuaTransport_norm_basisVec] using hbd n θ hθ
  apply hu.tendstoUniformlyOn.continuousOn
  refine (Eventually.of_forall fun s : Finset ℕ => ?_).frequently
  apply continuousOn_finset_sum s
  fun_prop

theorem localConformalVekuaTransportVector_periodic :
    Function.Periodic (Φ.vekuaTransportVector E b) anglePeriod := by
  intro θ
  apply tsum_congr
  intro n
  unfold DiskCoordinates.vekuaTransportCoordinate
  rw [localConformalVekuaTraceRow_periodic Φ (E : ℂ) b 0 θ,
    localConformalVekuaTraceRow_periodic Φ (E : ℂ) b n θ]

include hb1 hbn in
/-- The initial datum is proved from the actual zero-origin primitives. -/
theorem localConformalVekuaTransportVector_origin :
    Φ.vekuaTransportVector E b 0 =
      (hardyFourierTrace (normalizedHardyAverage b) 0 / vacuumWeight) • basisVec 0 := by
  apply lp.ext
  funext n
  rw [localConformalVekuaTransportVector_coord Φ E b hbn hb1 ⟨le_rfl, Real.two_pi_pos.le⟩]
  cases n with
  | zero =>
      simp only [DiskCoordinates.vekuaTransportCoordinate, if_true,
        localConformalVekuaTraceRow_zero_origin Φ (E : ℂ) b hbn hb1,
        lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, basisVec_coord, if_true, mul_one]
  | succ n =>
      simp only [DiskCoordinates.vekuaTransportCoordinate, Nat.succ_ne_zero, if_false,
        localConformalVekuaTraceRow_succ_origin Φ (E : ℂ) b hbn hb1, mul_zero,
        lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, basisVec_coord, if_false]

include E b n Φ θ in
/-- The true derivative of positive coordinate n+1. It is not an assumed
transport coefficient: it comes from the scalar Volterra recurrence. -/
def DiskCoordinates.vekuaPositiveTransportDerivative : ℂ :=
  physicalDrivenQ E ^ (n + 1) *
    ((-(E : ℂ) / 4) * deriv Φ.boundary θ *
        Φ.vekuaTraceRow (E : ℂ) b (n + 2) θ +
      conj (deriv Φ.boundary θ) *
        Φ.vekuaTraceRow (E : ℂ) b n θ)

include hb1 hbn in
theorem localConformalVekuaTransportCoordinate_hasDerivAt_succ {θ : ℝ} (hθ : θ ∈ angleInterior) :
    HasDerivAt
      (Φ.vekuaTransportCoordinate E b (n + 1))
      (Φ.vekuaPositiveTransportDerivative E b n θ) θ := by
  exact (localConformalVekuaTraceRow_hasDerivAt_succ Φ (E : ℂ) b hbn hb1 n hθ).const_mul (physicalDrivenQ E ^ (n + 1))

include hb1 hbn in
/-- The actual positive derivatives also have a genuine summable
factorial majorant, uniformly on the entire closed parameter interval. -/
theorem exists_localConformalVekuaPositiveTransportDerivative_majorant :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n θ, θ ∈ angleInterval →
      ‖Φ.vekuaPositiveTransportDerivative E b n θ‖ ≤ u n := by
  obtain ⟨A, B, hA, hB, hbd, hc⟩ := exists_localConformalVekuaTraceRow_factorial_bound
    Φ (E : ℂ) b hbn hb1
  have hΓ  :=
    Φ.boundaryC1
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hΓ.continuous_deriv_one.continuousOn
  have hM0  := (norm_nonneg _).trans (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  let D := ‖physicalDrivenQ E‖ * A * M * (‖-(E : ℂ) / 4‖ * B ^ 2 + 1)
  let r := ‖physicalDrivenQ E‖ * B
  refine ⟨fun n => D * r ^ n / n.factorial,
    summable_volterraPrimitive_majorant D r, ?_⟩
  intro n θ hθ
  have hfact : (n.factorial : ℝ) ≤ ((n + 2).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ n + 2)
  simp only [DiskCoordinates.vekuaPositiveTransportDerivative, norm_mul, norm_pow]
  calc
    _ ≤ ‖physicalDrivenQ E‖ ^ (n + 1) *
        (‖(-(E : ℂ) / 4) * deriv Φ.boundary θ *
            Φ.vekuaTraceRow (E : ℂ) b (n + 2) θ‖ +
          ‖conj (deriv Φ.boundary θ) *
            Φ.vekuaTraceRow (E : ℂ) b n θ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ ‖physicalDrivenQ E‖ ^ (n + 1) *
        (‖-(E : ℂ) / 4‖ * M * (A * B ^ (n + 2) / (n + 2).factorial) +
          M * (A * B ^ n / n.factorial)) := by
      simp only [norm_mul, Complex.norm_conj]
      apply mul_le_mul_of_nonneg_left
      · apply add_le_add
        · calc
            _
                ≤ ‖-(E : ℂ) / 4‖ * M *
                    ‖Φ.vekuaTraceRow (E : ℂ) b (n + 2) θ‖ := mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left (hM θ hθ) (norm_nonneg _))
                    (norm_nonneg _)
            _ ≤ _ := mul_le_mul_of_nonneg_left (hbd (n + 2) θ hθ)
                    (mul_nonneg (norm_nonneg _) hM0)
        · calc
            _
                ≤ M * ‖Φ.vekuaTraceRow (E : ℂ) b n θ‖ := mul_le_mul_of_nonneg_right (hM θ hθ) (norm_nonneg _)
            _ ≤ _ := mul_le_mul_of_nonneg_left (hbd n θ hθ) hM0
      · positivity
    _ ≤ ‖physicalDrivenQ E‖ ^ (n + 1) *
        (‖-(E : ℂ) / 4‖ * M * (A * B ^ (n + 2) / n.factorial) +
          M * (A * B ^ n / n.factorial)) := by
      gcongr
    _ = _ := by
      ring

include E b Φ θ in
/-- The positive part is a genuine Ell² series of the actual traces. -/
def DiskCoordinates.vekuaPositiveTransportVector : Ell2 :=
  ∑' n : ℕ, Φ.vekuaTransportCoordinate E b (n + 1) θ • basisVec (n + 1)

include hb1 hbn in
/-- Separating the exceptional zeroth row is justified by actual
absolute convergence, rather than by a formal rearrangement. -/
theorem localConformalVekuaTransportVector_zero_add_positive
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    Φ.vekuaTransportVector E b θ =
      Φ.vekuaTransportCoordinate E b 0 θ • basisVec 0 +
        Φ.vekuaPositiveTransportVector E b θ :=
  (localConformalVekuaTransportVector_hasSum Φ E b hbn hb1 hθ).summable.tsum_eq_zero_add

include hb1 hbn in
/-- Genuine Hilbert-space differentiation of the whole positive part.
Both the row and derivative series are justified by summable majorants. -/
theorem localConformalVekuaPositiveTransportVector_hasDerivAt
    {θ : ℝ} (hθ : θ ∈ angleInterior) :
    HasDerivAt
      (Φ.vekuaPositiveTransportVector E b)
      (∑' n : ℕ, Φ.vekuaPositiveTransportDerivative E b n θ • basisVec (n + 1)) θ := by
  obtain ⟨u, hu, hbd⟩ := exists_localConformalVekuaPositiveTransportDerivative_majorant
    Φ E b hbn hb1
  have hg (n : ℕ) (x : ℝ) (hx : x ∈ angleInterior) :
      HasDerivAt
        (fun t => Φ.vekuaTransportCoordinate E b (n + 1) t • basisVec (n + 1))
        (Φ.vekuaPositiveTransportDerivative E b n x • basisVec (n + 1)) x :=
    (localConformalVekuaTransportCoordinate_hasDerivAt_succ Φ E b hbn hb1 n hx).smul_const _
  have hgb (n : ℕ) (x : ℝ) (hx : x ∈ angleInterior) :
      ‖Φ.vekuaPositiveTransportDerivative E b n x • basisVec (n + 1)‖ ≤ u n := by
    simpa only [norm_smul, vekuaTransport_norm_basisVec, mul_one] using
      hbd n x (Ioo_subset_Icc_self hx)
  have hs := (localConformalVekuaTransportVector_hasSum Φ E b hbn hb1 (Ioo_subset_Icc_self hθ)).summable
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo _ _).isPreconnected
    hg hgb hθ ((summable_nat_add_iff 1).2 hs) hθ

include hE hb1 hbn in
/-- The computed positive derivative has exactly the corresponding
coordinate of the original physical transport coefficient. -/
theorem localConformalVekuaPositiveTransportDerivative_eq_transportCoeff_coord {θ : ℝ} (hθ : θ ∈ angleInterval) :
    Φ.vekuaPositiveTransportDerivative E b n θ =
      (transportCoeff Φ.boundary E θ
        (Φ.vekuaTransportVector E b θ) : ℕ → ℂ) (n + 1) := by
  rw [transportCoeff_apply_coord, shiftN_apply_succ,
    localConformalVekuaTransportVector_coord Φ E b hbn hb1 hθ (n + 2),
    localConformalVekuaTransportVector_coord Φ E b hbn hb1 hθ n]
  change _ = physicalDrivenQ E * _
  unfold DiskCoordinates.vekuaPositiveTransportDerivative
  rw [← physicalDrivenQ_sq hE]
  cases n with
  | zero =>
      have hs0 : vacuumWeight ≠ 0 := by
        simp
      simp only [DiskCoordinates.vekuaTransportCoordinate, shiftWeight, if_true,
        Nat.succ_ne_zero, if_false, one_mul, pow_one]
      field_simp [hs0]
      <;> ring
  | succ n =>
      simp [DiskCoordinates.vekuaTransportCoordinate, shiftWeight, Nat.succ_ne_zero, if_false, pow_succ, pow_zero] <;> ring

include hb1 hbn in
/-- Actual absolute convergence of the positive Hilbert derivative. -/
theorem summable_localConformalVekuaPositiveTransportDerivative
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    Summable (fun n : ℕ =>
      Φ.vekuaPositiveTransportDerivative E b n θ • basisVec (n + 1)) := by
  obtain ⟨u, hu, hbd⟩ := exists_localConformalVekuaPositiveTransportDerivative_majorant
    Φ E b hbn hb1
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le ((by norm_num)) _ hu
  intro n
  simpa [norm_smul, vekuaTransport_norm_basisVec] using hbd n θ hθ

include hE hb1 hbn in
/-- The positive derivative is the genuine physical transport term with
its exceptional zeroth coordinate removed. -/
theorem localConformalVekuaPositiveTransportDerivative_tsum_eq {θ : ℝ} (hθ : θ ∈ angleInterval) :
    (∑' n : ℕ, Φ.vekuaPositiveTransportDerivative E b n θ • basisVec (n + 1)) =
      transportCoeff Φ.boundary E θ
          (Φ.vekuaTransportVector E b θ) -
        ((transportCoeff Φ.boundary E θ
          (Φ.vekuaTransportVector E b θ) : ℕ → ℂ) 0) • basisVec 0 := by
  have hs := summable_localConformalVekuaPositiveTransportDerivative Φ E b hbn hb1 hθ
  apply lp.ext
  funext n
  have hm := (innerSL ℂ (basisVec n)).map_tsum hs
  simp only [innerSL_apply_apply, inner_smul_right, inner_basisVec, basisVec_coord,
    mul_ite, mul_one, mul_zero] at hm
  rw [hm]
  cases n with
  | zero =>
      simp only [Nat.succ_ne_zero, Nat.zero_ne_add_one, if_false, tsum_zero,
        lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        basisVec_coord, if_true, mul_one, sub_self]
  | succ n =>
      simp only [Nat.succ_inj, Nat.add_right_cancel_iff,
        lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        basisVec_coord, Nat.succ_ne_zero, if_false, mul_zero, sub_zero]
      let c  := fun z => Φ.vekuaPositiveTransportDerivative E b z θ
      have hsum : (∑' z : ℕ, if n = z then c z else 0) = c n := by
        simp
      calc
        _ = c n := hsum
        _ = _ := localConformalVekuaPositiveTransportDerivative_eq_transportCoeff_coord
          Φ E hE b hbn hb1 n hθ

end

/-- Kernel inputs obtain the regularity needed by the actual transport
construction from the proved normalized-conormal smoothing formula. -/
theorem localConformalVekuaConormal_kernel_raw_H1 (Φ : SmoothDiskMap) (E : ℂ) (b : L2Z)
    (hker : Φ.conormal E b = 0) :
    IsSobolevSeq 1 (fromL2 halfOrder b) :=
  normalizedConormal_kernel_raw_H1 (localConformalVelocityCircle_isWL1_half Φ) (localConformalHardyPrimitiveMultiplier_isWL1 Φ) (localConformalCenteredCircle_isWL1_half Φ) E b hker

section

variable (Φ : DiskCoordinates) (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
include hbn

theorem localConformalVekuaTraceRow_continuous (hb1 : IsSobolevSeq 1 (fromL2 halfOrder b))
    (n : ℕ) :
    Continuous (Φ.vekuaTraceRow E b n) := by
  have hp1 := kernel_conormal_primitive_raw_H1 Φ b hb1 n
  have hpn := localConformalHardyPrimitive_pow_nonpositive Φ Φ.holomorphic b hbn n
  have hr := localConformalVekuaBoundary_raw_H1 Φ E ((Φ.hardyPrimitive ^ n) b) hpn hp1
  have havg0 := isSobolevSeq_smul fourierScale⁻¹ hr
  have havg : IsSobolevSeq 1 (normalizedHardyAverage (Φ.vekuaBoundary E ((Φ.hardyPrimitive ^ n) b))) := by
    exact havg0
  exact continuous_hardyFourierTrace (sq_tsum_norm_le (s := 0) (by norm_num)
    (by simpa using havg)).1

/-- The actual conormal kernel determines the exceptional zeroth-row
derivative. Fourier inversion is applied to two genuine continuous
periodic functions; no differentiability of this row is assumed. -/
theorem localConformalVekuaConormal_kernel_hasDerivAt_zero
    (hker : Φ.conormal E b = 0)
    (θ : ℝ) :
    HasDerivAt
      (Φ.vekuaTraceRow E b 0)
      (2 * (-E / 4) * deriv Φ.boundary θ *
        Φ.vekuaTraceRow E b 1 θ) θ := by
  have hb1 := localConformalVekuaConormal_kernel_raw_H1 Φ E b hker
  let v  := Φ.vekuaTraceRow E b 0
  let d  := fun t => 2 * (-E / 4) * deriv Φ.boundary t *
    Φ.vekuaTraceRow E b 1 t
  have hv  := localConformalVekuaTraceRow_continuous Φ E b hbn hb1 0
  have hΓ  :=
    Φ.boundaryC1
  have hd : Continuous d :=
    (continuous_const.mul hΓ.continuous_deriv_one).mul
      (localConformalVekuaTraceRow_continuous Φ E b hbn hb1 1)
  have hvper  :=
    localConformalVekuaTraceRow_periodic Φ E b 0
  have hdper : Function.Periodic d anglePeriod := by
    intro t
    dsimp only [d]
    rw [deriv_periodic Φ.periodic_boundary,
      localConformalVekuaTraceRow_periodic Φ E b 1]
  let TF := Φ.pulledBackTrace Φ.lipschitzDomain
  let VF := Φ.vekuaH1
  let Vel := boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)
  let G  := Vel (TF (VF (Φ.map 1) E (Φ.hardyPrimitive b)))
  let L  := (2 * (-E / 4)) • G
  have hJbn := localConformalHardyPrimitive_nonpositive Φ Φ.holomorphic b hbn
  have hJ1 := kernel_conormal_primitive_raw_H1 Φ b hb1 1
  have ht0 : (TF (VF (Φ.map 1) E b) : ℝ → ℂ)
      =ᵐ[angleMeasure] v := by
    exact localConformalVekua_coordinate_trace_reconstruction_ae Φ E b hbn hb1
  have ht1 := localConformalVekua_coordinate_trace_reconstruction_ae Φ E (Φ.hardyPrimitive b) hJbn hJ1
  have hLae : (L : ℝ → ℂ) =ᵐ[angleMeasure] d := by
    filter_upwards [Lp.coeFn_smul (2 * (-E / 4)) G,
      boundaryContinuousMultiplier_ae (localConformalVelocityCircle Φ.map) (TF (VF (Φ.map 1) E (Φ.hardyPrimitive b))),
      ht1] with t Φ.lipschitzDomain hG ht
    rw [Φ.lipschitzDomain]
    simp only [Pi.smul_apply, smul_eq_mul, G, Vel, TF, VF, hG, ht,
      localConformalVelocityCircle_apply Φ, d, DiskCoordinates.vekuaTraceRow, pow_one]
    ring
  have hc (n : ℤ) : angleCoeff d n =
      (Complex.I * (n : ℂ)) * angleCoeff v n := by
    have hNC := localConformalVekua_normalizedConormal_fourier Φ E b hbn hb1 n
    simp only [hker, lp.coeFn_zero, Pi.zero_apply, localConformalVekuaGradientA_apply,
      map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hNC
    have hw : (((sobWeight n ^ (-halfOrder) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos (sobWeight_pos n) (-halfOrder)).ne'
    have hn  :=
      (mul_eq_zero.mp hNC.symm).resolve_left hw
    have hs0 : fourierScale ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
    apply mul_left_cancel₀ hs0
    calc
      _ = boundaryFourier L n := (kernel_conormal_coeff_ae L hLae n).symm
      _ = (Complex.I * (n : ℂ)) * boundaryFourier (TF (VF (Φ.map 1) E b)) n := by
        simp only [L, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        have h2 := (sub_eq_zero.mp hn).symm
        have hrel : 2 * (-E / 4) * boundaryFourier G n =
            Complex.I * (n : ℂ) * boundaryFourier (TF (VF (Φ.map 1) E b)) n := by
          have hI : Complex.I ^ 2 = (-1 : ℂ) := by norm_num
          calc
            _ = -(Complex.I * (2 * Complex.I * ((-E / 4) * boundaryFourier G n))) := by
              have hassoc : Complex.I *
                  (2 * Complex.I * ((-E / 4) * boundaryFourier G n)) =
                  2 * Complex.I ^ 2 * ((-E / 4) * boundaryFourier G n) := by ring
              rw [hassoc, hI]
              ring
            _ = -(Complex.I * (-(n : ℂ) * boundaryFourier (TF (VF (Φ.map 1) E b)) n)) := by
              rw [h2]
            _ = _ := by ring
        rw [hrel]
      _ = _ := by
        rw [kernel_conormal_coeff_ae _ ht0]
        ring
  exact hasDerivAt_of_periodic_fourier_derivative hv hd hvper hdper hc θ

end

section

variable (Φ : DiskCoordinates) (E : ℝ) (hE : 0 ≤ E) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (hker : Φ.conormal (E : ℂ) b = 0)
include hE

include hbn hker in
/-- The conormal-kernel rows solve the genuine homogeneous Ell² ODE.
The exceptional sqrt(2) scale is checked against its actual transport
coefficient, and all other derivatives are genuine Hilbert series. -/
theorem localConformalVekuaConormal_kernel_transport_hasDerivAt
    {θ : ℝ} (hθ : θ ∈ angleInterior) :
    HasDerivAt
      (Φ.vekuaTransportVector E b)
      (transportCoeff Φ.boundary E θ
        (Φ.vekuaTransportVector E b θ)) θ := by
  have hb1 := localConformalVekuaConormal_kernel_raw_H1 Φ (E : ℂ) b hker
  have hxcc := Ioo_subset_Icc_self hθ
  have hd0 : HasDerivAt
      (Φ.vekuaTransportCoordinate E b 0)
      ((2 * (-(E : ℂ) / 4) * deriv Φ.boundary θ *
        Φ.vekuaTraceRow (E : ℂ) b 1 θ) / vacuumWeight) θ := by
    exact (localConformalVekuaConormal_kernel_hasDerivAt_zero Φ (E : ℂ) b hbn hker θ).div_const vacuumWeight
  have he0 : ((2 * (-(E : ℂ) / 4) * deriv Φ.boundary θ *
        Φ.vekuaTraceRow (E : ℂ) b 1 θ) / vacuumWeight) =
      (transportCoeff Φ.boundary E θ
        (Φ.vekuaTransportVector E b θ) : ℕ → ℂ) 0 := by
    rw [transportCoeff_coord_zero,
      localConformalVekuaTransportVector_coord Φ E b hbn hb1 hxcc 1]
    simp only [DiskCoordinates.vekuaTransportCoordinate, if_false, Nat.one_ne_zero, pow_one]
    change _ = physicalDrivenQ E * _
    rw [← physicalDrivenQ_sq hE]
    have hs : vacuumWeight ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hs0 : vacuumWeight ≠ 0 := by
      simp
    field_simp [hs0]
    linear_combination -(physicalDrivenQ E ^ 2 * deriv Φ.boundary θ *
      Φ.vekuaTraceRow (E : ℂ) b 1 θ) * hs
  have hdp := (localConformalVekuaPositiveTransportVector_hasDerivAt Φ E b hbn hb1 hθ).congr_deriv
      (localConformalVekuaPositiveTransportDerivative_tsum_eq Φ E hE b hbn hb1 hxcc)
  have heq : Φ.vekuaTransportVector E b =ᶠ[𝓝 θ]
      fun x => Φ.vekuaTransportCoordinate E b 0 x • basisVec 0 +
        Φ.vekuaPositiveTransportVector E b x := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
    exact localConformalVekuaTransportVector_zero_add_positive Φ E b hbn hb1 (Ioo_subset_Icc_self hx)
  apply ((((hd0.congr_deriv he0).smul_const (basisVec 0)).add hdp).congr_of_eventuallyEq heq).congr_deriv
  abel

include hbn hker in
/-- The genuine pointwise Hilbert ODE gives its actual integral equation
on the full closed interval, including both endpoint values. -/
theorem localConformalVekuaConormal_kernel_transport_integral_eq
    {θ : ℝ} (hθ : θ ∈ angleInterval) :
    Φ.vekuaTransportVector E b θ =
      Φ.vekuaTransportVector E b 0 +
        ∫ s in (0 : ℝ)..θ, transportCoeff Φ.boundary E s
          (Φ.vekuaTransportVector E b s) := by
  have hb1 := localConformalVekuaConormal_kernel_raw_H1 Φ (E : ℂ) b hker
  have hy := localConformalVekuaTransportVector_continuousOn Φ E b hbn hb1
  have hΓ  :=
    Φ.boundaryC1
  
  have hc : Continuous (transportCoeff Φ.boundary E) := by
    unfold transportCoeff
    fun_prop
  have hsub : Icc 0 θ ⊆ angleInterval := Icc_subset_Icc le_rfl hθ.2
  have hg := hc.continuousOn.clm_apply hy
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.1 (hy.mono hsub)
    (fun s hs => localConformalVekuaConormal_kernel_transport_hasDerivAt Φ E hE b hbn hker ⟨hs.1, hs.2.trans_le hθ.2⟩)
    (by rw [← uIcc_of_le hθ.1] at hsub; exact (hg.mono hsub).intervalIntegrable)
  simpa [add_comm] using sub_eq_iff_eq_add.mp hi.symm

include hbn hker in
/-- Genuine variation of constants for a conormal-kernel input. The
boundary vector is the actual transport applied to its proved datum. -/
theorem localConformalVekuaConormal_kernel_transport_eq
    {W : TransportPath} (hW : IsTransport Φ.boundary E W) {θ : ℝ}
    (hθ : θ ∈ angleInterval) :
    Φ.vekuaTransportVector E b θ =
      W θ (Φ.vekuaTransportVector E b 0) := by
  have hb1 := localConformalVekuaConormal_kernel_raw_H1 Φ (E : ℂ) b hker
  obtain ⟨M, hM⟩ := exists_periodic_C1_density_lipschitz Φ.boundary
    Φ.boundaryC1
    Φ.periodic_boundary
  have hd := driven_eq_transport hM hW
    (continuous_const.aestronglyMeasurable : AEStronglyMeasurable (fun _ : ℝ => (0 : Ell2)) volume)
    (B := 0) (fun _ => by simp)
    (localConformalVekuaTransportVector_continuousOn Φ E b hbn hb1)
    (fun t ht => by
      simpa only [add_zero] using
        (localConformalVekuaConormal_kernel_transport_integral_eq Φ E hE b hbn hker (θ := t) ht)) θ hθ
  simpa using hd

include hbn hker in
/-- A true nonzero basepoint cut rules out the conormal kernel at a
reference energy, even when that energy belongs to the original Neumann
spectrum. The proof uses the actual endpoint and the genuine Hilbert ODE. -/
theorem localConformalVekuaConormal_eq_zero_imp_of_cutC_ne_zero
    {W : TransportPath} (hW : IsTransport Φ.boundary E W)
    (hcut : cutVector W ≠ 0) : b = 0 := by
  have hb1 := localConformalVekuaConormal_kernel_raw_H1 Φ (E : ℂ) b hker
  let s  := hardyFourierTrace (normalizedHardyAverage b) 0 / vacuumWeight
  let y := Φ.vekuaTransportVector E b
  have hinit : y 0 = s • basisVec 0 :=
    localConformalVekuaTransportVector_origin Φ E b hbn hb1
  have hper : y anglePeriod = y 0 := by
    simpa only [zero_add] using localConformalVekuaTransportVector_periodic Φ E b 0
  have hT : anglePeriod ∈ angleInterval := ⟨Real.two_pi_pos.le, le_rfl⟩
  have hform := localConformalVekuaConormal_kernel_transport_eq Φ E hE b hbn hker hW hT
  change y anglePeriod = W anglePeriod (y 0) at hform
  rw [hper, hinit] at hform
  obtain ⟨M, hM⟩ := exists_periodic_C1_density_lipschitz Φ.boundary
    Φ.boundaryC1
    Φ.periodic_boundary
  have hu : ContinuousLinearMap.adjoint (W anglePeriod) * W anglePeriod = 1 := by
    have hm := transport_mem_unitary hM hW hT
    exact hm.1
  have hadj := congrArg (ContinuousLinearMap.adjoint (W anglePeriod)) hform
  
  rw [map_smul, ← ContinuousLinearMap.mul_apply, hu, ContinuousLinearMap.one_apply] at hadj
  have hscut : s • cutVector W = 0 := by
    simpa only [cutC, smul_sub, sub_eq_zero] using hadj
  have hs  := (smul_eq_zero.mp hscut).resolve_right hcut
  have hinit0 : y 0 = 0 := by simp [*]
  have hyzero {t : ℝ} (ht : t ∈ angleInterval) : y t = 0 := by
    have he := localConformalVekuaConormal_kernel_transport_eq Φ E hE b hbn hker hW ht
    change y t = W t (y 0) at he
    simpa [hinit0, map_zero] using he
  
  have hrowzero {t : ℝ} (ht : t ∈ angleInterval) :
      Φ.vekuaTraceRow (E : ℂ) b 0 t = 0 := by
    have he := localConformalVekuaTransportVector_coord Φ E b hbn hb1 ht 0
    change (y t : ℕ → ℂ) 0 = _ at he
    rw [hyzero ht] at he
    simp only [lp.coeFn_zero, Pi.zero_apply, DiskCoordinates.vekuaTransportCoordinate, if_true] at he
    have hh := congrArg (fun z : ℂ => z * vacuumWeight) he.symm
    simpa using hh
  apply localConformalVekuaH1_eq_zero_input_of_coordinate_trace_zero Φ (E : ℂ) b hbn
  apply Lp.ext
  filter_upwards [localConformalVekua_coordinate_trace_reconstruction_ae Φ (E : ℂ) b hbn hb1,
    ae_restrict_mem measurableSet_Ioc,
    Lp.coeFn_zero ℂ 2 angleMeasure] with t ht hmem hzero
  simp only [DiskCoordinates.vekuaH1AtBoundaryOrigin]
  rw [ht]
  
  exact (hrowzero (Ioc_subset_Icc_self hmem)).trans hzero.symm

/-- Reference-energy injectivity on the original full nonpositive space,
obtained from a genuine nonzero cut, without a nonresonance premise. -/
theorem localConformalVekuaConormal_injective_on_nonpositive_of_cutC_ne_zero {W : TransportPath} (hW : IsTransport Φ.boundary E W)
    (hcut : cutVector W ≠ 0) :
    InjOn (Φ.conormal (E : ℂ))
      {b : L2Z | IsNonpositiveFourierSupport b} := by
  intro b hb' d hd' hbd
  have hn : IsNonpositiveFourierSupport (b - d) := by
    intro n hn
    simp [hb' n hn, hd' n hn]
  have hzero : Φ.conormal (E : ℂ) (b - d) = 0 := by
    simp [hbd, sub_self]
  exact sub_eq_zero.mp
    (localConformalVekuaConormal_eq_zero_imp_of_cutC_ne_zero Φ E hE (b - d) hn hzero hW hcut)

end

end PhysicalCoordinates

end PolyaNeumann

end
