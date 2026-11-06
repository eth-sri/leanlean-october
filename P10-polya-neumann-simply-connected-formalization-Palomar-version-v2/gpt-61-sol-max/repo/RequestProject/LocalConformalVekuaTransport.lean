module

public import RequestProject.PlanarTypes

public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

public import RequestProject.PhysicalDrivenRowsReconstruction
public import RequestProject.LocalConformalVekuaConormalBridge
public import RequestProject.NeumannResonanceDimension
public import RequestProject.LocalConformalHardySubspace
public import RequestProject.PhysicalDrivenHardyRegularity
public import RequestProject.PhysicalDrivenKernelConormal
public import RequestProject.PeriodicFourierDerivative
public import RequestProject.LocalConformalBoundaryLipschitz
public import Mathlib.Analysis.Calculus.SmoothSeries

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

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Filter Metric
open scoped Topology ComplexConjugate



/-- The actual interval-integral series defining row n of a Vekua trace. -/
def volterraVekuaTraceRowTerm γ E h
    n j θ  :=
  physicalVekuaCoeff E j * (γ θ - γ 0) ^ j *
    volterraPrimitiveIterate (fun s => conj (deriv γ s)) h (j + n) θ

def volterraVekuaTraceRow γ E h
    n θ  :=
  ∑' j : ℕ, volterraVekuaTraceRowTerm γ E h n j θ

private theorem transport_norm_physicalVekuaCoeff E j :
    ‖physicalVekuaCoeff E j‖ = (‖E‖ / 4) ^ j / (j.factorial : ℝ) := by
  simp_all [physicalVekuaCoeff]

section
variable {γ h : ComplexCurve} (hγ : ContDiff ℝ 1 γ) (hh : Continuous h) (E : ℂ)
local notation "volterraVekuaTraceRowFixed" => volterraVekuaTraceRow γ E h

local notation "volterraVekuaTraceRowTermFixed" => volterraVekuaTraceRowTerm γ E h


section
include γ h hγ hh E

private theorem volterraVekuaTraceRowTerm_bound
     (hM0 : 0 ≤ M) (hH0 : 0 ≤ H) (hR0 : 0 ≤ R)
    (hM : ∀ θ ∈ boundaryInterval, ‖conj (deriv γ θ)‖ ≤ M)
    (hH : ∀ θ ∈ boundaryInterval, ‖h θ‖ ≤ H)
    (hR : ∀ θ ∈ boundaryInterval, ‖γ θ - γ 0‖ ≤ R)
    n j  (hθ : θ ∈ boundaryInterval) :
    ‖volterraVekuaTraceRowTermFixed n j θ‖ ≤
      (H * (M * circlePeriod) ^ n / (n.factorial : ℝ)) *
        ((‖E‖ / 4 * R * (M * circlePeriod)) ^ j / (j.factorial : ℝ)) := by
  have ha : Continuous (fun s => conj (deriv γ s)) :=
    Complex.continuous_conj.comp hγ.continuous_deriv_one
  have hJ := volterraPrimitiveIterate_bound_uniform ha hh hM0 hH0
    hM hH (j + n) θ hθ
  have hfact : (n.factorial : ℝ) ≤ ((j + n).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ j + n)
  simp  [volterraVekuaTraceRowTerm, transport_norm_physicalVekuaCoeff]
  calc
    _ ≤ ((‖E‖ / 4) ^ j / j.factorial) * R ^ j *
        (H * (M * circlePeriod) ^ (j + n) / ((j + n).factorial)) := by
      gcongr <;> exact hR θ hθ
    _ ≤ ((‖E‖ / 4) ^ j / j.factorial) * R ^ j *
        (H * (M * circlePeriod) ^ (j + n) / n.factorial) := by
      gcongr
    _ = _ := by
      simp  [mul_pow]
      ring

theorem volterraVekuaTraceRowTerm_continuous n j : Continuous (volterraVekuaTraceRowTermFixed n j) := (continuous_const.mul ((hγ.continuous.sub continuous_const).pow j)).mul
    (continuous_volterraPrimitiveIterate
      (Complex.continuous_conj.comp hγ.continuous_deriv_one) hh (j + n))

/-- Actual row-index factorial decay on the whole parameter interval. -/
theorem exists_volterraVekuaTraceRow_factorial_bound :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      (∀ n θ, θ ∈ boundaryInterval →
        ‖volterraVekuaTraceRowFixed n θ‖ ≤ C * B ^ n / (n.factorial : ℝ)) ∧
      (∀ n, ContinuousOn (volterraVekuaTraceRowFixed n) boundaryInterval) := by
  have hzero : (0 : ℝ) ∈ boundaryInterval := ⟨le_rfl, Real.two_pi_pos.le⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn
  obtain ⟨H, hH⟩ := isCompact_Icc.exists_bound_of_continuousOn hh.continuousOn
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hγ.continuous.sub continuous_const).continuousOn
  have hM0  := (norm_nonneg _).trans (hM 0 hzero)
  have hH0  := (norm_nonneg _).trans (hH 0 hzero)
  have hR0  := (norm_nonneg _).trans (hR 0 hzero)
  let B := M * circlePeriod
  let r := ‖E‖ / 4 * R * B
  let S  := ∑' j : ℕ, r ^ j / j.factorial
  have hB : 0 ≤ B := by positivity
  have hS : 0 ≤ S := tsum_nonneg fun _ => by positivity
  have hs  :=
    Real.summable_pow_div_factorial r
  have hmaj (n : ℕ) : Summable (fun j : ℕ =>
      (H * B ^ n / (n.factorial : ℝ)) * (r ^ j / (j.factorial : ℝ))) :=
    hs.mul_left _
  have hbd (n j : ℕ) (θ : ℝ) (hθ : θ ∈ boundaryInterval)  :=
    volterraVekuaTraceRowTerm_bound hγ hh E hM0 hH0 hR0 hM hH hR n j hθ
  refine ⟨H * S, B, mul_nonneg hH0 hS, hB, ?_, ?_⟩
  · intro n θ hθ
    have hn  :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => hbd n j θ hθ) (hmaj n)
    calc
      _ ≤ ∑' j : ℕ, ‖volterraVekuaTraceRowTermFixed n j θ‖ := norm_tsum_le_tsum_norm hn
      _ ≤ ∑' j : ℕ, (H * B ^ n / n.factorial) *
          (r ^ j / j.factorial) := Summable.tsum_le_tsum (fun j => hbd n j θ hθ) hn (hmaj n)
      _ = _ := by rw [tsum_mul_left]; dsimp only [S]; ring
  · intro n
    have hu  :=
      HasSumUniformlyOn.of_norm_le_summable (hmaj n) (hbd n)
    apply hu.tendstoUniformlyOn.continuousOn
    exact (Eventually.of_forall fun s : Finset ℕ => continuousOn_finset_sum s
      (fun j _ => (volterraVekuaTraceRowTerm_continuous hγ hh E n j).continuousOn)).frequently

end


theorem volterraVekuaTraceRow_zero_origin γ h E :
    volterraVekuaTraceRow γ E h 0 0 = h 0 := by
  unfold volterraVekuaTraceRow
  rw [tsum_eq_single 0]
  · simp [volterraVekuaTraceRowTerm, physicalVekuaCoeff, volterraPrimitiveIterate]
  simp_all [volterraVekuaTraceRowTerm]

theorem volterraVekuaTraceRow_succ_origin γ h E n :
    volterraVekuaTraceRow γ E h (n + 1) 0 = 0 := by
  simp_all [volterraVekuaTraceRow, volterraVekuaTraceRowTerm, volterraPrimitiveIterate]

section
include γ h hγ hh E

/-- A genuine summable majorant for every term, with factorial decay in
the row index as well as in the series index. -/
theorem exists_volterraVekuaTraceRowTerm_majorant :
    ∃ A B r : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ r ∧
      ∀ n j θ, θ ∈ boundaryInterval →
        ‖volterraVekuaTraceRowTermFixed n j θ‖ ≤
          (A * B ^ n / (n.factorial : ℝ)) * (r ^ j / (j.factorial : ℝ)) := by
  have hzero : (0 : ℝ) ∈ boundaryInterval := ⟨le_rfl, Real.two_pi_pos.le⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn
  obtain ⟨H, hH⟩ := isCompact_Icc.exists_bound_of_continuousOn hh.continuousOn
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hγ.continuous.sub continuous_const).continuousOn
  have hM0  := (norm_nonneg _).trans (hM 0 hzero)
  have hH0  := (norm_nonneg _).trans (hH 0 hzero)
  have hR0  := (norm_nonneg _).trans (hR 0 hzero)
  refine ⟨H, M * circlePeriod, ‖E‖ / 4 * R * (M * circlePeriod),
    hH0, by positivity, by positivity, ?_⟩
  intro n j θ hθ
  exact volterraVekuaTraceRowTerm_bound hγ hh E hM0 hH0 hR0 hM hH hR n j hθ

private theorem volterraVekuaTraceRowTerm_hasDerivAt_succ_succ n j θ :
    HasDerivAt (volterraVekuaTraceRowTermFixed (n + 1) (j + 1))
      (conj (deriv γ θ) * volterraVekuaTraceRowTermFixed n (j + 1) θ +
        (-E / 4) * deriv γ θ * volterraVekuaTraceRowTermFixed (n + 2) j θ) θ := by
  have ha : Continuous (fun s => conj (deriv γ s)) :=
    Complex.continuous_conj.comp hγ.continuous_deriv_one
  have hJ := hasDerivAt_volterraPrimitiveIterate_succ ha hh ((j + 1) + n) θ
  have hprev : ((j + 1) + n) + 1 = (j + 1) + (n + 1) := by omega
  rw [hprev] at hJ
  have hd := (((hγ.differentiable_one θ).hasDerivAt.sub_const (γ 0)).pow (j + 1)).mul hJ
  have hidx : (j + 1) + (n + 1) = j + (n + 2) := by omega
  have he : physicalVekuaCoeff E (j + 1) *
      ((((j + 1 : ℕ) : ℂ) * (γ θ - γ 0) ^ j * deriv γ θ) *
          volterraPrimitiveIterate (fun s => conj (deriv γ s)) h (j + (n + 2)) θ +
        (γ θ - γ 0) ^ (j + 1) * (conj (deriv γ θ) *
          volterraPrimitiveIterate (fun s => conj (deriv γ s)) h ((j + 1) + n) θ)) =
      conj (deriv γ θ) * volterraVekuaTraceRowTermFixed n (j + 1) θ +
        (-E / 4) * deriv γ θ * volterraVekuaTraceRowTermFixed (n + 2) j θ := by
    simp only [volterraVekuaTraceRowTerm]
    calc
      _ = (physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ))) *
          deriv γ θ * (γ θ - γ 0) ^ j *
            volterraPrimitiveIterate (fun s => conj (deriv γ s)) h (j + (n + 2)) θ +
          conj (deriv γ θ) * (physicalVekuaCoeff E (j + 1) * (γ θ - γ 0) ^ (j + 1) *
            volterraPrimitiveIterate (fun s => conj (deriv γ s)) h ((j + 1) + n) θ) := by
          ring
      _ = _ := by rw [physicalVekuaCoeff_succ]; ring
  convert hd.const_mul (physicalVekuaCoeff E (j + 1)) using 1
  · funext x
    simp  [volterraVekuaTraceRowTerm]
    ring
  simp_all

/-- The positive row recurrence is the derivative of the actual Volterra
series. A summable derivative majorant justifies the differentiation. -/
theorem volterraVekuaTraceRow_hasDerivAt_succ n  (hθ : θ ∈ Ioo 0 circlePeriod) :
    HasDerivAt (volterraVekuaTraceRowFixed (n + 1))
      ((-E / 4) * deriv γ θ * volterraVekuaTraceRowFixed (n + 2) θ +
        conj (deriv γ θ) * volterraVekuaTraceRowFixed n θ) θ := by
  obtain ⟨A, B, r, hA, hB, hr, hbd⟩ := exists_volterraVekuaTraceRowTerm_majorant hγ hh E
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hγ.continuous_deriv_one.continuousOn
  have hM0  := (norm_nonneg _).trans (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  let k  := fun l => A * B ^ l / l.factorial
  have hk (l : ℕ) : 0 ≤ k l := by dsimp only [k]; positivity
  have hs (l : ℕ) {x : ℝ} (hx : x ∈ boundaryInterval) :
      Summable (volterraVekuaTraceRowTermFixed l · x) := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun j => hbd l j x hx) ((Real.summable_pow_div_factorial r).mul_left (k l))
  let d  := fun j x =>
    conj (deriv γ x) * volterraVekuaTraceRowTermFixed n (j + 1) x +
      (-E / 4) * deriv γ x * volterraVekuaTraceRowTermFixed (n + 2) j x
  let u  := fun j =>
    (M * k n * r + ‖-E / 4‖ * M * k (n + 2)) * (r ^ j / j.factorial)
  have hu : Summable u := (Real.summable_pow_div_factorial r).mul_left _
  have hd (j : ℕ) (x : ℝ) (_hx : x ∈ Ioo 0 circlePeriod)  :=
    volterraVekuaTraceRowTerm_hasDerivAt_succ_succ hγ hh E n j x
  have hdb (j : ℕ) (x : ℝ) (hx : x ∈ Ioo 0 circlePeriod) : ‖d j x‖ ≤ u j := by
    have hxcc := Ioo_subset_Icc_self hx
    have ha : ‖conj (deriv γ x)‖ ≤ M := by simpa only [Complex.norm_conj] using hM x hxcc
    have hfact : (j.factorial : ℝ) ≤ ((j + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega : j ≤ j + 1)
    dsimp only [d]
    calc
      _ ≤ ‖conj (deriv γ x) * volterraVekuaTraceRowTermFixed n (j + 1) x‖ +
          ‖(-E / 4) * deriv γ x * volterraVekuaTraceRowTermFixed (n + 2) j x‖ := norm_add_le _ _
      _ ≤ M * (k n * (r ^ (j + 1) / ((j + 1).factorial))) +
          ‖-E / 4‖ * M * (k (n + 2) * (r ^ j / j.factorial)) := by
        simp only [norm_mul]
        apply add_le_add
        · exact mul_le_mul ha (hbd n (j + 1) x hxcc) (norm_nonneg _) hM0
        · exact mul_le_mul (mul_le_mul_of_nonneg_left (hM x hxcc) (norm_nonneg _))
            (hbd (n + 2) j x hxcc) (norm_nonneg _) (by positivity)
      _ ≤ M * (k n * (r ^ (j + 1) / j.factorial)) +
          ‖-E / 4‖ * M * (k (n + 2) * (r ^ j / j.factorial)) := by
        gcongr
      _ = u j := by dsimp only [u]; rw [pow_succ]; ring
  have hxcc := Ioo_subset_Icc_self hθ
  have hds := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo _ _).isPreconnected
    hd hdb hθ ((summable_nat_add_iff 1).2 (hs (n + 1) hxcc)) hθ
  have ha : Continuous (fun s => conj (deriv γ s)) :=
    Complex.continuous_conj.comp hγ.continuous_deriv_one
  have hd0 : HasDerivAt (volterraVekuaTraceRowTermFixed (n + 1) 0)
      (conj (deriv γ θ) * volterraVekuaTraceRowTermFixed n 0 θ) θ := by
    convert hasDerivAt_volterraPrimitiveIterate_succ ha hh n θ using 1
    · funext x
      simp [volterraVekuaTraceRowTerm, physicalVekuaCoeff]
    · simp [volterraVekuaTraceRowTerm, physicalVekuaCoeff]
  have heq : volterraVekuaTraceRowFixed (n + 1) =ᶠ[𝓝 θ]
      fun x => volterraVekuaTraceRowTermFixed (n + 1) 0 x +
        ∑' j : ℕ, volterraVekuaTraceRowTermFixed (n + 1) (j + 1) x := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
    exact (hs (n + 1) (Ioo_subset_Icc_self hx)).tsum_eq_zero_add
  have hder := (hd0.add hds).congr_of_eventuallyEq heq
  have hdSum : (∑' j : ℕ, d j θ) =
      conj (deriv γ θ) * (∑' j : ℕ, volterraVekuaTraceRowTermFixed n (j + 1) θ) +
        (-E / 4) * deriv γ θ * volterraVekuaTraceRowFixed (n + 2) θ := by
    dsimp only [d, volterraVekuaTraceRow]
    rw [Summable.tsum_add (((summable_nat_add_iff 1).2 (hs n hxcc)).mul_left _)
      ((hs (n + 2) hxcc).mul_left _), tsum_mul_left, tsum_mul_left]
  apply hder.congr_deriv
  rw [hdSum]
  have hn := (hs n hxcc).tsum_eq_zero_add
  change volterraVekuaTraceRowFixed n θ = _ at hn
  rw [hn]
  ring

end


end


/-- A true conormal kernel gains regularity from NC−I smoothing. -/
theorem normalizedConormal_kernel_raw_H1
     (hβ : IsWL1 (1 / 2 : ℝ) β)
    (ha : IsWL1 (1 / 2 : ℝ) a) (hg : IsWL1 (1 / 2 : ℝ) g)
    E b (hb : normalizedConormal hβ ha hg E b = 0) :
    IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) := by
  have he := congrArg (fun A : L2Z →L[ℂ] L2Z => A b)
    (normalizedConormal_sub_one_eq hβ ha hg E)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply, hb, zero_sub] at he
  have hr : b = sobolevSmoothing 1 zero_le_one (b - conormalRemOp (by norm_num) hβ ha hg E b) := by
    have h := congrArg Neg.neg he
    simpa only [← map_neg, neg_sub, neg_neg] using h
  rw [hr, fromL2_half_smoothing_one]
  exact (sobNormSq_mono (by norm_num)
    (isSobolevSeq_fromL2 ((1 / 2) + 1) _)).1

section PhysicalCoordinates

variable {R C K } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    (hK : DiskDerivativeBound F K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : PlaneMap) = F)
    (hsource : closedUnitDisk ⊆ e.source)
    (hes : RealSmoothOn e.symm e.target)
local notation "physicalCircleTraceFixed" => physicalCircleTrace F


local notation "JF" => localConformalHardyPrimitive hR F hFs
local notation "VB" => localConformalVekuaBoundary hR F hFs hb hL hhol hinj hC hK
  e he hsource hes
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs

/-- These are actual normalized Vekua traces, reconstructed in ordinary
averaged coordinates. No formal row or derivative is substituted. -/
def localConformalVekuaTraceRow (E : ℂ) (b : L2Z) (n : ℕ) (θ : ℝ) : ℂ :=
  hardyFourierTrace (normalizedHardyAverage (VB E ((JF ^ n) b))) θ
local notation "vekuaTraceRowFixed" => localConformalVekuaTraceRow hR F hFs hb hL hhol hinj hC hK e he hsource hes


section
variable (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b) (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b))

include E b hbn hb1 in
/-- Every actual coordinate trace row equals its true interval-integral
series, for the full nonpositive input including frequency zero. -/
theorem localConformalVekuaTraceRow_eq_volterra n θ :
    vekuaTraceRowFixed E b n θ =
      volterraVekuaTraceRow (physicalCircleTraceFixed) E
        (hardyFourierTrace (normalizedHardyAverage b)) n θ := by
  have hpn := localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol b hbn n
  have hp1 := localConformalHardyPrimitive_pow_raw_H1 hR F hFs b hb1 n
  have havg : IsSobolevSeq 1 (normalizedHardyAverage b) := isSobolevSeq_smul _ hb1
  have hfun : hardyFourierTrace (normalizedHardyAverage ((JF ^ n) b)) =
      volterraPrimitiveIterate (fun s => conj (deriv (physicalCircleTraceFixed) s))
        (hardyFourierTrace (normalizedHardyAverage b)) n := by
    funext s
    exact localConformalHardyPrimitive_pow_volterra_of_H1 hR F hFs hhol b hbn havg n s
  have hs := localConformalVekuaBoundary_average_volterra_hasSum_of_H1 hR F hFs hb hL
    hhol hinj hC hK e he hsource hes E ((JF ^ n) b) hpn hp1 θ
  rw [hfun] at hs
  simpa only [localConformalVekuaTraceRow, volterraVekuaTraceRow, volterraVekuaTraceRowTerm, physicalCircleTrace, circleMap_zero, starRingEnd_apply, Complex.exp_zero, Complex.ofReal_zero, Complex.ofReal_one, zero_mul, mul_one, volterraPrimitiveIterate_iterate] using hs.tsum_eq.symm

theorem localConformalVekuaTraceRow_periodic E b n :
    Function.Periodic
      (vekuaTraceRowFixed E b n)
      circlePeriod := hardyFourierTrace_periodic _

section
include E b hbn hb1

/-- Genuine positive-row tangential differentiation of the full-input
physical Vekua traces, proved through their actual Volterra series. -/
theorem localConformalVekuaTraceRow_hasDerivAt_succ n
     (hθ : θ ∈ Ioo 0 circlePeriod) :
    HasDerivAt
      (vekuaTraceRowFixed E b (n + 1))
      ((-E / 4) * deriv (physicalCircleTraceFixed) θ *
          vekuaTraceRowFixed E b (n + 2) θ +
        conj (deriv (physicalCircleTraceFixed) θ) *
          vekuaTraceRowFixed E b n θ) θ := by
  have hfun (k : ℕ) :
      vekuaTraceRowFixed E b k =
        volterraVekuaTraceRow (physicalCircleTraceFixed) E
          (hardyFourierTrace (normalizedHardyAverage b)) k := by
    ext <;> simp_all [localConformalVekuaTraceRow_eq_volterra]
  rw [hfun (n + 1), hfun (n + 2), hfun n]
  have havg : IsSobolevSeq 1 (normalizedHardyAverage b) := isSobolevSeq_smul _ hb1
  exact volterraVekuaTraceRow_hasDerivAt_succ
    (contDiff_physicalCircleTrace_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top)))
    (continuous_hardyFourierTrace (sq_tsum_norm_le (s := 0) (by norm_num)
      (by simpa using havg)).1) E n hθ

/-- The factorial decay is a bound on the actual Vekua trace rows. -/
theorem exists_localConformalVekuaTraceRow_factorial_bound :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ n θ, θ ∈ boundaryInterval →
        ‖vekuaTraceRowFixed E b n θ‖ ≤ A * B ^ n / (n.factorial : ℝ)) ∧
      (∀ n, ContinuousOn
        (vekuaTraceRowFixed E b n) boundaryInterval) := by
  have hγ  :=
    contDiff_physicalCircleTrace_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have havg : IsSobolevSeq 1 (normalizedHardyAverage b) := isSobolevSeq_smul _ hb1
  have hh  :=
    continuous_hardyFourierTrace
      (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using havg)).1
  obtain ⟨A, B, hA, hB, hbd, hc⟩ := exists_volterraVekuaTraceRow_factorial_bound hγ hh E
  refine ⟨A, B, hA, hB, ?_, ?_⟩
  · simp_all [localConformalVekuaTraceRow_eq_volterra]
  · intro n
    have heq : vekuaTraceRowFixed E b n = volterraVekuaTraceRow (physicalCircleTraceFixed) E
          (hardyFourierTrace (normalizedHardyAverage b)) n := by
      funext θ
      simp_all [localConformalVekuaTraceRow_eq_volterra]
    rw [heq]
    exact hc n

theorem localConformalVekuaTraceRow_zero_origin :
    vekuaTraceRowFixed E b 0 0 = hardyFourierTrace (normalizedHardyAverage b) 0 := by
  simp_all [localConformalVekuaTraceRow_eq_volterra, volterraVekuaTraceRow_zero_origin]

theorem localConformalVekuaTraceRow_succ_origin n :
    vekuaTraceRowFixed E b (n + 1) 0 = 0 := by
  simp_all [localConformalVekuaTraceRow_eq_volterra, volterraVekuaTraceRow_succ_origin]

end


end


/-- Physical transport coordinates retain y₀=U₀/√2 and yₙ=qⁿUₙ. -/
def localConformalVekuaTransportCoordinate (E : ℝ) (b : L2Z) (n : ℕ) (θ : ℝ) : ℂ :=
  if n = 0 then
    vekuaTraceRowFixed (E : ℂ) b 0 θ / (Real.sqrt 2 : ℂ)
  else physicalDrivenQ E ^ n *
    vekuaTraceRowFixed (E : ℂ) b n θ
local notation "vekuaTransportCoordinateFixed" => localConformalVekuaTransportCoordinate hR F hFs hb hL hhol hinj hC hK e he hsource hes


section
variable (E : ℝ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b) (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b))

include E b hbn hb1 in
/-- Genuine factorial majorants for the scaled Ell² coordinates. -/
theorem exists_localConformalVekuaTransportCoordinate_factorial_bound :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ n θ, θ ∈ boundaryInterval →
        ‖vekuaTransportCoordinateFixed E b n θ‖ ≤ A * B ^ n / (n.factorial : ℝ)) ∧
      (∀ n, ContinuousOn
        (vekuaTransportCoordinateFixed E b n) boundaryInterval) := by
  obtain ⟨A, B, hA, hB, hbd, hc⟩ := exists_localConformalVekuaTraceRow_factorial_bound
    hR F hFs hb hL hhol hinj hC hK e he hsource hes E b hbn hb1
  refine ⟨A, ‖physicalDrivenQ E‖ * B, hA, mul_nonneg (norm_nonneg _) hB, ?_, ?_⟩
  · intro n θ hθ
    by_cases hn : n = 0
    · subst n
      simp only [localConformalVekuaTransportCoordinate, if_true, pow_zero,
        Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
      have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := by
        bound
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
      apply (div_le_iff₀ hs).2
      have hb0 : ‖vekuaTraceRowFixed (E : ℂ) b 0 θ‖ ≤ A := by simpa using hbd 0 θ hθ
      nlinarith
    · rw [localConformalVekuaTransportCoordinate, if_neg hn, norm_mul, norm_pow]
      calc
        _ ≤ ‖physicalDrivenQ E‖ ^ n * (A * B ^ n / n.factorial) :=
          mul_le_mul_of_nonneg_left (hbd n θ hθ) (by positivity)
        _ = _ := by ring
  · intro n
    unfold localConformalVekuaTransportCoordinate
    by_cases hn : n = 0
    · simp only [hn, if_true]
      exact (hc 0).div_const _
    · simp only [hn, if_false]
      exact continuousOn_const.mul (hc n)

section
variable {θ } (hθ : θ ∈ boundaryInterval)

include E b hbn hb1 in
include θ hθ in
/-- The coordinates form a genuinely absolutely summable sequence. -/
theorem summable_norm_localConformalVekuaTransportCoordinate :
    Summable (fun n : ℕ => ‖vekuaTransportCoordinateFixed E b n θ‖) := by
  obtain ⟨A, B, hA, hB, hbd, hc⟩ := exists_localConformalVekuaTransportCoordinate_factorial_bound
    hR F hFs hb hL hhol hinj hC hK e he hsource hes E b hbn hb1
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hbd n θ hθ)
    (summable_volterraPrimitive_majorant A B)

/-- An actual Ell² vector, synthesized from the true coordinate traces. -/
def localConformalVekuaTransportVector (E : ℝ) (b : L2Z) (θ : ℝ) : Ell2 :=
  ∑' n : ℕ, vekuaTransportCoordinateFixed E b n θ • basisVec n
local notation "vekuaTransportVectorFixed" => localConformalVekuaTransportVector hR F hFs hb hL hhol hinj hC hK e he hsource hes


private theorem vekuaTransport_norm_basisVec n : ‖basisVec n‖ = 1 := by
  simp_all [PolyaNeumann.basisVec]

section
include E b hbn hb1 θ hθ

theorem localConformalVekuaTransportVector_hasSum :
    HasSum (fun n : ℕ => vekuaTransportCoordinateFixed E b n θ • basisVec n)
      (vekuaTransportVectorFixed E b θ) := by
  apply Summable.hasSum
  apply Summable.of_norm
  simpa  [norm_smul, vekuaTransport_norm_basisVec] using
    summable_norm_localConformalVekuaTransportCoordinate hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 hθ

/-- Every coordinate of the actual Ell² synthesis is the intended row. -/
theorem localConformalVekuaTransportVector_coord n :
    (vekuaTransportVectorFixed E b θ : ComplexSeq) n =
      vekuaTransportCoordinateFixed E b n θ := by
  have hs := (localConformalVekuaTransportVector_hasSum hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn hb1 hθ).summable
  have hm := (innerSL ℂ (basisVec n)).map_tsum hs
  simp  [inner_basisVec, basisVec_coord] at hm
  simp_all [localConformalVekuaTransportVector]

end


include E b hbn hb1 in
theorem localConformalVekuaTransportVector_continuousOn :
    ContinuousOn (vekuaTransportVectorFixed E b) boundaryInterval := by
  obtain ⟨A, B, hA, hB, hbd, hc⟩ := exists_localConformalVekuaTransportCoordinate_factorial_bound
    hR F hFs hb hL hhol hinj hC hK e he hsource hes E b hbn hb1
  have hu : HasSumUniformlyOn
      (fun n θ => vekuaTransportCoordinateFixed E b n θ • basisVec n)
      (vekuaTransportVectorFixed E b)
      boundaryInterval := by
    apply HasSumUniformlyOn.of_norm_le_summable (summable_volterraPrimitive_majorant A B)
    intro n θ hθ
    simpa only [norm_smul, vekuaTransport_norm_basisVec, mul_one] using hbd n θ hθ
  apply hu.tendstoUniformlyOn.continuousOn
  refine (Eventually.of_forall fun s : Finset ℕ => ?_).frequently
  apply continuousOn_finset_sum s
  fun_prop

theorem localConformalVekuaTransportVector_periodic E b :
    Function.Periodic (vekuaTransportVectorFixed E b) circlePeriod := by
  intro θ
  apply tsum_congr
  intro n
  unfold localConformalVekuaTransportCoordinate
  rw [localConformalVekuaTraceRow_periodic hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b 0 θ,
    localConformalVekuaTraceRow_periodic hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b n θ]

include E b hbn hb1 in
/-- The initial datum is proved from the actual zero-origin primitives. -/
theorem localConformalVekuaTransportVector_origin :
    vekuaTransportVectorFixed E b 0 =
      (hardyFourierTrace (normalizedHardyAverage b) 0 / (Real.sqrt 2 : ℂ)) • basisVec 0 := by
  apply lp.ext
  funext n
  rw [localConformalVekuaTransportVector_coord hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn hb1 ⟨le_rfl, Real.two_pi_pos.le⟩]
  cases n with
  | zero =>
      simp_all [localConformalVekuaTransportCoordinate, localConformalVekuaTraceRow_zero_origin, PolyaNeumann.basisVec]
  | succ n =>
      simp_all [localConformalVekuaTransportCoordinate, localConformalVekuaTraceRow_succ_origin, PolyaNeumann.basisVec]

/-- The true derivative of positive coordinate n+1. It is not an assumed
transport coefficient: it comes from the scalar Volterra recurrence. -/
def localConformalVekuaPositiveTransportDerivative (E : ℝ) (b : L2Z)
    (n : ℕ) (θ : ℝ) : ℂ :=
  physicalDrivenQ E ^ (n + 1) *
    ((-(E : ℂ) / 4) * deriv (physicalCircleTraceFixed) θ *
        vekuaTraceRowFixed (E : ℂ) b (n + 2) θ +
      conj (deriv (physicalCircleTraceFixed) θ) *
        vekuaTraceRowFixed (E : ℂ) b n θ)
local notation "vekuaPositiveTransportDerivativeFixed" => localConformalVekuaPositiveTransportDerivative hR F hFs hb hL hhol hinj hC hK e he hsource hes


section
include E b hbn hb1

theorem localConformalVekuaTransportCoordinate_hasDerivAt_succ n
     (hθ : θ ∈ Ioo 0 circlePeriod) :
    HasDerivAt
      (vekuaTransportCoordinateFixed E b (n + 1))
      (vekuaPositiveTransportDerivativeFixed E b n θ) θ := by
  unfold localConformalVekuaTransportCoordinate localConformalVekuaPositiveTransportDerivative
  simpa   using
      (localConformalVekuaTraceRow_hasDerivAt_succ hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E b hbn hb1 n hθ).const_mul (physicalDrivenQ E ^ (n + 1))

/-- The actual positive derivatives also have a genuine summable
factorial majorant, uniformly on the entire closed parameter interval. -/
theorem exists_localConformalVekuaPositiveTransportDerivative_majorant :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n θ, θ ∈ boundaryInterval →
      ‖vekuaPositiveTransportDerivativeFixed E b n θ‖ ≤ u n := by
  obtain ⟨A, B, hA, hB, hbd, hc⟩ := exists_localConformalVekuaTraceRow_factorial_bound
    hR F hFs hb hL hhol hinj hC hK e he hsource hes E b hbn hb1
  have hΓ  :=
    contDiff_physicalCircleTrace_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hΓ.continuous_deriv_one.continuousOn
  have hM0  := (norm_nonneg _).trans (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  let D := ‖physicalDrivenQ E‖ * A * M * (‖-(E : ℂ) / 4‖ * B ^ 2 + 1)
  let r := ‖physicalDrivenQ E‖ * B
  refine ⟨fun n => D * r ^ n / n.factorial,
    summable_volterraPrimitive_majorant D r, ?_⟩
  intro n θ hθ
  have hfact : (n.factorial : ℝ) ≤ ((n + 2).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ n + 2)
  simp  [localConformalVekuaPositiveTransportDerivative]
  calc
    _ ≤ ‖physicalDrivenQ E‖ ^ (n + 1) *
        (‖(-E / 4) * deriv (physicalCircleTraceFixed) θ *
            vekuaTraceRowFixed E b (n + 2) θ‖ +
          ‖conj (deriv (physicalCircleTraceFixed) θ) *
            vekuaTraceRowFixed E b n θ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ ‖physicalDrivenQ E‖ ^ (n + 1) *
        (‖-(E : ℂ) / 4‖ * M * (A * B ^ (n + 2) / ((n + 2).factorial)) +
          M * (A * B ^ n / n.factorial)) := by
      simp only [norm_mul, Complex.norm_conj]
      apply mul_le_mul_of_nonneg_left
      · apply add_le_add
        · calc
            ‖-(E : ℂ) / 4‖ * ‖deriv (physicalCircleTraceFixed) θ‖ *
                ‖vekuaTraceRowFixed E b (n + 2) θ‖
                ≤ ‖-(E : ℂ) / 4‖ * M *
                    ‖vekuaTraceRowFixed E b (n + 2) θ‖ := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left (hM θ hθ) (norm_nonneg _))
                    (norm_nonneg _)
            _ ≤ ‖-(E : ℂ) / 4‖ * M *
                (A * B ^ (n + 2) / ((n + 2).factorial)) := by
                  exact mul_le_mul_of_nonneg_left (hbd (n + 2) θ hθ)
                    (mul_nonneg (norm_nonneg _) hM0)
        · calc
            ‖deriv (physicalCircleTraceFixed) θ‖ *
                ‖vekuaTraceRowFixed E b n θ‖
                ≤ M * ‖vekuaTraceRowFixed E b n θ‖ := by
                  exact mul_le_mul_of_nonneg_right (hM θ hθ) (norm_nonneg _)
            _ ≤ M * (A * B ^ n / n.factorial) := by
                  exact mul_le_mul_of_nonneg_left (hbd n θ hθ) hM0
      · positivity
    _ ≤ ‖physicalDrivenQ E‖ ^ (n + 1) *
        (‖-(E : ℂ) / 4‖ * M * (A * B ^ (n + 2) / n.factorial) +
          M * (A * B ^ n / n.factorial)) := by
      gcongr
    _ = D * r ^ n / n.factorial := by
      ring

end


/-- The positive part is a genuine Ell² series of the actual traces. -/
def localConformalVekuaPositiveTransportVector (E : ℝ) (b : L2Z) (θ : ℝ) : Ell2 :=
  ∑' n : ℕ, vekuaTransportCoordinateFixed E b (n + 1) θ • basisVec (n + 1)

section
include E b hbn hb1

include θ hθ in
/-- Separating the exceptional zeroth row is justified by actual
absolute convergence, rather than by a formal rearrangement. -/
theorem localConformalVekuaTransportVector_zero_add_positive :
    vekuaTransportVectorFixed E b θ =
      vekuaTransportCoordinateFixed E b 0 θ • basisVec 0 +
        localConformalVekuaPositiveTransportVector hR F hFs hb hL hhol hinj hC hK
          e he hsource hes E b θ :=
  (localConformalVekuaTransportVector_hasSum hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn hb1 hθ).summable.tsum_eq_zero_add

/-- Genuine Hilbert-space differentiation of the whole positive part.
Both the row and derivative series are justified by summable majorants. -/
theorem localConformalVekuaPositiveTransportVector_hasDerivAt
    {θ : ℝ} (hθ : θ ∈ Ioo 0 circlePeriod) :
    HasDerivAt
      (localConformalVekuaPositiveTransportVector hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E b)
      (∑' n : ℕ, vekuaPositiveTransportDerivativeFixed E b n θ • basisVec (n + 1)) θ := by
  obtain ⟨u, hu, hbd⟩ := exists_localConformalVekuaPositiveTransportDerivative_majorant
    hR F hFs hb hL hhol hinj hC hK e he hsource hes E b hbn hb1
  have hg (n : ℕ) (x : ℝ) (hx : x ∈ Ioo 0 circlePeriod) :
      HasDerivAt
        (fun t => vekuaTransportCoordinateFixed E b (n + 1) t • basisVec (n + 1))
        (vekuaPositiveTransportDerivativeFixed E b n x • basisVec (n + 1)) x :=
    (localConformalVekuaTransportCoordinate_hasDerivAt_succ hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 n hx).smul_const _
  have hgb (n : ℕ) (x : ℝ) (hx : x ∈ Ioo 0 circlePeriod) :
      ‖vekuaPositiveTransportDerivativeFixed E b n x • basisVec (n + 1)‖ ≤ u n := by
    simpa only [norm_smul, vekuaTransport_norm_basisVec, mul_one] using
      hbd n x (Ioo_subset_Icc_self hx)
  have hs := (localConformalVekuaTransportVector_hasSum hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn hb1 (Ioo_subset_Icc_self hθ)).summable
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo _ _).isPreconnected
    hg hgb hθ ((summable_nat_add_iff 1).2 hs) hθ

end


/-- The computed positive derivative has exactly the corresponding
coordinate of the original physical transport coefficient. -/
theorem localConformalVekuaPositiveTransportDerivative_eq_transportCoeff_coord
    E (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) n
     (hθ : θ ∈ boundaryInterval) :
    vekuaPositiveTransportDerivativeFixed E b n θ =
      (transportCoeff (physicalCircleTraceFixed) E θ
        (vekuaTransportVectorFixed E b θ) : ComplexSeq) (n + 1) := by
  rw [transportCoeff_apply_coord, shiftN_apply_succ,
    localConformalVekuaTransportVector_coord hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 hθ (n + 2),
    localConformalVekuaTransportVector_coord hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 hθ n]
  change _ = physicalDrivenQ E * _
  unfold localConformalVekuaPositiveTransportDerivative
  rw [← physicalDrivenQ_sq hE]
  cases n with
  | zero =>
      have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
        norm_num
      grind only [localConformalVekuaTransportCoordinate, shiftWeight, PolyaNeumann.physicalDrivenQ, PolyaNeumann.physicalCircleTrace, PolyaNeumann.shiftWeight]
  | succ n =>
      simp  [localConformalVekuaTransportCoordinate, shiftWeight]
      ring

include E b hbn hb1 in
include θ hθ in
/-- Actual absolute convergence of the positive Hilbert derivative. -/
theorem summable_localConformalVekuaPositiveTransportDerivative :
    Summable (fun n : ℕ =>
      vekuaPositiveTransportDerivativeFixed E b n θ • basisVec (n + 1)) := by
  obtain ⟨u, hu, hbd⟩ := exists_localConformalVekuaPositiveTransportDerivative_majorant
    hR F hFs hb hL hhol hinj hC hK e he hsource hes E b hbn hb1
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hu
  intro n
  simpa  [norm_smul, vekuaTransport_norm_basisVec] using hbd n θ hθ

end

end

local notation "vekuaPositiveTransportDerivativeFixed" => localConformalVekuaPositiveTransportDerivative hR F hFs hb hL hhol hinj hC hK e he hsource hes

local notation "vekuaTransportVectorFixed" => localConformalVekuaTransportVector hR F hFs hb hL hhol hinj hC hK e he hsource hes


section
variable (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)

include E hE b hbn in
/-- The positive derivative is the genuine physical transport term with
its exceptional zeroth coordinate removed. -/
theorem localConformalVekuaPositiveTransportDerivative_tsum_eq
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b))
    {θ : ℝ} (hθ : θ ∈ boundaryInterval) :
    (∑' n : ℕ, vekuaPositiveTransportDerivativeFixed E b n θ • basisVec (n + 1)) =
      transportCoeff (physicalCircleTraceFixed) E θ
          (vekuaTransportVectorFixed E b θ) -
        ((transportCoeff (physicalCircleTraceFixed) E θ
          (vekuaTransportVectorFixed E b θ) : ComplexSeq) 0) • basisVec 0 := by
  have hs := summable_localConformalVekuaPositiveTransportDerivative hR F hFs hb hL hhol hinj
    hC hK e he hsource hes E b hbn hb1 hθ
  apply lp.ext
  funext n
  have hm := (innerSL ℂ (basisVec n)).map_tsum hs
  simp  [inner_basisVec, basisVec_coord] at hm
  rw [hm]
  cases n with
  | zero =>
      simp only [Nat.zero_ne_add_one, if_false, tsum_zero, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, basisVec_coord, if_true, mul_one, sub_self]
  | succ n =>
      simp only [Nat.succ_inj, 
        lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        basisVec_coord, Nat.succ_ne_zero, if_false, mul_zero, sub_zero]
      let c  := fun z => vekuaPositiveTransportDerivativeFixed E b z θ
      simp_all [localConformalVekuaPositiveTransportDerivative_eq_transportCoeff_coord, PolyaNeumann.Ell2]

/-- Kernel inputs obtain the regularity needed by the actual transport
construction from the proved normalized-conormal smoothing formula. -/
theorem localConformalVekuaConormal_kernel_raw_H1 E b
    (hker : normalizedConormal hβF haF hgF E b = 0) :
    IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) :=
  normalizedConormal_kernel_raw_H1 hβF haF hgF E b hker

theorem localConformalVekuaTraceRow_continuous E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b)) n :
    Continuous (vekuaTraceRowFixed E b n) := by
  have hp1 := localConformalHardyPrimitive_pow_raw_H1 hR F hFs b hb1 n
  have hpn := localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol b hbn n
  have hr := localConformalVekuaBoundary_raw_H1 hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E ((JF ^ n) b) hpn hp1
  have havg0 := isSobolevSeq_smul (Real.sqrt circlePeriod)⁻¹ hr
  have havg : IsSobolevSeq 1 (normalizedHardyAverage (VB E ((JF ^ n) b))) := by
    assumption
  exact continuous_hardyFourierTrace (sq_tsum_norm_le (s := 0) (by norm_num)
    (by simpa using havg)).1

/-- The actual conormal kernel determines the exceptional zeroth-row
derivative. Fourier inversion is applied to two genuine continuous
periodic functions; no differentiability of this row is assumed. -/
theorem localConformalVekuaConormal_kernel_hasDerivAt_zero E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hker : normalizedConormal hβF haF hgF E b = 0) θ :
    HasDerivAt
      (vekuaTraceRowFixed E b 0)
      (2 * (-E / 4) * deriv (physicalCircleTraceFixed) θ *
        vekuaTraceRowFixed E b 1 θ) θ := by
  have hb1 := localConformalVekuaConormal_kernel_raw_H1 hR F hFs E b hker
  let v  := vekuaTraceRowFixed E b 0
  let d  := fun t => 2 * (-E / 4) * deriv (physicalCircleTraceFixed) t *
    vekuaTraceRowFixed E b 1 t
  have hv  := localConformalVekuaTraceRow_continuous hR F hFs hb hL hhol
    hinj hC hK e he hsource hes E b hbn hb1 0
  have hΓ  :=
    contDiff_physicalCircleTrace_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hd : Continuous d :=
    (continuous_const.mul hΓ.continuous_deriv_one).mul
      (localConformalVekuaTraceRow_continuous hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E b hbn hb1 1)
  have hvper  :=
    localConformalVekuaTraceRow_periodic hR F hFs hb hL hhol hinj hC hK e he hsource hes E b 0
  have hdper : Function.Periodic d circlePeriod := by
    intro t
    dsimp only [d]
    rw [deriv_periodic (physicalCircleTrace_periodic F),
      localConformalVekuaTraceRow_periodic hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E b 1]
  let TF := localConformalDiskH1Trace hR F hFs hL
  let VF := localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes
  let Vel := boundaryContinuousMultiplier (localConformalVelocityCircle F)
  let G  := Vel (TF (VF (F 1) E (JF b)))
  let L  := (2 * (-E / 4)) • G
  have hJbn := localConformalHardyPrimitive_nonpositive hR F hFs hhol b hbn
  have hJ1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) (JF b)) := by
    simpa only [pow_one] using localConformalHardyPrimitive_pow_raw_H1 hR F hFs b hb1 1
  have ht0 : (TF (VF (F 1) E b) : ComplexCurve)
      =ᵐ[volume.restrict boundaryHalfOpenInterval] v := by
    simp only [v, TF, VF]
    unfold localConformalVekuaTraceRow
    simpa only [pow_zero, ContinuousLinearMap.one_apply] using
      localConformalVekua_coordinate_trace_reconstruction_ae hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E b hbn hb1
  have ht1 := localConformalVekua_coordinate_trace_reconstruction_ae hR F hFs hb hL hhol
    hinj hC hK e he hsource hes E (JF b) hJbn hJ1
  have hLae : (L : ComplexCurve) =ᵐ[volume.restrict boundaryHalfOpenInterval] d := by
    filter_upwards [Lp.coeFn_smul (2 * (-E / 4)) G,
      boundaryContinuousMultiplier_ae (localConformalVelocityCircle F) (TF (VF (F 1) E (JF b))),
      ht1] with t hL hG ht
    rw [hL]
    simp only [Pi.smul_apply, smul_eq_mul, G, Vel, TF, VF, hG, ht,
      localConformalVelocityCircle_apply hR F hFs, d, localConformalVekuaTraceRow, pow_one]
    ring
  have hc (n : ℤ) : fourierCoeffOn Real.two_pi_pos d n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos v n := by
    have hNC := localConformalVekua_normalizedConormal_fourier hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 n
    simp only [hker, lp.coeFn_zero, Pi.zero_apply, localConformalVekuaGradientA_apply,
      map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hNC
    have hw : (((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos (sobWeight_pos n) (-(1 / 2))).ne'
    have hn  :=
      (mul_eq_zero.mp hNC.symm).resolve_left hw
    have hs0 : (Real.sqrt circlePeriod : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
    apply mul_left_cancel₀ hs0
    calc
      _ = boundaryFourier L n := (boundaryFourier_congr_ae L hLae n).symm
      _ = (Complex.I * n) * boundaryFourier (TF (VF (F 1) E b)) n := by
        simp only [L, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        have h2 : 2 * Complex.I * ((-E / 4) * boundaryFourier G n) =
            -(n : ℂ) * boundaryFourier (TF (VF (F 1) E b)) n := by
          exact (sub_eq_zero.mp hn).symm
        have hrel : 2 * (-E / 4) * boundaryFourier G n =
            Complex.I * (n : ℂ) * boundaryFourier (TF (VF (F 1) E b)) n := by
          have hI : Complex.I ^ 2 = (-1 : ℂ) := by norm_num
          calc
            _ = -(Complex.I * (2 * Complex.I * ((-E / 4) * boundaryFourier G n))) := by
              linear_combination (norm := (ring_nf <;> simp [Complex.I_sq] <;> ring)) hI
            _ = -(Complex.I * (-n * boundaryFourier (TF (VF (F 1) E b)) n)) := by
              rw [h2]
            _ = _ := by ring
        rw [hrel]
      _ = _ := by
        rw [boundaryFourier_congr_ae _ ht0]
        ring
  exact hasDerivAt_of_periodic_fourier_derivative hv hd hvper hdper hc θ

section
include E hE b hbn

/-- The conormal-kernel rows solve the genuine homogeneous Ell² ODE.
The exceptional sqrt(2) scale is checked against its actual transport
coefficient, and all other derivatives are genuine Hilbert series. -/
theorem localConformalVekuaConormal_kernel_transport_hasDerivAt
    (hker : normalizedConormal hβF haF hgF (E : ℂ) b = 0)
     (hθ : θ ∈ Ioo 0 circlePeriod) :
    HasDerivAt
      (vekuaTransportVectorFixed E b)
      (transportCoeff (physicalCircleTraceFixed) E θ
        (vekuaTransportVectorFixed E b θ)) θ := by
  have hb1 := localConformalVekuaConormal_kernel_raw_H1 hR F hFs E b hker
  have hxcc := Ioo_subset_Icc_self hθ
  have hd0 : HasDerivAt
      (vekuaTransportCoordinateFixed E b 0)
      ((2 * (-(E : ℂ) / 4) * deriv (physicalCircleTraceFixed) θ *
        vekuaTraceRowFixed (E : ℂ) b 1 θ) / (Real.sqrt 2 : ℂ)) θ := by
    unfold localConformalVekuaTransportCoordinate
    simpa only [↓reduceIte] using
      (localConformalVekuaConormal_kernel_hasDerivAt_zero hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E b hbn hker θ).div_const (Real.sqrt 2)
  have he0 : ((2 * (-(E : ℂ) / 4) * deriv (physicalCircleTraceFixed) θ *
        vekuaTraceRowFixed (E : ℂ) b 1 θ) / (Real.sqrt 2 : ℂ)) =
      (transportCoeff (physicalCircleTraceFixed) E θ
        (vekuaTransportVectorFixed E b θ) : ComplexSeq) 0 := by
    rw [transportCoeff_coord_zero,
      localConformalVekuaTransportVector_coord hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E b hbn hb1 hxcc 1]
    simp  [localConformalVekuaTransportCoordinate]
    change _ = physicalDrivenQ E * _
    rw [← physicalDrivenQ_sq hE]
    have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num)
    have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
      simp_all
    field_simp
    linear_combination -(physicalDrivenQ E ^ 2 * deriv (physicalCircleTraceFixed) θ *
      vekuaTraceRowFixed E b 1 θ) * hs
  have hdp := (localConformalVekuaPositiveTransportVector_hasDerivAt hR F hFs hb hL hhol
    hinj hC hK e he hsource hes E b hbn hb1 hθ).congr_deriv
      (localConformalVekuaPositiveTransportDerivative_tsum_eq hR F hFs hb hL hhol hinj
        hC hK e he hsource hes E hE b hbn hb1 hxcc)
  have heq : vekuaTransportVectorFixed E b =ᶠ[𝓝 θ]
      fun x => vekuaTransportCoordinateFixed E b 0 x • basisVec 0 +
        localConformalVekuaPositiveTransportVector hR F hFs hb hL hhol hinj hC hK
          e he hsource hes E b x := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
    exact localConformalVekuaTransportVector_zero_add_positive hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 (Ioo_subset_Icc_self hx)
  apply ((((hd0.congr_deriv he0).smul_const (basisVec 0)).add hdp).congr_of_eventuallyEq heq).congr_deriv
  abel

/-- The genuine pointwise Hilbert ODE gives its actual integral equation
on the full closed interval, including both endpoint values. -/
theorem localConformalVekuaConormal_kernel_transport_integral_eq
    (hker : normalizedConormal hβF haF hgF (E : ℂ) b = 0)
     (hθ : θ ∈ boundaryInterval) :
    vekuaTransportVectorFixed E b θ =
      vekuaTransportVectorFixed E b 0 +
        ∫ s in (0 : ℝ)..θ, transportCoeff (physicalCircleTraceFixed) E s
          (vekuaTransportVectorFixed E b s) := by
  have hb1 := localConformalVekuaConormal_kernel_raw_H1 hR F hFs E b hker
  have hy := localConformalVekuaTransportVector_continuousOn hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn hb1
  have hΓ  :=
    contDiff_physicalCircleTrace_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hΓd := hΓ.continuous_deriv_one
  have hc : Continuous (transportCoeff (physicalCircleTraceFixed) E) := by
    unfold transportCoeff
    fun_prop
  have hsub : Icc 0 θ ⊆ boundaryInterval := Icc_subset_Icc le_rfl hθ.2
  have hg := hc.continuousOn.clm_apply hy
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.1 (hy.mono hsub)
    (fun s hs => localConformalVekuaConormal_kernel_transport_hasDerivAt hR F hFs hb hL hhol
      hinj hC hK e he hsource hes E hE b hbn hker ⟨hs.1, hs.2.trans_le hθ.2⟩)
    (by rw [← uIcc_of_le hθ.1] at hsub; exact (hg.mono hsub).intervalIntegrable)
  simpa only [add_comm] using sub_eq_iff_eq_add.mp hi.symm

/-- Genuine variation of constants for a conormal-kernel input. The
boundary vector is the actual transport applied to its proved datum. -/
theorem localConformalVekuaConormal_kernel_transport_eq
    (hker : normalizedConormal hβF haF hgF (E : ℂ) b = 0)
     (hW : IsTransport (physicalCircleTraceFixed) E W)
     (hθ : θ ∈ boundaryInterval) :
    vekuaTransportVectorFixed E b θ =
      W θ (vekuaTransportVectorFixed E b 0) := by
  have hb1 := localConformalVekuaConormal_kernel_raw_H1 hR F hFs E b hker
  obtain ⟨M, hM⟩ := exists_periodic_C1_density_lipschitz (physicalCircleTraceFixed)
    (contDiff_physicalCircleTrace_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top)))
    (physicalCircleTrace_periodic F)
  have hd := driven_eq_transport hM hW
    (continuous_const.aestronglyMeasurable : AEStronglyMeasurable (fun _ : ℝ => (0 : Ell2)) volume)
    (B := 0) (fun _ => by simp)
    (localConformalVekuaTransportVector_continuousOn hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1)
    (fun t ht => by
      simpa only [add_zero] using
        (localConformalVekuaConormal_kernel_transport_integral_eq hR F hFs hb hL hhol hinj hC hK
          e he hsource hes E hE b hbn hker (θ := t) ht)) θ hθ
  simpa only [map_zero, intervalIntegral.integral_zero, add_zero] using hd

end


end


section
include hb hL hhol hinj hC hK e he hsource hes

/-- A true nonzero basepoint cut rules out the conormal kernel at a
reference energy, even when that energy belongs to the original Neumann
spectrum. The proof uses the actual endpoint and the genuine Hilbert ODE. -/
theorem localConformalVekuaConormal_eq_zero_imp_of_cutC_ne_zero
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hker : normalizedConormal hβF haF hgF (E : ℂ) b = 0)
     (hW : IsTransport (physicalCircleTraceFixed) E W)
    (hcut : cutC (W circlePeriod) (basisVec 0) ≠ 0) : b = 0 := by
  have hb1 := localConformalVekuaConormal_kernel_raw_H1 hR F hFs E b hker
  let s  := hardyFourierTrace (normalizedHardyAverage b) 0 / (Real.sqrt 2)
  let y := vekuaTransportVectorFixed E b
  have hinit : y 0 = s • basisVec 0 :=
    localConformalVekuaTransportVector_origin hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1
  have hper : y circlePeriod = y 0 := by
    simpa only [zero_add] using localConformalVekuaTransportVector_periodic hR F hFs
      hb hL hhol hinj hC hK e he hsource hes E b 0
  have hT : circlePeriod ∈ boundaryInterval := ⟨Real.two_pi_pos.le, le_rfl⟩
  have hform := localConformalVekuaConormal_kernel_transport_eq hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E hE b hbn hker hW hT
  change y circlePeriod = W circlePeriod (y 0) at hform
  rw [hper, hinit] at hform
  obtain ⟨M, hM⟩ := exists_periodic_C1_density_lipschitz (physicalCircleTraceFixed)
    (contDiff_physicalCircleTrace_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top)))
    (physicalCircleTrace_periodic F)
  have hu : ContinuousLinearMap.adjoint (W circlePeriod) * W circlePeriod = 1 := by
    have hm := transport_mem_unitary hM hW hT
    rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hm
    exact hm.1
  have hadj := congrArg ((ContinuousLinearMap.adjoint (W circlePeriod))) hform
  change ContinuousLinearMap.adjoint (W circlePeriod) (s • basisVec 0) =
    ContinuousLinearMap.adjoint (W circlePeriod) (W circlePeriod (s • basisVec 0)) at hadj
  rw [map_smul, ← ContinuousLinearMap.mul_apply, hu, ContinuousLinearMap.one_apply] at hadj
  have hscut : s • cutC (W circlePeriod) (basisVec 0) = 0 := by
    simpa only [cutC, smul_sub, sub_eq_zero] using hadj
  have hs  := (smul_eq_zero.mp hscut).resolve_right hcut
  have hinit0 : y 0 = 0 := by rw [hinit, hs, zero_smul]
  have hyzero {t : ℝ} (ht : t ∈ boundaryInterval) : y t = 0 := by
    have he := localConformalVekuaConormal_kernel_transport_eq hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E hE b hbn hker hW ht
    change y t = W t (y 0) at he
    simpa only [hinit0, map_zero] using he
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hrowzero {t : ℝ} (ht : t ∈ boundaryInterval) :
      vekuaTraceRowFixed (E : ℂ) b 0 t = 0 := by
    have he := localConformalVekuaTransportVector_coord hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 ht 0
    change (y t) 0 = _ at he
    rw [hyzero ht] at he
    simp only [lp.coeFn_zero, Pi.zero_apply, localConformalVekuaTransportCoordinate, if_true] at he
    have hh := congrArg (fun z : ℂ => z * (Real.sqrt 2)) he.symm
    simpa only [div_mul_cancel₀ _ hsqrt, zero_mul] using hh
  apply localConformalVekuaH1_eq_zero_input_of_coordinate_trace_zero hR F hFs hb hL hhol hinj
    hC hK e he hsource hes E b hbn
  apply Lp.ext
  filter_upwards [localConformalVekua_coordinate_trace_reconstruction_ae hR F hFs hb hL hhol hinj
      hC hK e he hsource hes E b hbn hb1,
    ae_restrict_mem measurableSet_Ioc,
    Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc 0 circlePeriod))] with t ht hmem hzero
  simp only [localConformalVekuaH1AtBoundaryOrigin]
  rw [ht]
  have hz : hardyFourierTrace (normalizedHardyAverage (VB (E : ℂ) b)) t = 0 := by
    simpa only [localConformalVekuaTraceRow, pow_zero, ContinuousLinearMap.one_apply] using
      hrowzero (Ioc_subset_Icc_self hmem)
  exact hz.trans hzero.symm

/-- Reference-energy injectivity on the original full nonpositive space,
obtained from a genuine nonzero cut, without a nonresonance premise. -/
theorem localConformalVekuaConormal_injective_on_nonpositive_of_cutC_ne_zero
    E (hE : 0 ≤ E) 
    (hW : IsTransport (physicalCircleTraceFixed) E W)
    (hcut : cutC (W circlePeriod) (basisVec 0) ≠ 0) :
    InjOn (normalizedConormal hβF haF hgF (E : ℂ))
      {b : L2Z | IsNonpositiveFourierSupport b} := by
  intro b hb' d hd' hbd
  have hn : IsNonpositiveFourierSupport (b - d) := by
    intro n hn
    simp [hb' n hn, hd' n hn]
  have hzero : normalizedConormal hβF haF hgF (E : ℂ) (b - d) = 0 := by
    rw [map_sub, hbd, sub_self]
  exact sub_eq_zero.mp
    (localConformalVekuaConormal_eq_zero_imp_of_cutC_ne_zero hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E hE (b - d) hn hzero hW hcut)

end


end PhysicalCoordinates

end PolyaNeumann

end
