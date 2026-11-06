module

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


noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Filter Metric
open scoped Topology ComplexConjugate ContDiff


/-- The actual interval-integral series defining row n of a Vekua trace. -/
def volterraVekuaTraceRowTerm (γ : ℝ → ℂ) (E : ℂ) (h : ℝ → ℂ)
    (n j : ℕ) (θ : ℝ) : ℂ :=
  physicalVekuaCoeff E j * (γ θ - γ 0) ^ j *
    volterraPrimitiveIterate (fun s => conj (deriv γ s)) h (j + n) θ

def volterraVekuaTraceRow (γ : ℝ → ℂ) (E : ℂ) (h : ℝ → ℂ)
    (n : ℕ) (θ : ℝ) : ℂ :=
  ∑' j : ℕ, volterraVekuaTraceRowTerm γ E h n j θ

local notation "Φ22" => Icc 0

private theorem volterraVekuaTraceRowTerm_bound
     (hγ : ContDiff ℝ 1 γ) (hh : Continuous h) E
     (hM0 : 0 ≤ M) (hH0 : 0 ≤ H) (hR0 : 0 ≤ R)
    (hM : ∀ θ ∈ Φ22 (2 * Real.pi), ‖conj (deriv γ θ)‖ ≤ M)
    (hH : ∀ θ ∈ Φ22 (2 * Real.pi), ‖h θ‖ ≤ H)
    (hR : ∀ θ ∈ Φ22 (2 * Real.pi), ‖γ θ - γ 0‖ ≤ R)
    n j  (hθ : θ ∈ Φ22 (2 * Real.pi)) :
    ‖volterraVekuaTraceRowTerm γ E h n j θ‖ ≤
      H * (M * (2 * Real.pi)) ^ n / (n.factorial : ℝ) *
        ((‖E‖ / 4 * R * (M * (2 * Real.pi))) ^ j / (j.factorial : ℝ)) := by
  have ha : Continuous (fun s => conj (deriv γ s)) :=
    Complex.continuous_conj.comp hγ.continuous_deriv_one
  have hJ := volterraPrimitiveIterate_bound_uniform ha hh Real.two_pi_pos.le hM0 hH0
    hM hH (j + n) θ hθ
  have : n.factorial ≤ (j + n).factorial := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ j + n)
  have h_inl E j : ‖physicalVekuaCoeff E j‖ = (‖E‖ / 4) ^ j / (j.factorial : ℝ) := by
    simp only [physicalVekuaCoeff, norm_div, norm_pow, norm_neg, Complex.norm_natCast]
    norm_num
  simp [volterraVekuaTraceRowTerm, h_inl]
  calc
    _ ≤ (‖E‖ / 4) ^ j / j.factorial * R ^ j *
        (H * (M * (2 * Real.pi)) ^ (j + n) / ((j + n).factorial)) := by
      gcongr <;> exact hR θ hθ
    _ ≤ (‖E‖ / 4) ^ j / j.factorial * R ^ j *
        (H * (M * (2 * Real.pi)) ^ (j + n) / n.factorial) := by
      gcongr
    _ = _ := by
      simp [pow_add, mul_pow]
      ring

/-- Actual row-index factorial decay on the whole parameter interval. -/
theorem exists_volterraVekuaTraceRow_factorial_bound
     (hγ : ContDiff ℝ 1 γ) (hh : Continuous h) E :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      (∀ n θ, θ ∈ Φ22 (2 * Real.pi) →
        ‖volterraVekuaTraceRow γ E h n θ‖ ≤ C * B ^ n / (n.factorial : ℝ)) ∧
      (∀ n, ContinuousOn (volterraVekuaTraceRow γ E h n) (Φ22 (2 * Real.pi))) := by
  have hzero : 0 ∈ Φ22 (2 * Real.pi) := ⟨le_rfl, Real.two_pi_pos.le⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn
  obtain ⟨H, hH⟩ := isCompact_Icc.exists_bound_of_continuousOn hh.continuousOn
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hγ.continuous.sub continuous_const).continuousOn
  have hM0  := (norm_nonneg _).trans (hM 0 hzero)
  have hH0 := (norm_nonneg _).trans (hH 0 hzero)
  have hR0 := (norm_nonneg _).trans (hR 0 hzero)
  let B := M * (2 * Real.pi)
  let r := ‖E‖ / 4 * R * B
  let S := ∑' j : ℕ, r ^ j / j.factorial
  have hmaj n : Summable (fun j =>
      H * B ^ n / n.factorial * (r ^ j / j.factorial)) :=
    (Real.summable_pow_div_factorial r).mul_left _
  have hbd (n j : ℕ) θ (hθ : θ ∈ Φ22 (2 * Real.pi))  :=
    volterraVekuaTraceRowTerm_bound hγ hh E hM0 hH0 hR0 hM hH hR n j hθ
  refine ⟨H * S, B, mul_nonneg hH0 (tsum_nonneg fun _ => by positivity), (by dsimp only [B]; positivity), ?_, ?_⟩
  · intro n θ hθ
    have hn :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => hbd n j θ hθ) (hmaj n)
    calc
      _ ≤ _ := norm_tsum_le_tsum_norm hn
      _ ≤ _ := Summable.tsum_le_tsum (fun j => hbd n j θ hθ) hn (hmaj n)
      _ = _ := by rw [tsum_mul_left]; dsimp only [S]; ring
  · intro n
    apply (HasSumUniformlyOn.of_norm_le_summable (hmaj n) (hbd n)).tendstoUniformlyOn.continuousOn
    exact (Eventually.of_forall fun s : Finset ℕ => continuousOn_finset_sum s
      (fun j _ => (show Continuous (volterraVekuaTraceRowTerm γ E h n j) by
        exact (continuous_const.mul ((hγ.continuous.sub continuous_const).pow j)).mul
          (continuous_volterraPrimitiveIterate
            (Complex.continuous_conj.comp hγ.continuous_deriv_one) hh (j + n))).continuousOn)).frequently

theorem volterraVekuaTraceRow_zero_origin γ h E :
    volterraVekuaTraceRow γ E h 0 0 = h 0 := by
  unfold volterraVekuaTraceRow
  rw [tsum_eq_single 0]
  · simp [volterraVekuaTraceRowTerm, physicalVekuaCoeff, volterraPrimitiveIterate]
  · intro j hj
    simp [volterraVekuaTraceRowTerm, hj]

theorem volterraVekuaTraceRow_succ_origin γ h E n :
    volterraVekuaTraceRow γ E h (n + 1) 0 = 0 := by
  unfold volterraVekuaTraceRow
  calc
    _ = ∑' _ : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro j
      by_cases hj : j = 0
      · subst j
        simp [volterraVekuaTraceRowTerm, volterraPrimitiveIterate]
      · simp [volterraVekuaTraceRowTerm, hj]
    _ = 0 := tsum_zero

/-- The positive row recurrence is the derivative of the actual Volterra
series. A summable derivative majorant justifies the differentiation. -/
theorem volterraVekuaTraceRow_hasDerivAt_succ
     (hγ : ContDiff ℝ 1 γ) (hh : Continuous h)
    E n  (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
    HasDerivAt (volterraVekuaTraceRow γ E h (n + 1))
      ((-E / 4) * deriv γ θ * volterraVekuaTraceRow γ E h (n + 2) θ +
        conj (deriv γ θ) * volterraVekuaTraceRow γ E h n θ) θ := by
  obtain ⟨A, B, r, hA, hB, hr, hbd⟩ : ∃ A B r : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ r ∧ ∀ n j θ, θ ∈ Φ22 (2 * Real.pi) → ‖volterraVekuaTraceRowTerm γ E h n j θ‖ ≤ A * B ^ n / (n.factorial : ℝ) * (r ^ j / (j.factorial : ℝ)) := by
    have hzero : 0 ∈ Φ22 (2 * Real.pi) := ⟨le_rfl, Real.two_pi_pos.le⟩
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn
    obtain ⟨H, hH⟩ := isCompact_Icc.exists_bound_of_continuousOn hh.continuousOn
    obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (hγ.continuous.sub continuous_const).continuousOn
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 hzero)
    have hH0 := (norm_nonneg _).trans (hH 0 hzero)
    have hR0 := (norm_nonneg _).trans (hR 0 hzero)
    refine ⟨H, M * (2 * Real.pi), ‖E‖ / 4 * R * (M * (2 * Real.pi)),
      hH0, by positivity, by positivity, ?_⟩
    intro n j θ hθ
    exact volterraVekuaTraceRowTerm_bound hγ hh E hM0 hH0 hR0 hM hH hR n j hθ
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hγ.continuous_deriv_one.continuousOn
  have hM0 := (norm_nonneg _).trans (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  let k : ℕ → ℝ := fun l => A * B ^ l / l.factorial
  have hs l {x : ℝ} (hx : x ∈ Φ22 (2 * Real.pi)) :
      Summable (volterraVekuaTraceRowTerm γ E h l · x) := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun j => hbd l j x hx) ((Real.summable_pow_div_factorial r).mul_left (k l))
  let d  := fun j x =>
    conj (deriv γ x) * volterraVekuaTraceRowTerm γ E h n (j + 1) x +
      (-E / 4) * deriv γ x * volterraVekuaTraceRowTerm γ E h (n + 2) j x
  let u : ℕ → ℝ := fun j =>
    (M * k n * r + ‖-E / 4‖ * M * k (n + 2)) * (r ^ j / j.factorial)
  have hd j x (_hx : x ∈ Ioo 0 (2 * Real.pi)) :
      HasDerivAt (volterraVekuaTraceRowTerm γ E h (n + 1) (j + 1)) (d j x) x :=
    (show HasDerivAt (volterraVekuaTraceRowTerm γ E h (n + 1) (j + 1)) (conj (deriv γ x) * volterraVekuaTraceRowTerm γ E h n (j + 1) x + (-E / 4) * deriv γ x * volterraVekuaTraceRowTerm γ E h (n + 2) j x) x by
      have ha : Continuous (fun s => conj (deriv γ s)) :=
        Complex.continuous_conj.comp hγ.continuous_deriv_one
      have hJ := hasDerivAt_volterraPrimitiveIterate_succ ha hh ((j + 1) + n) x
      rw [show j + 1 + n + 1 = j + 1 + (n + 1) by omega] at hJ
      have hd := (((hγ.differentiable_one x).hasDerivAt.sub_const (γ 0)).pow (j + 1)).mul hJ
      convert hd.const_mul (physicalVekuaCoeff E (j + 1)) using 1
      · funext x
        simp [volterraVekuaTraceRowTerm]
        ring
      · simpa [show (j + 1) + (n + 1) = j + (n + 2) by omega] using (show physicalVekuaCoeff E (j + 1) * (((j + 1 : ℕ) * (γ x - γ 0) ^ j * deriv γ x) * volterraPrimitiveIterate (fun s => conj (deriv γ s)) h (j + (n + 2)) x + (γ x - γ 0) ^ (j + 1) * (conj (deriv γ x) * volterraPrimitiveIterate (fun s => conj (deriv γ s)) h ((j + 1) + n) x)) = conj (deriv γ x) * volterraVekuaTraceRowTerm γ E h n (j + 1) x + (-E / 4) * deriv γ x * volterraVekuaTraceRowTerm γ E h (n + 2) j x by
          simp only [volterraVekuaTraceRowTerm]
          calc
            _ = physicalVekuaCoeff E (j + 1) * (j + 1 : ℕ) *
                deriv γ x * (γ x - γ 0) ^ j *
                  volterraPrimitiveIterate (fun s => conj (deriv γ s)) h (j + (n + 2)) x +
                conj (deriv γ x) * (physicalVekuaCoeff E (j + 1) * (γ x - γ 0) ^ (j + 1) *
                  volterraPrimitiveIterate (fun s => conj (deriv γ s)) h ((j + 1) + n) x) := by
                ring
            _ = _ := by rw [physicalVekuaCoeff_succ]; ring).symm)
  have hdb j x (hx : x ∈ Ioo 0 (2 * Real.pi)) : ‖d j x‖ ≤ u j := by
    have hxcc := Ioo_subset_Icc_self hx
    have ha : ‖conj (deriv γ x)‖ ≤ M := by simpa [Complex.norm_conj] using hM x hxcc
    have hfact : j.factorial ≤ (j + 1).factorial := by
      exact_mod_cast Nat.factorial_le (by omega : j ≤ j + 1)
    dsimp only [d]
    calc
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by
        simp only [norm_mul]
        apply add_le_add
        · exact mul_le_mul ha (hbd n (j + 1) x hxcc) (norm_nonneg _) hM0
        · exact mul_le_mul (mul_le_mul_of_nonneg_left (hM x hxcc) (norm_nonneg _))
            (hbd (n + 2) j x hxcc) (norm_nonneg _) (by positivity)
      _ ≤ M * (k n * (r ^ (j + 1) / j.factorial)) +
          ‖-E / 4‖ * M * (k (n + 2) * (r ^ j / j.factorial)) := by
        gcongr
      _ = _ := by dsimp only [u]; rw [pow_succ]; ring
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
  apply ((hd0.add hds).congr_of_eventuallyEq (by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
    exact (hs (n + 1) (Ioo_subset_Icc_self hx)).tsum_eq_zero_add)).congr_deriv
  rw [show (∑' j : ℕ, d j θ) = conj (deriv γ θ) * (∑' j : ℕ, volterraVekuaTraceRowTerm γ E h n (j + 1) θ) + (-E / 4) * deriv γ θ * volterraVekuaTraceRow γ E h (n + 2) θ by
    dsimp only [d, volterraVekuaTraceRow]
    rw [Summable.tsum_add (((summable_nat_add_iff 1).2 (hs n hxcc)).mul_left _)
      ((hs (n + 2) hxcc).mul_left _), tsum_mul_left, tsum_mul_left]]
  have hn := (hs n hxcc).tsum_eq_zero_add
  change volterraVekuaTraceRow γ E h n θ = _ at hn
  rw [hn]
  ring

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hb : Bornology.IsBounded (F '' ball 0 1))
    (hL : IsLipschitzDomain (F '' ball 0 1))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1))
    (hC : ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball 0 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : ↑e = F)
    (hsource : closedBall 0 1 ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target)

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

local notation "Φ10" => IsSobolevSeq 1

theorem localConformalHardyPrimitive_pow_raw_H1 b
    (hb1 : Φ10 (fromL2 (1 / 2) b)) n :
    Φ10 (fromL2 (1 / 2) ((JF ^ n) b)) := by
  rw [fromL2_localConformalHardyPrimitive_pow hR F hFs]
  exact (antiPrimIter_bound (by norm_num : (0 : ℝ) ≤ 1)
    (physicalCircleTrace_fourier_weights_of_smooth_neighborhood hR F hFs).1 hb1 n).1

/-- Every actual coordinate trace row equals its true interval-integral
series, for the full nonpositive input including frequency zero. -/
local notation "Φ0" => localConformalVekuaTraceRow hR F hFs hb hL hhol hinj hC hK e he hsource hes

local notation "Φ9" => physicalCircleTrace F

theorem localConformalVekuaTraceRow_eq_volterra E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : Φ10 (fromL2 (1 / 2) b)) n θ :
    Φ0 E b n θ =
      volterraVekuaTraceRow (Φ9) E
        (hardyFourierTrace (normalizedHardyAverage b)) n θ := by
  have hs := localConformalVekuaBoundary_average_volterra_hasSum_of_H1 hR F hFs hb hL
    hhol hinj hC hK e he hsource hes E ((JF ^ n) b) (localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol b hbn n) (localConformalHardyPrimitive_pow_raw_H1 hR F hFs b hb1 n) θ
  rw [show hardyFourierTrace (normalizedHardyAverage ((JF ^ n) b)) = volterraPrimitiveIterate (fun s => conj (deriv (Φ9) s)) (hardyFourierTrace (normalizedHardyAverage b)) n by
    funext s
    exact localConformalHardyPrimitive_pow_volterra_of_H1 hR F hFs hhol b hbn (isSobolevSeq_smul _ hb1) n s] at hs
  simp only [starRingEnd_apply] at hs
  change Φ0 E b n θ = _
  simpa only [localConformalVekuaTraceRow, volterraVekuaTraceRow,
    volterraVekuaTraceRowTerm, physicalCircleTrace, circleMap_zero,
    starRingEnd_apply, Complex.exp_zero, Complex.ofReal_zero, Complex.ofReal_one, zero_add,
    zero_mul, one_mul, mul_one, volterraPrimitiveIterate_iterate] using hs.tsum_eq.symm

theorem localConformalVekuaTraceRow_periodic E b n :
    Function.Periodic
      (Φ0 E b n)
      (2 * Real.pi) := hardyFourierTrace_periodic _

/-- The factorial decay is a bound on the actual Vekua trace rows. -/
local notation "Φ5" => localConformalVekuaTraceRow_eq_volterra hR F hFs hb hL hhol hinj hC hK e he hsource hes

local notation "Φ11" => Icc 0

theorem exists_localConformalVekuaTraceRow_factorial_bound E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : Φ10 (fromL2 (1 / 2) b)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ n θ, θ ∈ Φ11 (2 * Real.pi) →
        ‖Φ0 E b n θ‖ ≤ A * B ^ n / (n.factorial : ℝ)) ∧
      (∀ n, ContinuousOn
        (Φ0 E b n) (Φ11 (2 * Real.pi))) := by
  have havg : Φ10 (normalizedHardyAverage b) := isSobolevSeq_smul _ hb1
  obtain ⟨A, B, hA, hB, hbd, hc⟩ := exists_volterraVekuaTraceRow_factorial_bound (contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))) (continuous_hardyFourierTrace (sq_tsum_norm_le (s := 0) (by norm_num) (by simpa using havg)).1) E
  refine ⟨A, B, hA, hB, ?_, ?_⟩
  · intro n θ hθ
    rw [Φ5 E b hbn hb1]
    exact hbd n θ hθ
  · intro n
    rw [(show Φ0 E b n = volterraVekuaTraceRow (Φ9) E (hardyFourierTrace (normalizedHardyAverage b)) n by
      funext θ
      exact Φ5 E b hbn hb1 n θ)]
    exact hc n

/-- Physical transport coordinates retain y₀=U₀/√2 and yₙ=qⁿUₙ. -/
def localConformalVekuaTransportCoordinate (E : ℝ) (b : L2Z) (n : ℕ) (θ : ℝ) : ℂ :=
  if n = 0 then
    Φ0 (E : ℂ) b 0 θ / (Real.sqrt 2 : ℂ)
  else physicalDrivenQ E ^ n *
    Φ0 (E : ℂ) b n θ

/-- Genuine factorial majorants for the scaled Ell² coordinates. -/
local notation "Φ2" => localConformalVekuaTransportCoordinate hR F hFs hb hL hhol hinj hC hK e he hsource hes

local notation "Φ18" => exists_localConformalVekuaTraceRow_factorial_bound hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem exists_localConformalVekuaTransportCoordinate_factorial_bound E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : Φ10 (fromL2 (1 / 2) b)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ n θ, θ ∈ Φ11 (2 * Real.pi) →
        ‖Φ2 E b n θ‖ ≤ A * B ^ n / (n.factorial : ℝ)) ∧
      (∀ n, ContinuousOn
        (Φ2 E b n) (Φ11 (2 * Real.pi))) := by
  obtain ⟨A, B, hA, hB, hbd, hc⟩ := Φ18 E b hbn hb1
  refine ⟨A, ‖physicalDrivenQ E‖ * B, hA, mul_nonneg (norm_nonneg _) hB, ?_, ?_⟩
  · intro n θ hθ
    by_cases hn : n = 0
    · subst n
      simp only [localConformalVekuaTransportCoordinate, if_true, pow_zero,
        Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
      have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
      apply (div_le_iff₀ hs).2
      exact (show ‖Φ0 E b 0 θ‖ ≤ A by simpa using hbd 0 θ hθ).trans (le_mul_of_one_le_right hA (by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]))
    · rw [localConformalVekuaTransportCoordinate, if_neg hn, norm_mul, norm_pow]
      calc
        _ ≤ _ :=
          mul_le_mul_of_nonneg_left (hbd n θ hθ) (by positivity)
        _ = _ := by rw [mul_pow]; ring
  · intro n
    unfold localConformalVekuaTransportCoordinate
    by_cases hn : n = 0
    · simp [hn]
      exact (hc 0).div_const _
    · simp [hn]
      exact continuousOn_const.mul (hc n)

/-- An actual Ell² vector, synthesized from the true coordinate traces. -/
def localConformalVekuaTransportVector (E : ℝ) (b : L2Z) (θ : ℝ) : Ell2 :=
  ∑' n : ℕ, Φ2 E b n θ • basisVec n

private theorem vekuaTransport_norm_basisVec n : ‖basisVec n‖ = 1 := by
  rw [basisVec, lp.norm_single (by norm_num)]
  simp

local notation "Φ1" => localConformalVekuaTransportVector hR F hFs hb hL hhol hinj hC hK e he hsource hes

local notation "Φ17" => exists_localConformalVekuaTransportCoordinate_factorial_bound hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekuaTransportVector_hasSum E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : Φ10 (fromL2 (1 / 2) b))
     (hθ : θ ∈ Φ11 (2 * Real.pi)) :
    HasSum (fun n => Φ2 E b n θ • basisVec n)
      (Φ1 E b θ) := by
  apply Summable.hasSum
  apply Summable.of_norm
  simpa only [norm_smul, vekuaTransport_norm_basisVec, mul_one] using
    (by
      obtain ⟨A, B, hA, hB, hbd, hc⟩ := Φ17 E b hbn hb1
      exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hbd n θ hθ)
        (summable_volterraPrimitive_majorant A B))

/-- Every coordinate of the actual Ell² synthesis is the intended row. -/
local notation "Φ8" => localConformalVekuaTransportVector_hasSum hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekuaTransportVector_coord E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : Φ10 (fromL2 (1 / 2) b))
     (hθ : θ ∈ Φ11 (2 * Real.pi)) n :
    (Φ1 E b θ : ℕ → ℂ) n =
      Φ2 E b n θ := by
  have hm := (innerSL ℂ (basisVec n)).map_tsum ((Φ8 E b hbn hb1 hθ).summable)
  simp [inner_basisVec, basisVec_coord] at hm
  let c  := fun z => Φ2 E b z θ
  simpa [c] using (show (Φ1 E b θ) n = ∑' z : ℕ, if n = z then c z else 0 by
    simpa [c, localConformalVekuaTransportVector] using hm).trans (by
    calc
      _ = _ := by
        apply tsum_congr
        intro z
        by_cases hz : n = z
        · subst z; simp
        · have hzn := Ne.symm hz
          simp [hz, hzn]
      _ = _ := tsum_ite_eq n c)

theorem localConformalVekuaTransportVector_continuousOn E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : Φ10 (fromL2 (1 / 2) b)) :
    ContinuousOn (Φ1 E b) (Φ11 (2 * Real.pi)) := by
  obtain ⟨A, B, hA, hB, hbd, hc⟩ := Φ17 E b hbn hb1
  apply (show HasSumUniformlyOn (fun n θ => Φ2 E b n θ • basisVec n) (Φ1 E b) (Φ11 (2 * Real.pi)) by
    apply HasSumUniformlyOn.of_norm_le_summable (summable_volterraPrimitive_majorant A B)
    intro n θ hθ
    simpa only [norm_smul, vekuaTransport_norm_basisVec, mul_one] using hbd n θ hθ).tendstoUniformlyOn.continuousOn
  refine (Eventually.of_forall fun s : Finset ℕ => ?_).frequently
  apply continuousOn_finset_sum s
  intro n _
  exact (hc n).smul continuousOn_const

local notation "Φ6" => localConformalVekuaTraceRow_periodic hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekuaTransportVector_periodic E b :
    Function.Periodic (Φ1 E b) (2 * Real.pi) := by
  intro θ
  apply tsum_congr
  intro n
  unfold localConformalVekuaTransportCoordinate
  rw [Φ6 E b 0 θ,
    Φ6 E b n θ]

/-- The initial datum is proved from the actual zero-origin primitives. -/
local notation "Φ4" => localConformalVekuaTransportVector_coord hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekuaTransportVector_origin E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : Φ10 (fromL2 (1 / 2) b)) :
    Φ1 E b 0 =
      (hardyFourierTrace (normalizedHardyAverage b) 0 / (Real.sqrt 2 : ℂ)) • basisVec 0 := by
  apply lp.ext
  funext n
  rw [Φ4 E b hbn hb1 ⟨le_rfl, Real.two_pi_pos.le⟩]
  cases n with
  | zero =>
      have h_inl : Φ0 E b 0 0 = hardyFourierTrace (normalizedHardyAverage b) 0 := by
        rw [Φ5 E b hbn hb1, volterraVekuaTraceRow_zero_origin]
      simp [localConformalVekuaTransportCoordinate, h_inl, basisVec_coord]
  | succ n =>
      have h_inl n : Φ0 E b (n + 1) 0 = 0 := by
        rw [Φ5 E b hbn hb1, volterraVekuaTraceRow_succ_origin]
      simp [localConformalVekuaTransportCoordinate, Nat.succ_ne_zero, h_inl, basisVec_coord]

/-- The true derivative of positive coordinate n+1. It is not an assumed
transport coefficient: it comes from the scalar Volterra recurrence. -/
def localConformalVekuaPositiveTransportDerivative (E : ℝ) (b : L2Z)
    (n : ℕ) (θ : ℝ) : ℂ :=
  physicalDrivenQ E ^ (n + 1) *
    ((-(E : ℂ) / 4) * deriv (Φ9) θ *
        Φ0 (E : ℂ) b (n + 2) θ +
      conj (deriv (Φ9) θ) *
        Φ0 (E : ℂ) b n θ)

/-- The actual positive derivatives also have a genuine summable
factorial majorant, uniformly on the entire closed parameter interval. -/
local notation "Φ3" => localConformalVekuaPositiveTransportDerivative hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem exists_localConformalVekuaPositiveTransportDerivative_majorant E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : Φ10 (fromL2 (1 / 2) b)) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n θ, θ ∈ Φ11 (2 * Real.pi) →
      ‖Φ3 E b n θ‖ ≤ u n := by
  obtain ⟨A, B, hA, hB, hbd, hc⟩ := Φ18 (E : ℂ) b hbn hb1
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))).continuous_deriv_one.continuousOn
  have hM0 := (norm_nonneg _).trans (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  let D := ‖physicalDrivenQ E‖ * A * M * (‖-(E : ℂ) / 4‖ * B ^ 2 + 1)
  let r := ‖physicalDrivenQ E‖ * B
  refine ⟨fun n => D * r ^ n / (n.factorial : ℝ),
    summable_volterraPrimitive_majorant D r, ?_⟩
  intro n θ hθ
  have : (n.factorial : ℝ) ≤ (n + 2).factorial := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ n + 2)
  simp [localConformalVekuaPositiveTransportDerivative]
  calc
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ _ := by
      simp only [norm_mul, Complex.norm_conj]
      apply mul_le_mul_of_nonneg_left
      · apply add_le_add
        · calc
            ‖-(E : ℂ) / 4‖ * ‖deriv (Φ9) θ‖ *
                ‖Φ0 (E : ℂ) b (n + 2) θ‖
                ≤ ‖-(E : ℂ) / 4‖ * M *
                    ‖Φ0 (E : ℂ) b (n + 2) θ‖ := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left (hM θ hθ) (norm_nonneg _))
                    (norm_nonneg _)
            _ ≤ _ := by
                  exact mul_le_mul_of_nonneg_left (hbd (n + 2) θ hθ)
                    (mul_nonneg (norm_nonneg _) hM0)
        · calc
            ‖deriv (Φ9) θ‖ *
                ‖Φ0 (E : ℂ) b n θ‖
                ≤ M * ‖Φ0 (E : ℂ) b n θ‖ := by
                  exact mul_le_mul_of_nonneg_right (hM θ hθ) (norm_nonneg _)
            _ ≤ M * (A * B ^ n / (n.factorial : ℝ)) := by
                  exact mul_le_mul_of_nonneg_left (hbd n θ hθ) hM0
      · positivity
    _ ≤ ‖physicalDrivenQ E‖ ^ (n + 1) *
        (‖-(E : ℂ) / 4‖ * M * (A * B ^ (n + 2) / (n.factorial : ℝ)) +
          M * (A * B ^ n / (n.factorial : ℝ))) := by
      gcongr
    _ = _ := by
      dsimp only [D, r]
      rw [pow_succ, pow_add, mul_pow]
      ring

/-- The positive part is a genuine Ell² series of the actual traces. -/
def localConformalVekuaPositiveTransportVector (E : ℝ) (b : L2Z) (θ : ℝ) : Ell2 :=
  ∑' n : ℕ, Φ2 E b (n + 1) θ • basisVec (n + 1)

/-- Separating the exceptional zeroth row is justified by actual
absolute convergence, rather than by a formal rearrangement. -/
local notation "Φ15" => localConformalVekuaPositiveTransportVector hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekuaTransportVector_zero_add_positive E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : Φ10 (fromL2 (1 / 2 : ℝ) b))
     (hθ : θ ∈ Φ11 (2 * Real.pi)) :
    Φ1 E b θ =
      Φ2 E b 0 θ • basisVec 0 +
        Φ15 E b θ :=
  (Φ8 E b hbn hb1 hθ).summable.tsum_eq_zero_add

/-- Genuine Hilbert-space differentiation of the whole positive part.
Both the row and derivative series are justified by summable majorants. -/
local notation "Φ19" => exists_localConformalVekuaPositiveTransportDerivative_majorant hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekuaPositiveTransportVector_hasDerivAt E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : Φ10 (fromL2 (1 / 2) b))
     (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
    HasDerivAt
      (Φ15 E b)
      (∑' n : ℕ, Φ3 E b n θ • basisVec (n + 1)) θ := by
  obtain ⟨u, hu, hbd⟩ := Φ19 E b hbn hb1
  have hg n x (hx : x ∈ Ioo 0 (2 * Real.pi)) :
      HasDerivAt
        (fun t => Φ2 E b (n + 1) t • basisVec (n + 1))
        (Φ3 E b n x • basisVec (n + 1)) x :=
    have h_inl : HasDerivAt (Φ2 E b (n + 1)) (Φ3 E b n x) x := by
      unfold localConformalVekuaTransportCoordinate localConformalVekuaPositiveTransportDerivative
      have h_inl : HasDerivAt (Φ0 E b (n + 1)) ((-E / 4) * deriv (Φ9) x * Φ0 E b (n + 2) x + conj (deriv (Φ9) x) * Φ0 E b n x) x := by
        have hfun k :
            Φ0 E b k =
              volterraVekuaTraceRow (Φ9) E
                (hardyFourierTrace (normalizedHardyAverage b)) k := by
          funext x
          exact Φ5 E b hbn hb1 k x
        rw [hfun (n + 1), hfun (n + 2), hfun n]
        have havg : Φ10 (normalizedHardyAverage b) := isSobolevSeq_smul _ hb1
        exact volterraVekuaTraceRow_hasDerivAt_succ
          (contDiff_physicalCircleTrace_of_neighborhood hR F
            (hFs.of_le (WithTop.coe_le_coe.mpr le_top)))
          (continuous_hardyFourierTrace (sq_tsum_norm_le (s := 0) (by norm_num)
            (by simpa using havg)).1) E n hx
      simpa [Nat.succ_ne_zero, Nat.add_one_ne_zero, ↓reduceIte] using
          h_inl.const_mul (physicalDrivenQ E ^ (n + 1))
    h_inl.smul_const _
  have hgb n x (hx : x ∈ Ioo 0 (2 * Real.pi)) :
      ‖Φ3 E b n x • basisVec (n + 1)‖ ≤ u n := by
    simpa only [norm_smul, vekuaTransport_norm_basisVec, mul_one] using
      hbd n x (Ioo_subset_Icc_self hx)
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo _ _).isPreconnected
    hg hgb hθ ((summable_nat_add_iff 1).2 ((Φ8 E b hbn hb1 (Ioo_subset_Icc_self hθ)).summable)) hθ

/-- The computed positive derivative has exactly the corresponding
coordinate of the original physical transport coefficient. -/
theorem localConformalVekuaPositiveTransportDerivative_eq_transportCoeff_coord
    E (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hb1 : Φ10 (fromL2 (1 / 2) b)) n
     (hθ : θ ∈ Φ11 (2 * Real.pi)) :
    Φ3 E b n θ =
      (transportCoeff (Φ9) E θ
        (Φ1 E b θ) : ℕ → ℂ) (n + 1) := by
  rw [transportCoeff_apply_coord, shiftN_apply_succ,
    Φ4 E b hbn hb1 hθ (n + 2),
    Φ4 E b hbn hb1 hθ n]
  change _ = physicalDrivenQ E * _
  unfold localConformalVekuaPositiveTransportDerivative
  rw [← physicalDrivenQ_sq hE]
  cases n with
  | zero =>
      simp only [localConformalVekuaTransportCoordinate, shiftWeight, if_true,
        Nat.succ_ne_zero, if_false, one_mul, pow_one]
      field_simp [(by
        exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne')]
      <;> ring
  | succ n =>
      simp only [localConformalVekuaTransportCoordinate, shiftWeight, Nat.succ_ne_zero,
        if_false, one_mul, pow_succ, pow_zero, mul_one]
      ring

/-- The positive derivative is the genuine physical transport term with
its exceptional zeroth coordinate removed. -/
theorem localConformalVekuaPositiveTransportDerivative_tsum_eq
    E (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hb1 : Φ10 (fromL2 (1 / 2 : ℝ) b))
     (hθ : θ ∈ Φ11 (2 * Real.pi)) :
    (∑' n : ℕ, Φ3 E b n θ • basisVec (n + 1)) =
      transportCoeff (Φ9) E θ
          (Φ1 E b θ) -
        ((transportCoeff (Φ9) E θ
          (Φ1 E b θ) : ℕ → ℂ) 0) • basisVec 0 := by
  apply lp.ext
  funext n
  have hm := (innerSL ℂ (basisVec n)).map_tsum (show Summable (fun n => Φ3 E b n θ • basisVec (n + 1)) by
    obtain ⟨u, hu, hbd⟩ := Φ19 E b hbn hb1
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hu
    intro n
    simpa only [norm_smul, vekuaTransport_norm_basisVec, mul_one] using hbd n θ hθ)
  simp [inner_basisVec, basisVec_coord] at hm
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
      let c  := fun z => Φ3 E b z θ
      calc
        _ = _ := by simpa [c] using (by
          calc
            _ = _ := by
              apply tsum_congr
              intro z
              by_cases hz : n = z
              · subst z; simp
              · have hzn := Ne.symm hz
                simp [hz, hzn]
            _ = _ := tsum_ite_eq n c)
        _ = _ := localConformalVekuaPositiveTransportDerivative_eq_transportCoeff_coord
          hR F hFs hb hL hhol hinj hC hK e he hsource hes E hE b hbn hb1 n hθ

/-- Kernel inputs obtain the regularity needed by the actual transport
construction from the proved normalized-conormal smoothing formula. -/
local notation "Φ12" => normalizedConormal hβF haF hgF

theorem localConformalVekuaConormal_kernel_raw_H1 (E : ℂ) b
    (hker : Φ12 E b = 0) :
    Φ10 (fromL2 (1 / 2 : ℝ) b) :=
  (show Φ10 (fromL2 (1 / 2 : ℝ) b) by
    have he := congrArg (fun A : L2Z →L[ℂ] L2Z => A b)
      (normalizedConormal_sub_one_eq hβF haF hgF E)
    simp [hker] at he
    rw [(show b = sobolevSmoothing 1 zero_le_one (b - conormalRemOp (by norm_num) hβF haF hgF E b) by
      simpa [← map_neg] using (congrArg Neg.neg he)), fromL2_half_smoothing_one]
    exact (sobNormSq_mono (by norm_num : 1 ≤ (1 / 2 : ℝ) + 1)
      (isSobolevSeq_fromL2 ((1 / 2 : ℝ) + 1) _)).1)

theorem localConformalVekuaTraceRow_continuous E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hb1 : Φ10 (fromL2 (1 / 2) b)) n :
    Continuous (Φ0 E b n) := by
  exact continuous_hardyFourierTrace (sq_tsum_norm_le (s := 0) (by norm_num)
    (by simpa using (show Φ10 (normalizedHardyAverage (VB E ((JF ^ n) b))) by exact isSobolevSeq_smul (Real.sqrt (2 * Real.pi))⁻¹ (localConformalVekuaBoundary_raw_H1 hR F hFs hb hL hhol hinj hC hK e he hsource hes E ((JF ^ n) b) (localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol b hbn n) (localConformalHardyPrimitive_pow_raw_H1 hR F hFs b hb1 n))))).1

private theorem transport_fourier_coeff_ae  (v : BoundaryL2)
    (hv : v =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] f) n :
    boundaryFourier v n = (Real.sqrt (2 * Real.pi) : ℂ) *
      fourierCoeffOn Real.two_pi_pos f n := by
  rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hv]

/-- The actual conormal kernel determines the exceptional zeroth-row
derivative. Fourier inversion is applied to two genuine continuous
periodic functions; no differentiability of this row is assumed. -/
local notation "Φ7" => localConformalVekua_coordinate_trace_reconstruction_ae hR F hFs hb hL hhol hinj hC hK e he hsource hes

local notation "Φ14" => localConformalVekuaTraceRow_continuous hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekuaConormal_kernel_hasDerivAt_zero E (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b)
    (hker : Φ12 E b = 0) θ :
    HasDerivAt
      (Φ0 E b 0)
      (2 * (-E / 4) * deriv (Φ9) θ *
        Φ0 E b 1 θ) θ := by
  have hb1 := localConformalVekuaConormal_kernel_raw_H1 hR F hFs E b hker
  let v  := Φ0 E b 0
  let d  := fun t => 2 * (-E / 4) * deriv (Φ9) t *
    Φ0 E b 1 t
  have hd : Continuous d :=
    (continuous_const.mul (contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))).continuous_deriv_one).mul
      (Φ14 E b hbn hb1 1)
  let TF := localConformalDiskH1Trace hR F hFs hL
  let VF := localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes
  let Vel := boundaryContinuousMultiplier (localConformalVelocityCircle F)
  let G  := Vel (TF (VF (F 1) E (JF b)))
  let L := (2 * (-E / 4)) • G
  have ht0 : TF (VF (F 1) E b)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] v := by
    simp [v, TF, VF]
    unfold localConformalVekuaTraceRow
    simpa using
      Φ7 E b hbn hb1
  have ht1 := Φ7 E (JF b) (localConformalHardyPrimitive_nonpositive hR F hFs hhol b hbn) (by
      simpa using localConformalHardyPrimitive_pow_raw_H1 hR F hFs b hb1 1)
  have hc n : fourierCoeffOn Real.two_pi_pos d n =
      Complex.I * n * fourierCoeffOn Real.two_pi_pos v n := by
    have hNC := localConformalVekua_normalizedConormal_fourier hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 n
    simp only [hker, lp.coeFn_zero, Pi.zero_apply, localConformalVekuaGradientA_apply,
      map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hNC
    have hs0 : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
    apply mul_left_cancel₀ hs0
    calc
      _ = _ := (transport_fourier_coeff_ae L (by
        filter_upwards [Lp.coeFn_smul (2 * (-E / 4)) G,
          boundaryContinuousMultiplier_ae (localConformalVelocityCircle F) (TF (VF (F 1) E (JF b))),
          ht1] with t hL hG ht
        rw [hL]
        simp [G, Vel, TF, VF, hG, ht, localConformalVelocityCircle_apply hR F hFs, d, localConformalVekuaTraceRow]
        ring) n).symm
      _ = _ := by
        simp [L]
        have h2 : 2 * Complex.I * ((-E / 4) * boundaryFourier G n) =
            -n * boundaryFourier (TF (VF (F 1) E b)) n := by
          exact (sub_eq_zero.mp ((mul_eq_zero.mp hNC.symm).resolve_left (by
            exact_mod_cast (Real.rpow_pos_of_pos (sobWeight_pos n) (-(1 / 2))).ne'))).symm
        have hrel : 2 * (-E / 4) * boundaryFourier G n =
            Complex.I * n * boundaryFourier (TF (VF (F 1) E b)) n := by
          have hI : Complex.I ^ 2 = (-1) := by norm_num
          calc
            _ = -(Complex.I * (2 * Complex.I * ((-E / 4) * boundaryFourier G n))) := by
              have hassoc : Complex.I *
                  (2 * Complex.I * ((-E / 4) * boundaryFourier G n)) =
                  2 * Complex.I ^ 2 * ((-E / 4) * boundaryFourier G n) := by ring
              rw [hassoc, hI]
              ring
            _ = _ := by
              rw [h2]
            _ = _ := by ring
        rw [hrel]
      _ = _ := by
        rw [transport_fourier_coeff_ae _ ht0]
        ring
  exact hasDerivAt_of_periodic_fourier_derivative (Φ14 E b hbn hb1 0) hd (Φ6 E b 0) (by
    intro t
    dsimp only [d]
    rw [deriv_periodic (physicalCircleTrace_periodic F),
      Φ6 E b 1]) hc θ

/-- The conormal-kernel rows solve the genuine homogeneous Ell² ODE.
The exceptional sqrt(2) scale is checked against its actual transport
coefficient, and all other derivatives are genuine Hilbert series. -/
theorem localConformalVekuaConormal_kernel_transport_hasDerivAt
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hker : Φ12 E b = 0)
     (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
    HasDerivAt
      (Φ1 E b)
      (transportCoeff (Φ9) E θ
        (Φ1 E b θ)) θ := by
  have hb1 := localConformalVekuaConormal_kernel_raw_H1 hR F hFs E b hker
  have hxcc := Ioo_subset_Icc_self hθ
  apply (((((show HasDerivAt (Φ2 E b 0) ((2 * (-E / 4) * deriv (Φ9) θ * Φ0 E b 1 θ) / (Real.sqrt 2)) θ by
    unfold localConformalVekuaTransportCoordinate
    simpa [↓reduceIte] using
      (localConformalVekuaConormal_kernel_hasDerivAt_zero hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E b hbn hker θ).div_const (Real.sqrt 2)).congr_deriv (show 2 * (-E / 4) * deriv (Φ9) θ * Φ0 E b 1 θ / Real.sqrt 2 = (transportCoeff (Φ9) E θ (Φ1 E b θ)) 0 by
    rw [transportCoeff_coord_zero,
      Φ4 E b hbn hb1 hxcc 1]
    simp [localConformalVekuaTransportCoordinate, Nat.one_ne_zero]
    change _ = physicalDrivenQ E * _
    rw [← physicalDrivenQ_sq hE]
    have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp [(show (Real.sqrt 2 : ℂ) ≠ 0 by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne')]
    linear_combination -(physicalDrivenQ E ^ 2 * deriv (Φ9) θ *
      Φ0 E b 1 θ) * hs)).smul_const (basisVec 0)).add ((localConformalVekuaPositiveTransportVector_hasDerivAt hR F hFs hb hL hhol hinj hC hK e he hsource hes E b hbn hb1 hθ).congr_deriv (localConformalVekuaPositiveTransportDerivative_tsum_eq hR F hFs hb hL hhol hinj hC hK e he hsource hes E hE b hbn hb1 hxcc))).congr_of_eventuallyEq (by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
    exact localConformalVekuaTransportVector_zero_add_positive hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 (Ioo_subset_Icc_self hx))).congr_deriv
  abel

/-- Genuine variation of constants for a conormal-kernel input. The
boundary vector is the actual transport applied to its proved datum. -/
local notation "Φ13" => localConformalVekuaTransportVector_continuousOn hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekuaConormal_kernel_transport_eq
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hker : Φ12 E b = 0)
     (hW : IsTransport (Φ9) E W)
     (hθ : θ ∈ Φ11 (2 * Real.pi)) :
    Φ1 E b θ =
      W θ (Φ1 E b 0) := by
  obtain ⟨M, hM⟩ := exists_periodic_C1_density_lipschitz (Φ9)
    (contDiff_physicalCircleTrace_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top)))
    (physicalCircleTrace_periodic F)
  have hd := driven_eq_transport hM hW
    (continuous_const.aestronglyMeasurable : AEStronglyMeasurable (fun _ : ℝ => (0 : Ell2)) volume)
    (B := 0) (fun _ => by simp)
    (Φ13 E b hbn (localConformalVekuaConormal_kernel_raw_H1 hR F hFs E b hker))
    (fun t ht => by
      simpa using
        (by
          have hy := Φ13 E b hbn (localConformalVekuaConormal_kernel_raw_H1 hR F hFs E b hker)
          have hΓd := (contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))).continuous_deriv_one
          have hsub : Φ11 t ⊆ Φ11 (2 * Real.pi) := Icc_subset_Icc le_rfl ht.2
          simpa [add_comm] using sub_eq_iff_eq_add.mp (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hy.mono hsub) (fun s hs => localConformalVekuaConormal_kernel_transport_hasDerivAt hR F hFs hb hL hhol hinj hC hK e he hsource hes E hE b hbn hker ⟨hs.1, hs.2.trans_le ht.2⟩) (by rw [← uIcc_of_le ht.1] at hsub; exact (((show Continuous (transportCoeff (Φ9) E) by
            unfold transportCoeff
            fun_prop).continuousOn.clm_apply hy).mono hsub).intervalIntegrable)).symm)) θ hθ
  simpa using hd

include hb hL hhol hinj hC hK e he hsource hes in
/-- A true nonzero basepoint cut rules out the conormal kernel at a
reference energy, even when that energy belongs to the original Neumann
spectrum. The proof uses the actual endpoint and the genuine Hilbert ODE. -/
theorem localConformalVekuaConormal_eq_zero_imp_of_cutC_ne_zero
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hker : Φ12 E b = 0)
     (hW : IsTransport (Φ9) E W)
    (hcut : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) : b = 0 := by
  have hb1 := localConformalVekuaConormal_kernel_raw_H1 hR F hFs E b hker
  let s  := hardyFourierTrace (normalizedHardyAverage b) 0 / Real.sqrt 2
  let y := Φ1 E b
  have hinit : y 0 = s • basisVec 0 :=
    localConformalVekuaTransportVector_origin hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1
  have hT : 2 * Real.pi ∈ Φ11 (2 * Real.pi) := ⟨Real.two_pi_pos.le, le_rfl⟩
  have hform := localConformalVekuaConormal_kernel_transport_eq hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E hE b hbn hker hW hT
  change y (2 * Real.pi) = W (2 * Real.pi) (y 0) at hform
  rw [show y (2 * Real.pi) = y 0 by
    simpa using localConformalVekuaTransportVector_periodic hR F hFs
      hb hL hhol hinj hC hK e he hsource hes E b 0, hinit] at hform
  obtain ⟨M, hM⟩ := exists_periodic_C1_density_lipschitz (Φ9)
    (contDiff_physicalCircleTrace_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top)))
    (physicalCircleTrace_periodic F)
  have hadj := congrArg (fun z => ContinuousLinearMap.adjoint (W (2 * Real.pi)) z) hform
  change ContinuousLinearMap.adjoint (W (2 * Real.pi)) (s • basisVec 0) =
    ContinuousLinearMap.adjoint (W (2 * Real.pi)) (W (2 * Real.pi) (s • basisVec 0)) at hadj
  rw [map_smul, ← ContinuousLinearMap.mul_apply, (show ContinuousLinearMap.adjoint (W (2 * Real.pi)) * W (2 * Real.pi) = 1 by
    have hm := transport_mem_unitary hM hW hT
    rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint] at hm
    exact hm.1), ContinuousLinearMap.one_apply] at hadj
  have hyzero {t : ℝ} (ht : t ∈ Φ11 (2 * Real.pi)) : y t = 0 := by
    have he := localConformalVekuaConormal_kernel_transport_eq hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E hE b hbn hker hW ht
    change y t = W t (y 0) at he
    simpa [show y 0 = 0 by rw [hinit, ((smul_eq_zero.mp (show s • cutC (W (2 * Real.pi)) (basisVec 0) = 0 by
      simpa only [cutC, smul_sub, sub_eq_zero] using hadj)).resolve_right hcut), zero_smul]] using he
  have hrowzero {t : ℝ} (ht : t ∈ Φ11 (2 * Real.pi)) :
      Φ0 E b 0 t = 0 := by
    have he := Φ4 E b hbn hb1 ht 0
    change (y t) 0 = _ at he
    rw [hyzero ht] at he
    simp [localConformalVekuaTransportCoordinate] at he
    simpa [div_mul_cancel₀ _ (by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne')] using congrArg (fun z => z * (Real.sqrt 2 : ℂ)) he.symm
  apply localConformalVekuaH1_eq_zero_input_of_coordinate_trace_zero hR F hFs hb hL hhol hinj
    hC hK e he hsource hes E b hbn
  apply Lp.ext
  filter_upwards [Φ7 E b hbn hb1,
    ae_restrict_mem measurableSet_Ioc,
    Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc 0 (2 * Real.pi)))] with t ht hmem hzero
  simp [localConformalVekuaH1AtBoundaryOrigin]
  rw [ht]
  exact (show hardyFourierTrace (normalizedHardyAverage (VB E b)) t = 0 by
    simpa [localConformalVekuaTraceRow] using
      hrowzero (Ioc_subset_Icc_self hmem)).trans hzero.symm

include hb hL hhol hinj hC hK e he hsource hes in
/-- Reference-energy injectivity on the original full nonpositive space,
obtained from a genuine nonzero cut, without a nonresonance premise. -/
theorem localConformalVekuaConormal_injective_on_nonpositive_of_cutC_ne_zero
    (E : ℝ) (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport (Φ9) E W)
    (hcut : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) :
    InjOn (Φ12 (E : ℂ))
      {b : L2Z | IsNonpositiveFourierSupport b} := by
  intro b hb' d hd' hbd
  exact sub_eq_zero.mp
    (localConformalVekuaConormal_eq_zero_imp_of_cutC_ne_zero hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E hE (b - d) (by
        intro n hn
        simp [hb' n hn, hd' n hn]) (by
        rw [map_sub, hbd, sub_self]) hW hcut)

end PhysicalCoordinates

end PolyaNeumann

end
