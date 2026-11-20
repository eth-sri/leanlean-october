module

public import RequestProject.CircleFourier
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import RequestProject.DiskHarmonicModes
public import RequestProject.NeumannTraceInjective
public import RequestProject.BoundaryFourier
public import RequestProject.SobolevMultiplier
public import RequestProject.Herglotz

/-!
# The actual half-order H¹ trace on the unit disk

Green's identity is tested against compactly supported extensions of the
harmonic monomials. The resulting Fourier coefficients are the coefficients
of the actual H¹ boundary trace. Bessel's inequality in the physical gradient
Hilbert space controls the nonzero frequencies. The bounded L² trace controls
the remaining part of the weight, including frequency zero.

The Fourier transform is normalized for ordinary parameter measure `dθ`.
Accordingly the nonzero-frequency estimate has constant one in these
orthonormal Fourier coordinates, and constant `1 / (2π)` for average
Fourier coefficients. The disk is an auxiliary domain throughout.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter Real
open scoped Real ComplexConjugate InnerProductSpace Topology

/-- The already constructed physical trace, specialized to the unit disk. -/
def diskH1Trace : NeumannH1 (ball (0 : ℂ) 1) →L[ℂ] BoundaryL2 :=
  h1BoundaryTrace unitDisk_bounded isLipschitzDomain_unitDisk unitCircle_isBoundaryParam

section

variable (u : NeumannH1 (ball (0 : ℂ) 1))
include u

/-- The two actual weak-gradient components, in their physical L² space. -/
def diskH1Gradient  : DiskGradientSpace :=
  WithLp.toLp 2 (fun i => h1Gradient (ball (0 : ℂ) 1) i u)

theorem norm_sq_diskH1Gradient  :
    ‖diskH1Gradient u‖ ^ 2 = ∑ i : Fin 2, ‖h1Gradient (ball (0 : ℂ) 1) i u‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ _

theorem norm_sq_diskH1Gradient_le  :
    ‖diskH1Gradient u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [norm_sq_diskH1Gradient, h1_norm_sq]
  simp

end

/-- Orthonormal Fourier coordinates of the actual boundary trace. -/
def diskH1Fourier : NeumannH1 (ball (0 : ℂ) 1) →L[ℂ] L2Z :=
  (boundaryFourier : BoundaryL2 →L[ℂ] L2Z).comp diskH1Trace

@[simp] theorem diskH1Fourier_apply (u : NeumannH1 (ball (0 : ℂ) 1)) (n : ℤ) :
    diskH1Fourier u n = (√(2 * π) : ℂ) *
      fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) n :=
  boundaryFourier_apply (diskH1Trace u) n

private lemma disk_integral_fourier (r : ℝ → ℂ) (n : ℤ) :
    (∫ θ in Ioc (0 : ℝ) (2 * π),
      r θ * Complex.exp (-((n : ℂ) * Complex.I * θ))) =
        (2 * π : ℂ) * fourierCoeffOn two_pi_pos r n := by
  rw [← intervalIntegral.integral_of_le two_pi_pos.le,
    ← coeffIntegral_eq_fourierCoeffOn]
  have hpi : (2 * π : ℂ) ≠ 0 := by simp
  push_cast
  grind

private lemma unitCircle_mem_cutoff_ball (θ : ℝ) :
    circleMap 0 1 θ ∈ ball (0 : ℂ) 2 := by simp

private lemma disk_h1_fourier_green (u : NeumannH1 (ball (0 : ℂ) 1))
    {φ : ℂ → ℂ} (hs : ContDiff ℝ (⊤ : ℕ∞) φ) (hl : ∀ z, lap φ z = 0)
    (n : ℤ) (c : ℂ)
    (hν : ∀ θ, fderiv ℝ φ (circleMap 0 1 θ) (-(Complex.I * deriv (circleMap 0 1) θ)) =
      c * Complex.exp (-((n : ℂ) * Complex.I * θ)))
    (G : DiskGradientSpace)
    (hG : ∀ i, ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)),
      conj (G i z) = dirD φ (coordDir i) z) :
    ⟪G, diskH1Gradient u⟫_ℂ = (2 * π : ℂ) * c *
        fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) n := by
  have hd : ball (0 : ℂ) 1 ⊆ ball 0 2 := ball_subset_ball (by norm_num)
  have hm : (∫ z in ball (0 : ℂ) 1, h1Value (ball (0 : ℂ) 1) u z *
      lap (diskHarmonicCutoff φ) z) = 0 := by
    calc
      _ = ∫ _z in ball (0 : ℂ) 1, (0 : ℂ) :=
        setIntegral_congr_fun measurableSet_ball fun z hz => by
          simp [lap_diskHarmonicCutoff_eq (hd hz), hl]
      _ = 0 := by simp
  have hg : (∑ i : Fin 2, ∫ z in ball (0 : ℂ) 1, h1Gradient (ball (0 : ℂ) 1) i u z *
      dirD (diskHarmonicCutoff φ) (coordDir i) z) = ⟪G, diskH1Gradient u⟫_ℂ := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hG i, ae_restrict_mem measurableSet_ball] with z hzi hz
    simp [RCLike.inner_apply, diskH1Gradient, hzi, dirD_diskHarmonicCutoff_eq (hd hz)]
  have hgreen := h1_doubleLayer_green unitDisk_bounded isLipschitzDomain_unitDisk
    unitCircle_isBoundaryParam (diskHarmonicCutoff_testFunction hs) u
  change _ = ∫ θ in Ioc (0 : ℝ) (2 * π), diskH1Trace u θ * _ at hgreen
  rw [hm, zero_add, hg] at hgreen
  rw [hgreen, mul_comm (2 * π : ℂ), mul_assoc,
    ← disk_integral_fourier, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioc fun θ _ => by
    rw [fderiv_diskHarmonicCutoff_eq (unitCircle_mem_cutoff_ball θ), hν]
    ring

section

variable (m : ℕ) (u : NeumannH1 (ball (0 : ℂ) 1))
include m u

theorem disk_h1_fourier_green_pos :
    ⟪diskHolomorphicGradient m, diskH1Gradient u⟫_ℂ =
      (2 * π : ℂ) * (m : ℂ) * fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) (m : ℤ) := by
  refine disk_h1_fourier_green u (contDiff_diskAntiholomorphicMode m) (lap_diskAntiholomorphicMode m)
    m m (fun θ => ?_) _ (fun i => (diskHolomorphicGradient_ae m i).mono fun z hz => ?_)
  · rw [conormal_diskAntiholomorphicMode, diskAntiholomorphicMode_unitCircle, Int.cast_natCast]
  · rw [hz, conj_dirD_diskHolomorphicMode]

theorem disk_h1_fourier_green_neg :
    ⟪diskAntiholomorphicGradient m, diskH1Gradient u⟫_ℂ =
      (2 * π : ℂ) * (m : ℂ) * fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) (-(m : ℤ)) := by
  refine disk_h1_fourier_green u (contDiff_diskHolomorphicMode m) (lap_diskHolomorphicMode m)
    _ m (fun θ => ?_) _ (fun i => (diskAntiholomorphicGradient_ae m i).mono fun z hz => ?_)
  · rw [conormal_diskHolomorphicMode, diskHolomorphicMode_unitCircle]
    simp
  · rw [hz, conj_dirD_diskAntiholomorphicMode]

end

private lemma disk_normalized_coefficient_norm (m : ℕ) (a : ℂ) :
    ‖conj (diskHarmonicGradientScale m) *
        ((2 * π : ℂ) * ((m + 1 : ℕ) : ℂ) * a)‖ ^ 2 =
      ((m + 1 : ℕ) : ℝ) * ‖(√(2 * π) : ℂ) * a‖ ^ 2 := by
  have hp : 0 < 2 * π * ((m + 1 : ℕ) : ℝ) := by positivity
  have hk : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hscale : ‖diskHarmonicGradientScale m‖ =
      (Real.sqrt (2 * π * ((m + 1 : ℕ) : ℝ)))⁻¹ :=
    Complex.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hperiod : ‖(2 * π : ℂ)‖ = 2 * π := by
    simp
  rw [norm_mul, Complex.norm_conj, hscale, norm_mul, norm_mul, hperiod,
    Complex.norm_natCast, norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
  simp only [mul_pow, inv_pow]
  rw [Real.sq_sqrt hp.le, Real.sq_sqrt two_pi_pos.le]
  grind

section

variable (m : ℕ) (u : NeumannH1 (ball (0 : ℂ) 1))
include m u

theorem norm_sq_diskNormalizedHarmonicGradient_pos  :
    ‖⟪diskNormalizedHarmonicGradient (Sum.inl m), diskH1Gradient u⟫_ℂ‖ ^ 2 =
      ((m + 1 : ℕ) : ℝ) * ‖diskH1Fourier u ((m + 1 : ℕ) : ℤ)‖ ^ 2 := by
  rw [diskNormalizedHarmonicGradient, inner_smul_left, disk_h1_fourier_green_pos,
    diskH1Fourier_apply]
  exact disk_normalized_coefficient_norm m _

theorem norm_sq_diskNormalizedHarmonicGradient_neg  :
    ‖⟪diskNormalizedHarmonicGradient (Sum.inr m), diskH1Gradient u⟫_ℂ‖ ^ 2 =
      ((m + 1 : ℕ) : ℝ) * ‖diskH1Fourier u (-((m + 1 : ℕ) : ℤ))‖ ^ 2 := by
  rw [diskNormalizedHarmonicGradient, inner_smul_left, disk_h1_fourier_green_neg,
    diskH1Fourier_apply]
  exact disk_normalized_coefficient_norm m _

end


section

variable (u : NeumannH1 (ball (0 : ℂ) 1))
include u

/-- The weighted nonzero Fourier coefficients are summable, with the physical
gradient energy as their bound. Frequency zero contributes zero here. -/
theorem disk_h1_fourier_energy  :
    Summable (fun n : ℤ => |(n : ℝ)| * ‖diskH1Fourier u n‖ ^ 2) ∧
      (∑' n : ℤ, |(n : ℝ)| * ‖diskH1Fourier u n‖ ^ 2) ≤
        ‖diskH1Gradient u‖ ^ 2 := by
  let a : ℤ → ℝ := fun n => |(n : ℝ)| * ‖diskH1Fourier u n‖ ^ 2
  let b := fun j =>
    ‖⟪diskNormalizedHarmonicGradient j, diskH1Gradient u⟫_ℂ‖ ^ 2
  have hb :=
    orthonormal_diskNormalizedHarmonicGradient.inner_products_summable (diskH1Gradient u)
  have hpos (m : ℕ) : a ((m + 1 : ℕ) : ℤ) = b (Sum.inl m) := by
    simp only [a, Int.cast_natCast,
      abs_of_nonneg (Nat.cast_nonneg (m + 1) : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]
    exact (norm_sq_diskNormalizedHarmonicGradient_pos m u).symm
  have hneg (m : ℕ) : a (-((m + 1 : ℕ) : ℤ)) = b (Sum.inr m) := by
    simp only [a, Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (m + 1) : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))]
    exact (norm_sq_diskNormalizedHarmonicGradient_neg m u).symm
  obtain ⟨ha, hsum⟩ := int_tsum_eq_halves a b hb (by ring) hpos hneg
  refine ⟨ha, ?_⟩
  change (∑' n : ℤ, a n) ≤ _
  rw [hsum]
  exact orthonormal_diskNormalizedHarmonicGradient.tsum_inner_products_le (diskH1Gradient u)

private lemma disk_half_weight_norm  (n : ℤ) :
    ‖(Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n‖ ^ 2 =
      ‖diskH1Fourier u n‖ ^ 2 + |(n : ℝ)| * ‖diskH1Fourier u n‖ ^ 2 := by
  rw [norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (sobWeight_pos n).le]
  unfold sobWeight
  ring

theorem disk_h1_half_trace_summable  :
    Summable (fun n : ℤ =>
      ‖(Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n‖ ^ 2) :=
  ((summable_norm_sq_L2Z (diskH1Fourier u)).add
    (disk_h1_fourier_energy u).1).congr (fun n => (disk_half_weight_norm u n).symm)

/-- Half-order trace bound in the orthonormal Fourier coordinates. -/
theorem disk_h1_half_trace_bound  :
    (∑' n : ℤ, ‖(Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n‖ ^ 2) ≤
      ‖diskH1Trace u‖ ^ 2 + ‖diskH1Gradient u‖ ^ 2 := by
  simp_rw [disk_half_weight_norm]
  rw [Summable.tsum_add (summable_norm_sq_L2Z (diskH1Fourier u))
    (disk_h1_fourier_energy u).1, ← norm_sq_L2Z]
  have hnorm : ‖diskH1Fourier u‖ = ‖diskH1Trace u‖ :=
    boundaryFourier.norm_map _
  rw [hnorm]
  exact add_le_add le_rfl (disk_h1_fourier_energy u).2

end

/-- The weighted actual Fourier trace, first as a linear map. -/
def diskHalfTraceLin : NeumannH1 (ball (0 : ℂ) 1) →ₗ[ℂ] L2Z where
  toFun u := ⟨fun n => (Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n,
    memℓp_two_iff_summable.mpr (disk_h1_half_trace_summable u)⟩
  map_add' u v := by
    apply lp.ext
    funext n
    change (Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier (u + v) n =
      (Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n +
        (Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier v n
    simp only [map_add, lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c u := by
    apply lp.ext
    funext n
    change (Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier (c • u) n =
      c * ((Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n)
    simp only [map_smul, lp.coeFn_smul, Pi.smul_apply]
    ring

theorem norm_diskHalfTraceLin_le (u : NeumannH1 (ball (0 : ℂ) 1)) :
    ‖diskHalfTraceLin u‖ ≤ Real.sqrt (‖diskH1Trace‖ ^ 2 + 1) * ‖u‖ := by
  have ht : ‖diskH1Trace u‖ ^ 2 ≤ ‖diskH1Trace‖ ^ 2 * ‖u‖ ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (diskH1Trace.le_opNorm u)
  have hs : ‖diskHalfTraceLin u‖ ^ 2 ≤
      (Real.sqrt (‖diskH1Trace‖ ^ 2 + 1) * ‖u‖) ^ 2 := by
    rw [norm_sq_L2Z, mul_pow, Real.sq_sqrt (by positivity)]
    calc
      _ ≤ ‖diskH1Trace u‖ ^ 2 + ‖diskH1Gradient u‖ ^ 2 := disk_h1_half_trace_bound u
      _ ≤ ‖diskH1Trace‖ ^ 2 * ‖u‖ ^ 2 + ‖u‖ ^ 2 :=
        add_le_add ht (norm_sq_diskH1Gradient_le u)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs

/-- A bounded actual H¹-to-half-order Fourier trace on the unit disk. -/
def diskHalfTrace : NeumannH1 (ball (0 : ℂ) 1) →L[ℂ] L2Z :=
  diskHalfTraceLin.mkContinuous (Real.sqrt (‖diskH1Trace‖ ^ 2 + 1))
    norm_diskHalfTraceLin_le

@[simp] theorem diskHalfTrace_apply (u : NeumannH1 (ball (0 : ℂ) 1)) (n : ℤ) :
    diskHalfTrace u n = (Real.sqrt (1 + |(n : ℝ)|) : ℂ) *
      boundaryFourier (diskH1Trace u) n := rfl

end PolyaNeumann

end
