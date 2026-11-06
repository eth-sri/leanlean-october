module

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
local notation "Φ0" => ball 0 1

def diskH1Trace : NeumannH1 (Φ0) →L[ℂ] BoundaryL2 :=
  h1BoundaryTrace unitDisk_bounded isLipschitzDomain_unitDisk unitCircle_isBoundaryParam

/-- The two actual weak-gradient components, in their physical L² space. -/
def diskH1Gradient (u : NeumannH1 (Φ0)) : DiskGradientSpace :=
  WithLp.toLp 2 (fun i => h1Gradient (Φ0) i u)

theorem norm_sq_diskH1Gradient u :
    ‖diskH1Gradient u‖ ^ 2 = ∑ i : Fin 2, ‖h1Gradient (Φ0) i u‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ _

/-- Orthonormal Fourier coordinates of the actual boundary trace. -/
def diskH1Fourier : NeumannH1 (Φ0) →L[ℂ] L2Z :=
  (boundaryFourier : BoundaryL2 →L[ℂ] L2Z).comp diskH1Trace

@[simp] theorem diskH1Fourier_apply u n :
    diskH1Fourier u n = (√(2 * π) : ℂ) *
      fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) n :=
  boundaryFourier_apply (diskH1Trace u) n

private lemma disk_integral_fourier r (n : ℤ) :
    (∫ θ in Ioc 0 (2 * π),
      r θ * Complex.exp (-((n : ℂ) * Complex.I * θ))) =
        (2 * π : ℂ) * fourierCoeffOn two_pi_pos r n := by
  rw [← intervalIntegral.integral_of_le two_pi_pos.le,
    ← coeffIntegral_eq_fourierCoeffOn]
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast two_pi_pos.ne'), one_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [mul_comm (r θ)]
  congr 1
  congr 1
  ring

private lemma unitCircle_mem_cutoff_ball θ :
    circleMap 0 1 θ ∈ ball 0 2 := by
  rw [mem_ball_zero_iff]
  simp

theorem disk_h1_fourier_green_pos m u :
    ⟪diskHolomorphicGradient m, diskH1Gradient u⟫_ℂ =
      (2 * π : ℂ) * (m : ℂ) *
        fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) (m : ℤ) := by
  have hgreen := h1_doubleLayer_green unitDisk_bounded isLipschitzDomain_unitDisk
    unitCircle_isBoundaryParam
    (diskHarmonicCutoff_testFunction (contDiff_diskAntiholomorphicMode m)) u
  change _ = ∫ θ in Ioc 0 (2 * π), diskH1Trace u θ * _ at hgreen
  rw [show (∫ z in Φ0, h1Value (Φ0) u z * lap (diskHarmonicCutoff (diskAntiholomorphicMode m)) z) = 0 by
    calc
      _ = ∫ _z in ball (0 : ℂ) 1, (0 : ℂ) := by
        apply setIntegral_congr_fun measurableSet_ball
        intro z hz
        dsimp only
        rw [lap_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hz),
          lap_diskAntiholomorphicMode, mul_zero]
      _ = 0 := by simp, zero_add, show (∑ i : Fin 2, ∫ z in Φ0, h1Gradient (Φ0) i u z * dirD (diskHarmonicCutoff (diskAntiholomorphicMode m)) (coordDir i) z) = ⟪diskHolomorphicGradient m, diskH1Gradient u⟫_ℂ by
    have h_inl m u : ⟪diskHolomorphicGradient m, diskH1Gradient u⟫_ℂ = ∑ i : Fin 2, ∫ z in Φ0, h1Gradient (Φ0) i u z * dirD (diskAntiholomorphicMode m) (coordDir i) z := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [diskHolomorphicGradient_ae m i] with z hz
      simp [hz, diskH1Gradient, PiLp.toLp_apply, conj_dirD_diskHolomorphicMode]
    rw [h_inl]
    apply Finset.sum_congr rfl
    intro i _
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    dsimp only
    rw [dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hz)], show (∫ θ in Ioc 0 (2 * π), diskH1Trace u θ * fderiv ℝ (diskHarmonicCutoff (diskAntiholomorphicMode m)) (circleMap 0 1 θ) (-(Complex.I * deriv (circleMap 0 1) θ))) = m * ((2 * π) * fourierCoeffOn two_pi_pos (diskH1Trace u) m) by
    rw [← disk_integral_fourier, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro θ _
    dsimp only
    rw [fderiv_diskHarmonicCutoff_eq (unitCircle_mem_cutoff_ball θ),
      conormal_diskAntiholomorphicMode, diskAntiholomorphicMode_unitCircle]
    simp
    ring] at hgreen
  exact hgreen.trans (by ring)

/-- The conjugate harmonic sector gives the negative Fourier frequencies. -/
theorem disk_h1_fourier_green_neg m u :
    ⟪diskAntiholomorphicGradient m, diskH1Gradient u⟫_ℂ =
      (2 * π : ℂ) * (m : ℂ) *
        fourierCoeffOn two_pi_pos (diskH1Trace u : ℝ → ℂ) (-(m : ℤ)) := by
  have hgreen := h1_doubleLayer_green unitDisk_bounded isLipschitzDomain_unitDisk
    unitCircle_isBoundaryParam
    (diskHarmonicCutoff_testFunction (contDiff_diskHolomorphicMode m)) u
  change _ = ∫ θ in Ioc 0 (2 * π), diskH1Trace u θ * _ at hgreen
  rw [show (∫ z in Φ0, h1Value (Φ0) u z * lap (diskHarmonicCutoff (diskHolomorphicMode m)) z) = 0 by
    calc
      _ = ∫ _z in ball (0 : ℂ) 1, (0 : ℂ) := by
        apply setIntegral_congr_fun measurableSet_ball
        intro z hz
        dsimp only
        rw [lap_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hz),
          lap_diskHolomorphicMode, mul_zero]
      _ = 0 := by simp, zero_add, show (∑ i : Fin 2, ∫ z in Φ0, h1Gradient (Φ0) i u z * dirD (diskHarmonicCutoff (diskHolomorphicMode m)) (coordDir i) z) = ⟪diskAntiholomorphicGradient m, diskH1Gradient u⟫_ℂ by
    have h_inl m u : ⟪diskAntiholomorphicGradient m, diskH1Gradient u⟫_ℂ = ∑ i : Fin 2, ∫ z in Φ0, h1Gradient (Φ0) i u z * dirD (diskHolomorphicMode m) (coordDir i) z := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [diskAntiholomorphicGradient_ae m i] with z hz
      simp [hz, diskH1Gradient, PiLp.toLp_apply, conj_dirD_diskAntiholomorphicMode]
    rw [h_inl]
    apply Finset.sum_congr rfl
    intro i _
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    dsimp only
    rw [dirD_diskHarmonicCutoff_eq (ball_subset_ball (by norm_num) hz)], show (∫ θ in Ioc 0 (2 * π), diskH1Trace u θ * fderiv ℝ (diskHarmonicCutoff (diskHolomorphicMode m)) (circleMap 0 1 θ) (-(Complex.I * deriv (circleMap 0 1) θ))) = m * ((2 * π) * fourierCoeffOn two_pi_pos (diskH1Trace u) (-m)) by
    rw [← disk_integral_fourier, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro θ _
    dsimp only
    rw [fderiv_diskHarmonicCutoff_eq (unitCircle_mem_cutoff_ball θ),
      conormal_diskHolomorphicMode, diskHolomorphicMode_unitCircle]
    simp
    ring] at hgreen
  exact hgreen.trans (by ring)

private lemma disk_normalized_coefficient_norm m a :
    ‖conj (diskHarmonicGradientScale m) *
        ((2 * π : ℂ) * ((m + 1 : ℕ) : ℂ) * a)‖ ^ 2 =
      ((m + 1 : ℕ) : ℝ) * ‖(√(2 * π) : ℂ) * a‖ ^ 2 := by
  have hscale : ‖diskHarmonicGradientScale m‖ =
      (Real.sqrt (2 * π * (m + 1 : ℕ)))⁻¹ :=
    Complex.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
  rw [norm_mul, Complex.norm_conj, hscale, norm_mul, norm_mul, show ‖(2 * π : ℂ)‖ = 2 * π by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.norm_of_nonneg two_pi_pos.le,
    Complex.norm_natCast, norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
  simp only [mul_pow, inv_pow]
  rw [Real.sq_sqrt (show 0 < 2 * π * (m + 1 : ℕ) by positivity).le, Real.sq_sqrt two_pi_pos.le]
  field_simp [two_pi_pos.ne', show (m + 1 : ℕ) ≠ 0 by positivity]

private lemma int_tsum_eq_halves (a : ℤ → ℝ) b
    (hb : Summable b) (hzero : a 0 = 0)
    (hpos : ∀ m : ℕ, a ((m + 1 : ℕ) : ℤ) = b (Sum.inl m))
    (hneg : ∀ m : ℕ, a (-((m + 1 : ℕ) : ℤ)) = b (Sum.inr m)) :
    Summable a ∧ (∑' n : ℤ, a n) = ∑' j : ℕ ⊕ ℕ, b j := by
  have hbl := hb.comp_injective Sum.inl_injective
  have hbr := hb.comp_injective Sum.inr_injective
  have hpos0 : Summable (fun m : ℕ => a m) :=
    (summable_nat_add_iff 1).mp (hbl.congr (fun m => (hpos m).symm))
  have hneg0 : Summable (fun m : ℕ => a (-(m + 1))) := by
    simpa using hbr.congr (fun m => (hneg m).symm)
  refine ⟨Summable.of_nat_of_neg_add_one hpos0 hneg0, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hpos0 hneg0, hpos0.tsum_eq_zero_add]
  simp [hzero]
  calc
    _ = _ := by
      congr 1
      · exact tsum_congr hpos
      · apply tsum_congr
        intro m
        simpa using hneg m
    _ = _ := (hbl.tsum_sum hbr).symm

/-- The weighted nonzero Fourier coefficients are summable, with the physical
gradient energy as their bound. Frequency zero contributes zero here. -/
theorem disk_h1_fourier_energy (u : NeumannH1 (Φ0)) :
    Summable (fun n : ℤ => |(n : ℝ)| * ‖diskH1Fourier u n‖ ^ 2) ∧
      (∑' n : ℤ, |(n : ℝ)| * ‖diskH1Fourier u n‖ ^ 2) ≤
        ‖diskH1Gradient u‖ ^ 2 := by
  let a : ℤ → ℝ := fun n => |(n : ℝ)| * ‖diskH1Fourier u n‖ ^ 2
  let b : ℕ ⊕ ℕ → ℝ := fun j =>
    ‖⟪diskNormalizedHarmonicGradient j, diskH1Gradient u⟫_ℂ‖ ^ 2
  have hpos m : a (m + 1 : ℕ) = b (Sum.inl m) := by
    simp only [a, b, Int.cast_natCast,
      abs_of_nonneg (Nat.cast_nonneg (m + 1) : 0 ≤ ((m + 1 : ℕ) : ℝ))]
    exact (show ‖⟪diskNormalizedHarmonicGradient (Sum.inl m), diskH1Gradient u⟫_ℂ‖ ^ 2 = ((m + 1 : ℕ) : ℝ) * ‖diskH1Fourier u ((m + 1 : ℕ) : ℤ)‖ ^ 2 by
      rw [diskNormalizedHarmonicGradient, inner_smul_left, disk_h1_fourier_green_pos,
        diskH1Fourier_apply]
      exact disk_normalized_coefficient_norm m _).symm
  have hneg m : a (-(m + 1 : ℕ)) = b (Sum.inr m) := by
    simp only [a, b, Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (m + 1) : 0 ≤ ((m + 1 : ℕ) : ℝ))]
    exact (show ‖⟪diskNormalizedHarmonicGradient (Sum.inr m), diskH1Gradient u⟫_ℂ‖ ^ 2 = ((m + 1 : ℕ) : ℝ) * ‖diskH1Fourier u (-((m + 1 : ℕ) : ℤ))‖ ^ 2 by
      rw [diskNormalizedHarmonicGradient, inner_smul_left, disk_h1_fourier_green_neg,
        diskH1Fourier_apply]
      exact disk_normalized_coefficient_norm m _).symm
  obtain ⟨ha, hsum⟩ := int_tsum_eq_halves a b (orthonormal_diskNormalizedHarmonicGradient.inner_products_summable (diskH1Gradient u)) (by simp [a]) hpos hneg
  refine ⟨ha, ?_⟩
  change (∑' n : ℤ, a n) ≤ _
  rw [hsum]
  exact orthonormal_diskNormalizedHarmonicGradient.tsum_inner_products_le (diskH1Gradient u)

private lemma disk_half_weight_norm u n :
    ‖(Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n‖ ^ 2 =
      ‖diskH1Fourier u n‖ ^ 2 + |(n : ℝ)| * ‖diskH1Fourier u n‖ ^ 2 := by
  rw [norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (sobWeight_pos n).le]
  unfold sobWeight
  ring

theorem disk_h1_half_trace_summable u :
    Summable (fun n =>
      ‖(Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n‖ ^ 2) :=
  ((summable_norm_sq_L2Z (diskH1Fourier u)).add
    (disk_h1_fourier_energy u).1).congr (fun n => (disk_half_weight_norm u n).symm)

/-- The weighted actual Fourier trace, first as a linear map. -/
def diskHalfTraceLin : NeumannH1 (Φ0) →ₗ[ℂ] L2Z where
  toFun u := ⟨fun n => (Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n,
    memℓp_two_iff_summable.mpr (disk_h1_half_trace_summable u)⟩
  map_add' u v := by
    apply lp.ext
    funext n
    change (Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier (u + v) n =
      (Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n +
        (Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier v n
    simp [mul_add]
  map_smul' c u := by
    apply lp.ext
    funext n
    change (Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier (c • u) n =
      c * ((Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n)
    simp
    ring

theorem norm_diskHalfTraceLin_le u :
    ‖diskHalfTraceLin u‖ ≤ Real.sqrt (‖diskH1Trace‖ ^ 2 + 1) * ‖u‖ := by
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (by
    rw [norm_sq_L2Z, mul_pow, Real.sq_sqrt (by positivity)]
    calc
      _ ≤ _ := (show (∑' n : ℤ, ‖(Real.sqrt (sobWeight n) : ℂ) * diskH1Fourier u n‖ ^ 2) ≤ ‖diskH1Trace u‖ ^ 2 + ‖diskH1Gradient u‖ ^ 2 by
        simp_rw [disk_half_weight_norm]
        rw [Summable.tsum_add (summable_norm_sq_L2Z (diskH1Fourier u))
          (disk_h1_fourier_energy u).1, ← norm_sq_L2Z]
        have hnorm : ‖diskH1Fourier u‖ = ‖diskH1Trace u‖ :=
          boundaryFourier.norm_map _
        rw [hnorm]
        exact add_le_add le_rfl (disk_h1_fourier_energy u).2)
      _ ≤ ‖diskH1Trace‖ ^ 2 * ‖u‖ ^ 2 + ‖u‖ ^ 2 :=
        add_le_add (by
          simpa [mul_pow] using
            (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (diskH1Trace.le_opNorm u)) (by
              rw [norm_sq_diskH1Gradient, h1_norm_sq]
              exact le_add_of_nonneg_left (sq_nonneg _))
      _ = _ := by ring)

/-- A bounded actual H¹-to-half-order Fourier trace on the unit disk. -/
def diskHalfTrace : NeumannH1 (Φ0) →L[ℂ] L2Z :=
  diskHalfTraceLin.mkContinuous (Real.sqrt (‖diskH1Trace‖ ^ 2 + 1))
    norm_diskHalfTraceLin_le

@[simp] theorem diskHalfTrace_apply u n :
    diskHalfTrace u n = (Real.sqrt (1 + |(n : ℝ)|) : ℂ) *
      boundaryFourier (diskH1Trace u) n := rfl

end PolyaNeumann

end
