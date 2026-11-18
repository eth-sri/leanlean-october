module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Integral
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
open Set MeasureTheory Filter
open scoped Topology ContDiff


/-- The kernel decreases when the positive Laplace parameter increases. -/
theorem laplaceKernelReal_antitone (a b t : ℝ) (ht : 0 < t)
    (z w : ℝ) (hzw : z ≤ w) :
    laplaceKernelReal a b w t ≤ laplaceKernelReal a b z t := by
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · apply Real.exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_right hzw ht.le)
    · exact Real.rpow_nonneg ht.le _
  · exact Real.rpow_nonneg (by linarith only [ht]) _

/-- The first argument derivative is the negative shifted kernel. -/
theorem hasDerivAt_laplaceKernelReal (a b z t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun w => laplaceKernelReal a b w t)
      (-laplaceKernelReal (a + 1) (b + 1) z t) z  := by
  have laplaceKernelReal_shift :
      laplaceKernelReal (a + 1) (b + 1) z t = t * laplaceKernelReal a b z t := by
    simp only [laplaceKernelReal]
    rw [show a + 1 - 1 = (a - 1) + 1 by ring,
      show b + 1 - (a + 1) - 1 = b - a - 1 by ring, Real.rpow_add_one ht.ne']
    ring
  have heq : -laplaceKernelReal (a + 1) (b + 1) z t =
      Real.exp (-(z * t)) * -(1 * t) * t ^ (a - 1) * (1 + t) ^ (b - a - 1) := by
    rw [laplaceKernelReal_shift]
    simp only [laplaceKernelReal]
    ring
  rw [heq]
  exact (((hasDerivAt_id z).mul_const t).neg.exp.mul_const (t ^ (a - 1))).mul_const ((1 + t) ^ (b - a - 1))

/-- The unnormalized Laplace integral. -/
def laplaceIntegral (a b z : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), laplaceKernelReal a b z t

/-- Differentiation of the integral by an exact simultaneous parameter shift. -/
theorem hasDerivAt_laplaceIntegral (a b z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    HasDerivAt (laplaceIntegral a b) (-laplaceIntegral (a + 1) (b + 1) z) z := by
  have hmeas : ∀ w : ℝ,
      AEStronglyMeasurable (laplaceKernelReal a b w) (volume.restrict (Ioi 0)) :=
    fun w => (continuousOn_laplaceKernelReal a b w).aestronglyMeasurable measurableSet_Ioi
  have hdmeas : AEStronglyMeasurable
      (fun t => -laplaceKernelReal (a + 1) (b + 1) z t)
      (volume.restrict (Ioi 0)) :=
    ((continuousOn_laplaceKernelReal (a + 1) (b + 1) z).aestronglyMeasurable
      measurableSet_Ioi).neg
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi 0), ∀ w ∈ Ioi (z / 2),
      ‖-laplaceKernelReal (a + 1) (b + 1) w t‖ ≤
        laplaceKernelReal (a + 1) (b + 1) (z / 2) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w hw
    rw [norm_neg, Real.norm_eq_abs,
      abs_of_pos (laplaceKernelReal_pos (a + 1) (b + 1) w t ht)]
    exact laplaceKernelReal_antitone (a + 1) (b + 1) t ht (z / 2) w hw.le
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioi 0), ∀ w ∈ Ioi (z / 2),
      HasDerivAt (fun u => laplaceKernelReal a b u t)
        (-laplaceKernelReal (a + 1) (b + 1) w t) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w _
    exact hasDerivAt_laplaceKernelReal a b w t ht
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioi_mem_nhds (by linarith only [hz] : z / 2 < z))
    (Eventually.of_forall hmeas) (integrableOn_laplaceKernelReal a b z ha hz)
    hdmeas hbound (integrableOn_laplaceKernelReal (a + 1) (b + 1) (z / 2) (add_pos ha zero_lt_one) (half_pos hz))
    hdiff
  change HasDerivAt (fun w => ∫ t in Ioi 0, laplaceKernelReal a b w t)
    (-∫ t in Ioi 0, laplaceKernelReal (a + 1) (b + 1) z t) z
  rw [← integral_neg]
  exact h.2

/-- The normalized integral is differentiable at every positive argument. -/
theorem hasDerivAt_UIr (a : Pos) (b z : ℝ) (hz : 0 < z) :
    HasDerivAt (UIr a b)
      (-(Real.Gamma a.1)⁻¹ * laplaceIntegral (a.1 + 1) (b + 1) z) z := by
  rw [neg_mul, ← mul_neg]
  exact (hasDerivAt_laplaceIntegral a.1 b z a.2 hz).const_mul (Real.Gamma a.1)⁻¹

/-- The unnormalized integral is differentiable throughout the positive half-line. -/
theorem differentiableOn_laplaceIntegral (a b : ℝ) (ha : 0 < a) :
    DifferentiableOn ℝ (laplaceIntegral a b) (Ioi 0) :=
  fun z hz => (hasDerivAt_laplaceIntegral a b z ha hz).differentiableAt.differentiableWithinAt

/-- Exact derivative of the unnormalized integral at a positive argument. -/
theorem deriv_laplaceIntegral (a b z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    deriv (laplaceIntegral a b) z = -laplaceIntegral (a + 1) (b + 1) z :=
  (hasDerivAt_laplaceIntegral a b z ha hz).deriv


/-- The positive Laplace integral is smooth, with the C-infinity order. -/
theorem contDiffOn_laplaceIntegral (a b : ℝ) (ha : 0 < a) :
    ContDiffOn ℝ (⊤ : ℕ∞) (laplaceIntegral a b) (Ioi 0)  := by
  have contDiffOn_laplaceIntegral_nat (n : ℕ) :
      ContDiffOn ℝ n (laplaceIntegral a b) (Ioi 0) := by
    induction n generalizing a b with
    | zero =>
        exact contDiffOn_zero.mpr (differentiableOn_laplaceIntegral a b ha).continuousOn
    | succ n ih =>
        change ContDiffOn ℝ ((n : ℕ∞ω) + 1) (laplaceIntegral a b) (Ioi 0)
        rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
        refine ⟨differentiableOn_laplaceIntegral a b ha, ?_, ?_⟩
        · intro hn
          exact False.elim (by simp at hn)
        · exact (ih (a + 1) (b + 1) (add_pos ha zero_lt_one)).neg.congr
            (fun z hz => deriv_laplaceIntegral a b z ha hz)
  exact contDiffOn_infty.mpr (fun n => contDiffOn_laplaceIntegral_nat n)

/-- Smoothness of the normalized integral on its genuine positive domain. -/
theorem contDiffOn_UIr (a : Pos) (b : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (UIr a b) (Ioi 0) :=
  contDiffOn_const.mul (contDiffOn_laplaceIntegral a.1 b a.2)

/-- Smoothness of the transformed negative-shape formula on the positive half-line. -/
theorem contDiffOn_UNr (a : NegThird) :
    ContDiffOn ℝ (⊤ : ℕ∞) (UNr a) (Ioi 0) :=
  (contDiffOn_id.rpow_const_of_ne (fun _ hz => ne_of_gt hz)).mul (contDiffOn_UIr _ _)


/-- The flux whose integral derivative supplies Kummer's equation. -/
def laplaceFlux (a b z t : ℝ) : ℝ :=
  Real.exp (-(z * t)) * t ^ a * (1 + t) ^ (b - a)









/-- First derivative of a power times a differentiable function. -/
theorem hasDerivAt_power_mul (f : ℝ → ℝ) (p z : ℝ) (hz : 0 < z)
    (hf : HasDerivAt f (deriv f z) z) :
    HasDerivAt (fun w => w ^ p * f w)
      (p * z ^ (p - 1) * f z + z ^ p * deriv f z) z :=
  (Real.hasDerivAt_rpow_const (Or.inl hz.ne')).mul hf

/-- Exact second derivative of a power product on the positive half-line. -/
theorem deriv_deriv_power_mul (f : ℝ → ℝ) (p z : ℝ) (hz : 0 < z)
    (hf : ∀ w ∈ Ioi (0 : ℝ), HasDerivAt f (deriv f w) w)
    (hf' : HasDerivAt (deriv f) (deriv (deriv f) z) z) :
    deriv (deriv (fun w => w ^ p * f w)) z =
      p * (p - 1) * z ^ (p - 2) * f z +
        2 * p * z ^ (p - 1) * deriv f z + z ^ p * deriv (deriv f) z := by
  have h1 := ((Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hz.ne')).const_mul p).mul
    (hf z hz)
  have heq : deriv (fun w => w ^ p * f w) =ᶠ[𝓝 z]
      fun w => p * w ^ (p - 1) * f w + w ^ p * deriv f w := by
    filter_upwards [Ioi_mem_nhds hz] with w hw
    exact (hasDerivAt_power_mul f p w hw (hf w hw)).deriv
  have h := ((h1.add ((Real.hasDerivAt_rpow_const (p := p) (Or.inl hz.ne')).mul hf')).congr_of_eventuallyEq heq).deriv
  rw [show p - 1 - 1 = p - 2 by ring] at h
  exact h.trans (by ring)

/-- Power transformation of Kummer's equation on the nonsingular domain. -/
theorem power_mul_kummer_ode (f : ℝ → ℝ) (c p z : ℝ) (hz : 0 < z)
    (hf : ∀ w ∈ Ioi (0 : ℝ), HasDerivAt f (deriv f w) w)
    (hf' : HasDerivAt (deriv f) (deriv (deriv f) z) z)
    (hode : z * deriv (deriv f) z + (p + 1 - z) * deriv f z - c * f z = 0) :
    z * deriv (deriv (fun w => w ^ p * f w)) z +
      (1 - p - z) * deriv (fun w => w ^ p * f w) z -
      (c - p) * (z ^ p * f z) = 0 := by
  rw [deriv_deriv_power_mul f p z hz hf hf',
    (hasDerivAt_power_mul f p z hz (hf z hz)).deriv]
  have h1 : z ^ (p - 1) = z ^ (p - 2) * z := by
    rw [← Real.rpow_add_one hz.ne']
    congr 1
    ring
  have h2 : z ^ p = z ^ (p - 2) * z * z := by
    rw [← h1, ← Real.rpow_add_one hz.ne']
    congr 1
    ring
  rw [h1, h2]
  linear_combination z ^ (p - 2) * z * z * hode

/-- The transformed negative-shape integral solves the required Kummer equation. -/
theorem UNr_ode (a : NegThird) (z : ℝ) (hz : 0 < z) :
    z * deriv (deriv (UNr a)) z + (2 / 3 - z) * deriv (UNr a) z - a.1 * UNr a z = 0  := by
  have UIr_ode (a : Pos) (b : ℝ) :
      z * deriv (deriv (UIr a b)) z + (b - z) * deriv (UIr a b) z - a.1 * UIr a b z = 0 := open MeasureTheory in by
    have deriv_deriv_UIr :
        deriv (deriv (UIr a b)) z =
        (Real.Gamma a.1)⁻¹ * laplaceIntegral (a.1 + 2) (b + 2) z := by
      have h := (hasDerivAt_laplaceIntegral (a.1 + 1) (b + 1) z
        (add_pos a.2 zero_lt_one) hz).const_mul (-(Real.Gamma a.1)⁻¹)
      have heq : deriv (UIr a b) =ᶠ[𝓝 z]
          fun w => -(Real.Gamma a.1)⁻¹ * laplaceIntegral (a.1 + 1) (b + 1) w := by
        filter_upwards [Ioi_mem_nhds hz] with w hw
        exact (hasDerivAt_UIr a b w hw).deriv
      have hd := (h.congr_of_eventuallyEq heq).deriv
      simpa only [neg_mul_neg, show a.1 + 1 + 1 = a.1 + 2 by ring,
        show b + 1 + 1 = b + 2 by ring] using hd
    have laplaceIntegral_moment_relation (a : ℝ) (ha : 0 < a) :
        a * laplaceIntegral a b z + (b - z) * laplaceIntegral (a + 1) (b + 1) z -
        z * laplaceIntegral (a + 2) (b + 2) z = 0 := by
      have hasDerivAt_laplaceFlux (t : ℝ) (ht : 0 < t) :
          HasDerivAt (laplaceFlux a b z)
          (a * laplaceKernelReal a b z t +
            (b - z) * laplaceKernelReal (a + 1) (b + 1) z t -
            z * laplaceKernelReal (a + 2) (b + 2) z t) t := by
        have ht1 := add_pos zero_lt_one ht
        have heq : a * laplaceKernelReal a b z t +
            (b - z) * laplaceKernelReal (a + 1) (b + 1) z t -
            z * laplaceKernelReal (a + 2) (b + 2) z t =
            (Real.exp (-(z * t)) * -(z * 1) * t ^ a +
              Real.exp (-(z * t)) * (a * t ^ (a - 1))) * (1 + t) ^ (b - a) +
            Real.exp (-(z * t)) * t ^ a * ((0 + 1) *
              ((b - a) * (1 + t) ^ (b - a - 1))) := by
          have hpa : t ^ a = t ^ (a - 1) * t := by
            rw [← Real.rpow_add_one ht.ne']
            congr 1
            ring
          have hpb : (1 + t) ^ (b - a) = (1 + t) ^ (b - a - 1) * (1 + t) := by
            rw [← Real.rpow_add_one ht1.ne']
            congr 1
            ring
          simp only [laplaceKernelReal]
          rw [show a + 1 - 1 = (a - 1) + 1 by ring,
            show a + 2 - 1 = (a - 1) + 1 + 1 by ring,
            show b + 1 - (a + 1) - 1 = b - a - 1 by ring,
            show b + 2 - (a + 2) - 1 = b - a - 1 by ring,
            Real.rpow_add_one ht.ne', Real.rpow_add_one ht.ne',
            Real.rpow_add_one ht.ne']
          simp only [hpa, hpb]
          ring
        rw [heq]
        convert (((hasDerivAt_id t).const_mul z).neg.exp.mul (Real.hasDerivAt_rpow_const (Or.inl ht.ne') : HasDerivAt (fun u => u ^ a) (a * t ^ (a - 1)) t)).mul (((hasDerivAt_const t 1).add (hasDerivAt_id t)).rpow_const (p := b - a) (Or.inl ht1.ne')) using 1
        · rfl
        · dsimp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply, id_eq]
          ring
      have tendsto_laplaceFlux_atTop :
          Tendsto (laplaceFlux a b z) atTop (𝓝 0) := by
        obtain ⟨n, hn⟩ := exists_nat_gt (b - a)
        have hlimit : Tendsto
            (fun t => 2 ^ n *
              (t ^ a * Real.exp (-z * t) + t ^ (a + (n : ℝ)) * Real.exp (-z * t)))
            atTop (𝓝 0) := by
          simpa using
            ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a z hz).add
              (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a + n) z hz)).const_mul
                (2 ^ n)
        apply squeeze_zero' _ _ hlimit
        · filter_upwards [Ioi_mem_atTop 0] with t ht
          exact (mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos ht _))
            (Real.rpow_pos_of_pos (add_pos zero_lt_one ht) _)).le
        · filter_upwards [Ioi_mem_atTop 0] with t ht
          have h := mul_le_mul_of_nonneg_left
            (one_add_rpow_le_polynomial (b - a) n hn.le t ht.le)
            (mul_pos (Real.exp_pos (-(z * t))) (Real.rpow_pos_of_pos ht a)).le
          rw [Real.rpow_add ht a (n : ℝ), Real.rpow_natCast]
          simp at h ⊢
          exact h.trans_eq (by ring)
      have continuousAt_laplaceFlux_zero :
          ContinuousAt (laplaceFlux a b z) 0 := by
        apply ContinuousAt.mul
        · exact ((continuous_const.mul continuous_id).neg.rexp.continuousAt).mul
            (Real.continuousAt_rpow_const 0 a (Or.inr ha.le))
        · exact (continuousAt_const.add continuousAt_id).rpow_const
            (Or.inl (by norm_num))
      have laplaceFlux_zero :
          laplaceFlux a b z 0 = 0 := by
        simp [laplaceFlux, Real.zero_rpow ha.ne']
      have h0 := integrableOn_laplaceKernelReal a b z ha hz
      have h1 := integrableOn_laplaceKernelReal (a + 1) (b + 1) z
        (add_pos ha zero_lt_one) hz
      have h2 := integrableOn_laplaceKernelReal (a + 2) (b + 2) z
        (by linarith only [ha]) hz
      have hf := integral_Ioi_of_hasDerivAt_of_tendsto
        (continuousAt_laplaceFlux_zero).continuousWithinAt
        (fun t ht => hasDerivAt_laplaceFlux t ht)
        (((h0.const_mul a).add (h1.const_mul (b - z))).sub (h2.const_mul z))
        (tendsto_laplaceFlux_atTop)
      rw [laplaceFlux_zero, sub_self] at hf
      have hsub := integral_sub ((h0.const_mul a).add (h1.const_mul (b - z)))
        (h2.const_mul z)
      have hadd := integral_add (h0.const_mul a) (h1.const_mul (b - z))
      simp at hsub hadd
      rwa [hsub, hadd, integral_const_mul, integral_const_mul, integral_const_mul] at hf
    rw [deriv_deriv_UIr, (hasDerivAt_UIr a b z hz).deriv]
    change z * ((Real.Gamma a.1)⁻¹ * laplaceIntegral (a.1 + 2) (b + 2) z) +
      (b - z) * (-(Real.Gamma a.1)⁻¹ * laplaceIntegral (a.1 + 1) (b + 1) z) -
      a.1 * ((Real.Gamma a.1)⁻¹ * laplaceIntegral a.1 b z) = 0
    have h := laplaceIntegral_moment_relation a.1 a.2
    linear_combination -(Real.Gamma a.1)⁻¹ * h
  let c : Pos := ⟨a.1 + 1 / 3, by linarith only [a.2.1]⟩
  have hf : ∀ w ∈ Ioi 0, HasDerivAt (UIr c (4 / 3))
      (deriv (UIr c (4 / 3)) w) w := by
    intro w hw
    exact (hasDerivAt_UIr c (4 / 3) w hw).differentiableAt.hasDerivAt
  have hf' := ((contDiffOn_UIr c (4 / 3)).deriv_of_isOpen isOpen_Ioi (by norm_num : 1 + 1 ≤ ∞))
    |>.differentiableOn (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hd := (hf' z hz).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have h := power_mul_kummer_ode (UIr c (4 / 3)) c.1 (1 / 3) z hz hf hd.hasDerivAt
    (by convert (UIr_ode c (4 / 3)) using 1; norm_num)
  rw [show c.1 - 1 / 3 = a.1 by dsimp only [c]; ring,
    show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at h
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

