module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.BasisM
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.EulerIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsMoments
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsDerivatives
import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Topology.Piecewise
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarEquations

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
open Set MeasureTheory Real Filter
open scoped Topology

/-- A concave translated power differs from one by at most its linear tangent. -/
theorem one_add_rpow_sub_one_le (q s : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hs : 0 ≤ s) :
    (1 + s) ^ q - 1 ≤ q * s := by
  have hd : ∀ u ∈ Icc 0 s,
      HasDerivWithinAt (fun t : ℝ => (1 + t) ^ q)
        (q * (1 + u) ^ (q - 1)) (Icc 0 s) u := by
    intro u hu
    have hu1 := add_pos_of_pos_of_nonneg zero_lt_one hu.1
    have h := ((hasDerivAt_const u 1).add (hasDerivAt_id u)).rpow_const
      (p := q) (Or.inl hu1.ne')
    simpa using h.hasDerivWithinAt
  have hb : ∀ u ∈ Ico 0 s, ‖q * (1 + u) ^ (q - 1)‖ ≤ q := by
    intro u hu
    have hu1 : 1 ≤ 1 + u := by linarith only [hu.1]
    have hp : (1 + u) ^ (q - 1) ≤ 1 := by
      simpa using
        Real.rpow_le_rpow_of_exponent_le hu1 (sub_nonpos.mpr hq1)
    rw [Real.norm_of_nonneg (mul_nonneg hq (Real.rpow_nonneg (by linarith only [hu.1]) _))]
    exact (mul_le_mul_of_nonneg_left hp hq).trans_eq (mul_one q)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb s ⟨hs, le_rfl⟩
  simp at h
  exact (le_abs_self ((1 + s) ^ q - 1)).trans h

/-- The integrable difference used to renormalize the singular connection integral. -/
def connectionKernel (c t : ℝ) : ℝ :=
  t ^ (c - 1) * (1 + t) ^ (1 / 3 - c) - t ^ (-(2 / 3 : ℝ))

/-- The renormalized kernel is nonnegative for the shifted source parameter range. -/
theorem connectionKernel_nonneg (c t : ℝ) (hc : c ≤ 1 / 3) (ht : 0 < t) :
    0 ≤ connectionKernel c t := by
  have hp : t ^ (1 / 3 - c) ≤ (1 + t) ^ (1 / 3 - c) :=
    Real.rpow_le_rpow ht.le (by linarith) (sub_nonneg.mpr hc)
  have h := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg ht.le (c - 1))
  rw [← Real.rpow_add ht] at h
  rw [show c - 1 + (1 / 3 - c) = -(2 / 3 : ℝ) by ring] at h
  exact sub_nonneg.mpr h



/-- Continuity of the subtracted kernel away from the integration endpoint. -/
theorem continuousOn_connectionKernel (c : ℝ) :
    ContinuousOn (connectionKernel c) (Ioi 0) := by
  apply ContinuousOn.sub
  · exact (continuousOn_id.rpow_const (fun _ ht => Or.inl ht.ne')).mul
      ((continuousOn_const.add continuousOn_id).rpow_const
        (fun t ht => Or.inl (ne_of_gt (add_pos zero_lt_one ht))))
  · exact continuousOn_id.rpow_const (fun _ ht => Or.inl ht.ne')

/-- The subtracted kernel is integrable at both endpoints in the source parameter range. -/
theorem integrableOn_connectionKernel (c : ℝ) (hc : 0 < c) (hc1 : c < 1 / 3) :
    IntegrableOn (connectionKernel c) (Ioi 0) volume  := by
  have connectionKernel_tail_bound (t : ℝ) (ht : 0 < t) :
      connectionKernel c t ≤ (1 / 3 - c) * t ^ (-(5 / 3 : ℝ)) := by
    have connectionKernel_factor :
        connectionKernel c t = t ^ (-(2 / 3 : ℝ)) *
        ((1 + t⁻¹) ^ (1 / 3 - c) - 1) := by
      have hbase : 1 + t = t * (1 + t⁻¹) := by field_simp; ring
      rw [connectionKernel, hbase, Real.mul_rpow ht.le (by positivity),
        ← mul_assoc, ← Real.rpow_add ht,
        show c - 1 + (1 / 3 - c) = -(2 / 3 : ℝ) by ring]
      ring
    rw [connectionKernel_factor]
    have hq := (sub_pos.mpr hc1).le
    have hq1 : 1 / 3 - c ≤ 1 := by linarith only [hc]
    have heq : t ^ (-(2 / 3 : ℝ)) * t⁻¹ = t ^ (-(5 / 3 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
      congr 1
      ring
    exact (mul_le_mul_of_nonneg_left (one_add_rpow_sub_one_le (1 / 3 - c) t⁻¹ hq hq1 (inv_pos.mpr ht).le) (Real.rpow_nonneg ht.le (-(2 / 3 : ℝ)))).trans_eq (by rw [mul_comm (1 / 3 - c), ← mul_assoc, heq]; ring)
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrableOn_union]
  constructor
  · have hdom := ((integrableOn_gammaKernel c 1 hc zero_lt_one).mono_set
      (show Ioc 0 1 ⊆ Ioi 0 from Ioc_subset_Ioi_self))
      |>.const_mul (2 ^ (1 / 3 - c) * Real.exp 1)
    apply hdom.mono'
    · exact ContinuousOn.aestronglyMeasurable
        ((continuousOn_connectionKernel c).mono Ioc_subset_Ioi_self) measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Real.norm_of_nonneg (connectionKernel_nonneg c t hc1.le ht.1)]
      have hp : (1 + t) ^ (1 / 3 - c) ≤ 2 ^ (1 / 3 - c) :=
        Real.rpow_le_rpow (by linarith only [ht.1]) (by linarith only [ht.2]) ((sub_pos.mpr hc1).le)
      have hexp : 1 ≤ Real.exp 1 * Real.exp (-t) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp_iff.mpr (by linarith only [ht.2])
      have hpow : 0 ≤ t ^ (c - 1) := Real.rpow_nonneg ht.1.le _
      have htwo : 0 ≤ (2 : ℝ) ^ (1 / 3 - c) := Real.rpow_nonneg (by norm_num) _
      calc
        connectionKernel c t ≤ t ^ (c - 1) * (1 + t) ^ (1 / 3 - c) :=
          sub_le_self _ (Real.rpow_nonneg ht.1.le _)
        _ ≤ t ^ (c - 1) * 2 ^ (1 / 3 - c) :=
          mul_le_mul_of_nonneg_left hp hpow
        _ = 2 ^ (1 / 3 - c) * t ^ (c - 1) := by ring
        _ ≤ (2 ^ (1 / 3 - c) * t ^ (c - 1)) *
            (Real.exp 1 * Real.exp (-t)) :=
          le_mul_of_one_le_right (mul_nonneg htwo hpow) hexp
        _ = (2 ^ (1 / 3 - c) * Real.exp 1) *
            (Real.exp (-(1 * t)) * t ^ (c - 1)) := by rw [one_mul]; ring
  · have hdom := (integrableOn_Ioi_rpow_of_lt
      (by norm_num : -(5 / 3 : ℝ) < -1) zero_lt_one).const_mul (1 / 3 - c)
    apply hdom.mono'
    · exact ContinuousOn.aestronglyMeasurable
        ((continuousOn_connectionKernel c).mono (Ioi_subset_Ioi zero_le_one)) measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 := zero_lt_one.trans ht
      rw [Real.norm_of_nonneg (connectionKernel_nonneg c t hc1.le ht0)]
      exact connectionKernel_tail_bound t ht0



/-- Fractional linear coordinate on the positive half-line. -/
def betaCoordinate (t : ℝ) : ℝ := t / (1 + t)

/-- Derivative of the fractional linear coordinate. -/
theorem hasDerivAt_betaCoordinate (t : ℝ) (ht : 0 < t) :
    HasDerivAt betaCoordinate ((1 + t) ^ (-2 : ℝ)) t := by
  convert (hasDerivAt_id t).div ((hasDerivAt_const t 1).add (hasDerivAt_id t)) (ne_of_gt (by linarith : 0 < 1 + t)) using 1
  · rfl
  · change (1 + t) ^ (-2 : ℝ) = (1 * (1 + t) - t * (0 + 1)) / (1 + t) ^ 2
    rw [show (-2 : ℝ) = -2 by norm_num,
      Real.rpow_neg (by linarith : 0 ≤ 1 + t), Real.rpow_two]
    field_simp
    ring

/-- The coordinate is injective on the positive half-line. -/
theorem betaCoordinate_injOn : InjOn betaCoordinate (Ioi 0) := by
  intro x hx y hy h
  change 0 < x at hx
  change 0 < y at hy
  dsimp [betaCoordinate] at h
  have h' := (div_eq_div_iff (by linarith : 1 + x ≠ 0)
    (by linarith : 1 + y ≠ 0)).mp h
  nlinarith

/-- The image of the positive half-line is the open unit interval. -/
theorem betaCoordinate_image : betaCoordinate '' Ioi 0 = Ioo 0 1 := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    change 0 < t at ht
    dsimp [betaCoordinate]
    constructor
    · exact div_pos ht (by linarith)
    · exact (div_lt_one (by linarith : 0 < 1 + t)).mpr (by linarith)
  · intro hu
    refine ⟨u / (1 - u), div_pos hu.1 (sub_pos.mpr hu.2), ?_⟩
    dsimp [betaCoordinate]
    field_simp [(ne_of_gt (sub_pos.mpr hu.2)), (ne_of_gt (add_pos zero_lt_one (div_pos hu.1 (sub_pos.mpr hu.2))))]
    ring

/-- Pullback of the Beta weight including the Jacobian. -/
theorem betaCoordinate_weight (a c t : ℝ) (ht : 0 < t) :
    |(1 + t) ^ (-2 : ℝ)| • betaWeight a c (betaCoordinate t) =
      t ^ (a - 1) * (1 + t) ^ (-a - c) := by
  have hp : 0 < 1 + t := by linarith
  have he : 1 - betaCoordinate t = (1 + t)⁻¹ := by
    dsimp [betaCoordinate]
    field_simp
    ring
  rw [smul_eq_mul, abs_of_pos (Real.rpow_pos_of_pos hp _), betaWeight, he,
    betaCoordinate, Real.div_rpow ht.le hp.le, Real.inv_rpow hp.le,
    div_eq_mul_inv, ← Real.rpow_neg hp.le]
  rw [← Real.rpow_neg hp.le]
  rw [mul_left_comm, mul_assoc, ← Real.rpow_add hp, ← Real.rpow_add hp]
  congr 2
  ring

/-- Integrability of the half-line Beta weight. -/
theorem integrableOn_betaHalf (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * (1 + t) ^ (-a - c)) (Ioi 0) := by
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun t ht => (hasDerivAt_betaCoordinate t ht).hasDerivWithinAt)
    betaCoordinate_injOn (betaWeight a c)).mp
    (by rw [betaCoordinate_image]; exact
      (intervalIntegrable_betaWeight a c ha hc).1.mono_set Ioo_subset_Ioc_self)
  exact h.congr_fun (fun t ht => betaCoordinate_weight a c t ht) measurableSet_Ioi

/-- Evaluation of the half-line Beta integral. -/
theorem integral_betaHalf (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    (∫ t in Ioi (0 : ℝ), t ^ (a - 1) * (1 + t) ^ (-a - c)) =
      Real.Gamma a * Real.Gamma c / Real.Gamma (a + c) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t ht => (hasDerivAt_betaCoordinate t ht).hasDerivWithinAt)
    betaCoordinate_injOn (betaWeight a c)
  rw [betaCoordinate_image] at h
  rw [(setIntegral_congr_fun (μ := volume) measurableSet_Ioi (fun t ht => betaCoordinate_weight a c t ht))] at h
  rw [← h, setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le
    (by norm_num : (0 : ℝ) ≤ 1), integral_betaWeight a c ha hc]



/-- Flux for the finite part at the singular endpoint. -/
def connectionFlux (c t : ℝ) : ℝ :=
  t ^ c * (1 + t) ^ (1 / 3 - c) - t ^ (1 / 3 : ℝ)






/-- Exact evaluation of the renormalized connection kernel. -/
theorem integral_connectionKernel_beta (c : ℝ) (hc : 0 < c) (hc1 : c < 1 / 3) :
    (∫ t in Ioi (0 : ℝ), connectionKernel c t) =
      (1 - 3 * c) *
        (Real.Gamma c * Real.Gamma (2 / 3) / Real.Gamma (c + 2 / 3))     := by
  have hasDerivAt_connectionFlux (t : ℝ) (ht : 0 < t) :
      HasDerivAt (connectionFlux c)
      ((1 / 3 : ℝ) * connectionKernel c t +
        (c - 1 / 3) * (t ^ (c - 1) * (1 + t) ^ (-c - 2 / 3))) t := by
    have hp := add_pos zero_lt_one ht
    convert (((hasDerivAt_id t).rpow_const (p := c) (Or.inl ht.ne')).mul (((hasDerivAt_const t 1).add (hasDerivAt_id t)).rpow_const (p := 1 / 3 - c) (Or.inl hp.ne'))).sub ((hasDerivAt_id t).rpow_const (p := (1 / 3 : ℝ)) (Or.inl ht.ne')) using 1
    · rfl
    · dsimp only [Pi.add_apply, id_eq]
      rw [connectionKernel]
      have he : (1 + t) ^ (1 / 3 - c) =
          (1 + t) * (1 + t) ^ (-c - 2 / 3) := by
        conv_rhs => lhs; rw [← Real.rpow_one (1 + t)]
        rw [← Real.rpow_add hp]
        congr 1
        ring
      have he2 : t ^ c = t * t ^ (c - 1) := by
        conv_rhs => lhs; rw [← Real.rpow_one t]
        rw [← Real.rpow_add ht]
        congr 1
        ring
      rw [he, he2, show 1 / 3 - c - 1 = -c - 2 / 3 by ring,
        show (1 / 3 : ℝ) - 1 = -(2 / 3 : ℝ) by ring]
      ring
  have tendsto_connectionFlux_atTop :
      Tendsto (connectionFlux c) atTop (𝓝 0) := by
    have connectionFlux_factor (t : ℝ) (ht : 0 < t) :
        connectionFlux c t = t ^ (1 / 3 : ℝ) *
        ((1 + t⁻¹) ^ (1 / 3 - c) - 1) := by
      have he : 1 + t = t * (1 + t⁻¹) := by field_simp; ring
      rw [connectionFlux, he, Real.mul_rpow ht.le (by positivity),
        ← mul_assoc, ← Real.rpow_add ht, show c + (1 / 3 - c) = 1 / 3 by ring]
      ring
    have hl : Tendsto (fun t : ℝ => (1 / 3 - c) * t ^ (-(2 / 3 : ℝ)))
        atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : 0 < (2 / 3 : ℝ))).const_mul
        (1 / 3 - c)
    apply squeeze_zero' _ _ hl
    · filter_upwards [Ioi_mem_atTop 0] with t ht
      rw [connectionFlux_factor t ht]
      apply mul_nonneg (Real.rpow_nonneg ht.le _)
      exact sub_nonneg.mpr (Real.one_le_rpow (by linarith [inv_pos.mpr ht] : 1 ≤ 1 + t⁻¹)
        (sub_pos.mpr hc1).le)
    · filter_upwards [Ioi_mem_atTop 0] with t ht
      rw [connectionFlux_factor t ht]
      have he : t ^ (1 / 3 : ℝ) * t⁻¹ = t ^ (-(2 / 3 : ℝ)) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
        congr 1
        ring
      exact (mul_le_mul_of_nonneg_left (one_add_rpow_sub_one_le (1 / 3 - c) t⁻¹ (sub_pos.mpr hc1).le (by linarith only [hc]) (inv_pos.mpr ht).le) (Real.rpow_nonneg ht.le (1 / 3 : ℝ))).trans_eq (by rw [mul_comm (1 / 3 - c), ← mul_assoc, he]; ring)
  have connectionFlux_zero :
      connectionFlux c 0 = 0 := by
    simp [connectionFlux, Real.zero_rpow hc.ne']
  have continuousAt_connectionFlux_zero :
      ContinuousAt (connectionFlux c) 0 := by
    exact ((Real.continuousAt_rpow_const 0 c (Or.inr hc.le)).mul
      ((continuousAt_const.add continuousAt_id).rpow_const
        (Or.inl (by norm_num)))).sub
      (Real.continuousAt_rpow_const 0 (1 / 3 : ℝ) (Or.inr (by norm_num)))
  have hk := integrableOn_connectionKernel c hc hc1
  have hb := integrableOn_betaHalf c (2 / 3) hc (by norm_num)
  have hf := integral_Ioi_of_hasDerivAt_of_tendsto
    (continuousAt_connectionFlux_zero).continuousWithinAt
    (fun t ht => hasDerivAt_connectionFlux t ht)
    ((hk.const_mul (1 / 3 : ℝ)).add (hb.const_mul (c - 1 / 3)))
    (tendsto_connectionFlux_atTop)
  rw [connectionFlux_zero, sub_self] at hf
  rw [(integral_add (hk.const_mul (1 / 3 : ℝ)) (hb.const_mul (c - 1 / 3))), integral_const_mul, integral_const_mul, integral_betaHalf c (2 / 3) hc
    (by norm_num)] at hf
  linarith only [hf]



/-- Wronskian with the Abel integrating factor for Kummer's equation. -/
def weightedWronskian (b : ℝ) (f g : ℝ → ℝ) (z : ℝ) : ℝ :=
  Real.exp (-z) * z ^ b * (deriv f z * g z - f z * deriv g z)


/-- Abel's weighted Wronskian is constant on the positive axis. -/
theorem weightedWronskian_eq (a b : ℝ) (f g : ℝ → ℝ)
    (hf : DifferentiableOn ℝ f (Ioi 0)) (hg : DifferentiableOn ℝ g (Ioi 0))
    (hf' : DifferentiableOn ℝ (deriv f) (Ioi 0))
    (hg' : DifferentiableOn ℝ (deriv g) (Ioi 0))
    (heqf : ∀ z > 0, z * deriv (deriv f) z + (b - z) * deriv f z - a * f z = 0)
    (heqg : ∀ z > 0, z * deriv (deriv g) z + (b - z) * deriv g z - a * g z = 0)
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    weightedWronskian b f g x = weightedWronskian b f g y  := by
  have hasDerivAt_weightedWronskian (z : ℝ) (hz : 0 < z) (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (hf' : DifferentiableAt ℝ (deriv f) z) (hg' : DifferentiableAt ℝ (deriv g) z) (heqf : z * deriv (deriv f) z + (b - z) * deriv f z - a * f z = 0) (heqg : z * deriv (deriv g) z + (b - z) * deriv g z - a * g z = 0) :
      HasDerivAt (weightedWronskian b f g) 0 z := by
    have hd := (((hasDerivAt_id z).neg.exp.mul
      ((hasDerivAt_id z).rpow_const (p := b) (Or.inl hz.ne'))).mul
      ((hf'.hasDerivAt.mul hg.hasDerivAt).sub (hf.hasDerivAt.mul hg'.hasDerivAt)))
    convert hd using 1
    · rfl
    · dsimp only [id_eq, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply]
      have hp : z ^ b = z * z ^ (b - 1) := by
        conv_rhs => lhs; rw [← Real.rpow_one z]
        rw [← Real.rpow_add hz]
        congr 1
        ring
      rw [hp]
      linear_combination -(Real.exp (-z) * z ^ (b - 1) * g z) * heqf +
        (Real.exp (-z) * z ^ (b - 1) * f z) * heqg
  have hd (z : ℝ) (hz : z ∈ Ioi 0) := hasDerivAt_weightedWronskian z hz
    (hf.differentiableAt (isOpen_Ioi.mem_nhds hz))
    (hg.differentiableAt (isOpen_Ioi.mem_nhds hz))
    (hf'.differentiableAt (isOpen_Ioi.mem_nhds hz))
    (hg'.differentiableAt (isOpen_Ioi.mem_nhds hz)) (heqf z hz) (heqg z hz)
  exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi 0).isPreconnected
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv) hx hy



/-- The regular M solution has zero scaled derivative at the singular endpoint. -/
theorem tendsto_M_scaled_deriv_zero (a : ℝ) (b : Pos) :
    Tendsto (fun z : ℝ => z * deriv (M a b) z) (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt (fun z : ℝ => z * deriv (M a b) z) 0 := by
    simp_rw [deriv_M]
    exact continuousAt_id.mul
      (continuousAt_const.mul (hasDerivAt_M _ _ 0).continuousAt)
  simpa using hc.tendsto.mono_left nhdsWithin_le_nhds




/-- Laplace transform of the finite-part connection kernel. -/
def connectionIntegral (c z : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-(z * t)) * connectionKernel c t

/-- Integrability of the transformed finite-part kernel for nonnegative Laplace parameter. -/
theorem integrableOn_connectionLaplace (c z : ℝ) (hc : 0 < c) (hc1 : c < 1 / 3)
    (hz : 0 ≤ z) :
    IntegrableOn (fun t => Real.exp (-(z * t)) * connectionKernel c t) (Ioi 0) := by
  apply (integrableOn_connectionKernel c hc hc1).mono'
  · exact ContinuousOn.aestronglyMeasurable
      (((continuous_const.mul continuous_id).neg.rexp.continuousOn).mul
        (continuousOn_connectionKernel c)) measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (connectionKernel_nonneg c t hc1.le ht)]
    exact mul_le_of_le_one_left (connectionKernel_nonneg c t hc1.le ht)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hz ht.le)))

/-- The finite-part transform tends to its exact integral at the lower endpoint. -/
theorem tendsto_connectionIntegral_zero (c : ℝ) (hc : 0 < c) (hc1 : c < 1 / 3) :
    Tendsto (connectionIntegral c) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (0 : ℝ), connectionKernel c t)) := by
  apply tendsto_integral_filter_of_dominated_convergence (connectionKernel c)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact (integrableOn_connectionLaplace c z hc hc1 hz.le).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (connectionKernel_nonneg c t hc1.le ht)]
    exact mul_le_of_le_one_left (connectionKernel_nonneg c t hc1.le ht)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hz.le ht.le)))
  · exact integrableOn_connectionKernel c hc hc1
  · filter_upwards with t
    have h : Tendsto (fun z : ℝ => Real.exp (-(z * t))) (𝓝[>] 0) (𝓝 1) := by
      have hc : ContinuousAt (fun z : ℝ => Real.exp (-(z * t))) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h.mul_const (connectionKernel c t)

/-- Exact decomposition of the positive integral into its singular term and finite part. -/
theorem UIr_connection_decomposition (c : Pos) (hc1 : c.1 < 1 / 3)
    (z : ℝ) (hz : 0 < z) :
    UIr c (4 / 3) z = (Real.Gamma c.1)⁻¹ *
      (z ^ (-(1 / 3 : ℝ)) * Real.Gamma (1 / 3) + connectionIntegral c.1 z) := by
  have he : ∀ t ∈ Ioi 0, laplaceKernel c (4 / 3) z t =
      Real.exp (-(z * t)) * t ^ ((1 / 3 : ℝ) - 1) +
        Real.exp (-(z * t)) * connectionKernel c.1 t := by
    intro t ht
    dsimp [laplaceKernel, laplaceKernelReal, connectionKernel]
    rw [show (4 / 3 : ℝ) - c.1 - 1 = 1 / 3 - c.1 by ring,
      show (1 / 3 : ℝ) - 1 = -(2 / 3 : ℝ) by ring]
    ring
  rw [UIr, setIntegral_congr_fun measurableSet_Ioi he, integral_add (integrableOn_gammaKernel (1 / 3 : ℝ) z (by norm_num) hz) (integrableOn_connectionLaplace c.1 z c.2 hc1 hz.le),
    integral_gammaKernel (1 / 3 : ℝ) z (by norm_num) hz]
  rfl


/-- Exact finite-part decomposition of the negative-parameter U solution. -/
theorem UNr_connection_decomposition (a : NegThird) (z : ℝ) (hz : 0 < z) :
    UNr a z = Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3) +
      z ^ (1 / 3 : ℝ) * (Real.Gamma (a.1 + 1 / 3))⁻¹ *
        connectionIntegral (a.1 + 1 / 3) z := by
  rw [UNr, UIr_connection_decomposition _ (by linarith [a.2.2]) z hz]
  have he : z ^ (1 / 3 : ℝ) * z ^ (-(1 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hz, add_neg_cancel, Real.rpow_zero]
  calc
    _ = (Real.Gamma (a.1 + 1 / 3))⁻¹ * Real.Gamma (1 / 3) *
        (z ^ (1 / 3 : ℝ) * z ^ (-(1 / 3 : ℝ))) +
        z ^ (1 / 3 : ℝ) * (Real.Gamma (a.1 + 1 / 3))⁻¹ *
          connectionIntegral (a.1 + 1 / 3) z := by ring
    _ = _ := by rw [he]; ring





/-- Renormalized first moment, with its small Laplace parameter included. -/
def connectionMoment (c z : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), (z * t) * Real.exp (-(z * t)) * connectionKernel c t

/-- The first moment multiplier is bounded by one for a nonnegative argument. -/
theorem mul_exp_neg_le_one (y : ℝ) : y * Real.exp (-y) ≤ 1 :=
  (Real.mul_exp_neg_le_exp_neg_one y).trans (Real.exp_le_one_iff.mpr (by norm_num))

/-- Integrability of the renormalized first moment. -/
theorem integrableOn_connectionMoment (c z : ℝ) (hc : 0 < c) (hc1 : c < 1 / 3)
    (hz : 0 ≤ z) :
    IntegrableOn (fun t => (z * t) * Real.exp (-(z * t)) * connectionKernel c t) (Ioi 0) := by
  apply (integrableOn_connectionKernel c hc hc1).mono'
  · exact ContinuousOn.aestronglyMeasurable
      ((by fun_prop : Continuous (fun t : ℝ => (z * t) * Real.exp (-(z * t)))).continuousOn.mul
        (continuousOn_connectionKernel c)) measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg hz ht.le) (Real.exp_pos _).le)
      (connectionKernel_nonneg c t hc1.le ht))]
    exact mul_le_of_le_one_left (connectionKernel_nonneg c t hc1.le ht)
      (mul_exp_neg_le_one (z * t))

/-- Dominated convergence for the renormalized first moment. -/
theorem tendsto_connectionMoment_zero (c : ℝ) (hc : 0 < c) (hc1 : c < 1 / 3) :
    Tendsto (connectionMoment c) (𝓝[>] 0) (𝓝 0) := by
  have hl : Tendsto (connectionMoment c) (𝓝[>] 0)
      (𝓝 (∫ _t in Ioi (0 : ℝ), 0)) := by
    apply tendsto_integral_filter_of_dominated_convergence (connectionKernel c)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact (integrableOn_connectionMoment c z hc hc1 hz.le).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with z hz
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_of_nonneg (mul_nonneg
        (mul_nonneg (mul_nonneg hz.le ht.le) (Real.exp_pos _).le)
        (connectionKernel_nonneg c t hc1.le ht))]
      exact mul_le_of_le_one_left (connectionKernel_nonneg c t hc1.le ht)
        (mul_exp_neg_le_one (z * t))
    · exact integrableOn_connectionKernel c hc hc1
    · filter_upwards with t
      have h : ContinuousAt
          (fun z : ℝ => (z * t) * Real.exp (-(z * t)) * connectionKernel c t) 0 := by
        fun_prop
      simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  simpa using hl






/-- The regular M increment vanishes after division by the fractional power. -/
theorem tendsto_M_fractional_increment_zero (a : ℝ) (b : Pos) :
    Tendsto (fun z : ℝ => (M a b z - 1) / z ^ (1 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
  have hs := (hasDerivAt_M a b 0).tendsto_slope_zero_right
  simp at hs
  have hp : Tendsto (fun z : ℝ => z ^ (2 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Real.continuousAt_rpow_const 0 (2 / 3 : ℝ)
      (Or.inr (by norm_num))).tendsto.mono_left nhdsWithin_le_nhds
  have hl := hs.mul hp
  simp at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have he : z ^ (2 / 3 : ℝ) * z ^ (1 / 3 : ℝ) = z := by
    rw [← Real.rpow_add hz, show (2 / 3 : ℝ) + 1 / 3 = 1 by ring, Real.rpow_one]
  apply (eq_div_iff (ne_of_gt (Real.rpow_pos_of_pos hz (1 / 3 : ℝ)))).mpr
  rw [mul_assoc, he]
  field_simp [ne_of_gt hz]

/-- Connection formula for the source's negative first-parameter range. -/
theorem UNr_connection (a : NegThird) (z : ℝ) (hz : 0 < z) :
    UNr a z =
      Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3) * M a.1 b23 z +
      Real.Gamma (-(1 / 3)) / Real.Gamma a.1 * Real.rpow z (1 / 3) *
        M (a.1 + 1 / 3) b43 z     := by
  have tendsto_UNr_scaled_deriv_zero :
      Tendsto (fun z : ℝ => z * deriv (UNr a) z) (𝓝[>] 0) (𝓝 0) := open MeasureTheory in by
    have UNr_scaled_deriv (z : ℝ) (hz : 0 < z) :
        z * deriv (UNr a) z = z ^ (1 / 3 : ℝ) * (Real.Gamma (a.1 + 1 / 3))⁻¹ *
        ((1 / 3 : ℝ) * connectionIntegral (a.1 + 1 / 3) z -
          connectionMoment (a.1 + 1 / 3) z) := by
      have laplaceIntegral_connectionMoment (c : ℝ) (hc : 0 < c) (hc1 : c < 1 / 3) :
          z * laplaceIntegral (c + 1) (7 / 3) z =
          z ^ (-(1 / 3 : ℝ)) * Real.Gamma (4 / 3) + connectionMoment c z := by
        have hl := integrableOn_laplaceKernelReal (c + 1) (7 / 3) z (by linarith) hz
        have hg := integrableOn_gammaKernel (4 / 3 : ℝ) z (by norm_num) hz
        have hm := integrableOn_connectionMoment c z hc hc1 hz.le
        have he : ∀ t ∈ Ioi 0, z * laplaceKernelReal (c + 1) (7 / 3) z t =
            z * (Real.exp (-(z * t)) * t ^ ((4 / 3 : ℝ) - 1)) +
              (z * t) * Real.exp (-(z * t)) * connectionKernel c t := by
          intro t ht
          dsimp [laplaceKernelReal, connectionKernel]
          have hp : t ^ c = t * t ^ (c - 1) := by
            conv_rhs => lhs; rw [← Real.rpow_one t]
            rw [← Real.rpow_add ht]
            congr 1
            ring
          have hq : t ^ ((4 / 3 : ℝ) - 1) = t * t ^ (-(2 / 3 : ℝ)) := by
            conv_rhs => lhs; rw [← Real.rpow_one t]
            rw [← Real.rpow_add ht]
            congr 1
            ring
          rw [show c + 1 - 1 = c by ring,
            show (7 / 3 : ℝ) - (c + 1) - 1 = 1 / 3 - c by ring, hp, hq]
          ring
        change z * (∫ t in Ioi 0, laplaceKernelReal (c + 1) (7 / 3) z t) = _
        rw [← integral_const_mul, setIntegral_congr_fun measurableSet_Ioi he,
          integral_add (hg.const_mul z) hm, integral_const_mul,
          integral_gammaKernel (4 / 3 : ℝ) z (by norm_num) hz]
        have hp : z * z ^ (-(4 / 3 : ℝ)) = z ^ (-(1 / 3 : ℝ)) := by
          conv_lhs => lhs; rw [← Real.rpow_one z]
          rw [← Real.rpow_add hz]
          congr 1
          ring
        rw [← mul_assoc, hp]
        rfl
      have hc : 0 < a.1 + 1 / 3 := by linarith [a.2.1]
      have hc1 : a.1 + 1 / 3 < 1 / 3 := by linarith [a.2.2]
      have hui := hasDerivAt_UIr ⟨a.1 + 1 / 3, hc⟩ (4 / 3) z hz
      have hd := hasDerivAt_power_mul (UIr ⟨a.1 + 1 / 3, hc⟩ (4 / 3))
        (1 / 3 : ℝ) z hz hui.differentiableAt.hasDerivAt
      rw [hui.deriv] at hd
      have he : deriv (UNr a) z =
          (1 / 3 : ℝ) * z ^ ((1 / 3 : ℝ) - 1) * UIr ⟨a.1 + 1 / 3, hc⟩ (4 / 3) z +
          z ^ (1 / 3 : ℝ) * (-(Real.Gamma (a.1 + 1 / 3))⁻¹ *
            laplaceIntegral (a.1 + 1 / 3 + 1) (4 / 3 + 1) z) := hd.deriv
      rw [he, UIr_connection_decomposition _ hc1 z hz]
      have hm := laplaceIntegral_connectionMoment _ hc hc1
      rw [show (4 / 3 : ℝ) + 1 = 7 / 3 by ring] 
      have hp : z * z ^ ((1 / 3 : ℝ) - 1) = z ^ (1 / 3 : ℝ) := by
        conv_lhs => lhs; rw [← Real.rpow_one z]
        rw [← Real.rpow_add hz]
        congr 1
        ring
      have hg := Real.Gamma_add_one (by norm_num : (1 / 3 : ℝ) ≠ 0)
      rw [show (1 / 3 : ℝ) + 1 = 4 / 3 by ring] at hg
      calc
        _ = z ^ (1 / 3 : ℝ) * (Real.Gamma (a.1 + 1 / 3))⁻¹ *
            ((1 / 3 : ℝ) * (z ^ (-(1 / 3 : ℝ)) * Real.Gamma (1 / 3) +
              connectionIntegral (a.1 + 1 / 3) z) -
              z * laplaceIntegral (a.1 + 1 / 3 + 1) (7 / 3) z) := by
                rw [← hp]
                ring
        _ = _ := by rw [hm, hg]; ring
    have hc : 0 < a.1 + 1 / 3 := by linarith [a.2.1]
    have hc1 : a.1 + 1 / 3 < 1 / 3 := by linarith [a.2.2]
    have hp : Tendsto (fun z : ℝ => z ^ (1 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
      simpa using (Real.continuousAt_rpow_const 0 (1 / 3 : ℝ)
        (Or.inr (by norm_num))).tendsto.mono_left nhdsWithin_le_nhds
    have hl := (hp.mul_const (Real.Gamma (a.1 + 1 / 3))⁻¹).mul
      (((tendsto_connectionIntegral_zero _ hc hc1).const_mul (1 / 3 : ℝ)).sub
        (tendsto_connectionMoment_zero _ hc hc1))
    simp only [zero_mul] at hl
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (UNr_scaled_deriv z hz).symm
  have tendsto_UNr_finitePart_zero :
      Tendsto (fun z : ℝ =>
      (UNr a z - Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3)) /
        z ^ (1 / 3 : ℝ)) (𝓝[>] 0)
      (𝓝 (Real.Gamma (-(1 / 3 : ℝ)) / Real.Gamma a.1)) := by
    have integral_connectionKernel_gamma :
        (∫ t in Ioi 0, connectionKernel (a.1 + 1 / 3) t) =
        Real.Gamma (a.1 + 1 / 3) * Real.Gamma (-(1 / 3 : ℝ)) / Real.Gamma a.1 := by
      have hc : 0 < a.1 + 1 / 3 := by linarith [a.2.1]
      have hc1 : a.1 + 1 / 3 < 1 / 3 := by linarith [a.2.2]
      rw [integral_connectionKernel_beta _ hc hc1]
      have ha := ne_of_lt a.2.2
      have hga : Real.Gamma a.1 ≠ 0 := by
        have hg := Real.Gamma_pos_of_pos (show 0 < a.1 + 1 by linarith [a.2.1])
        rw [Real.Gamma_add_one ha] at hg
        exact right_ne_zero_of_mul (ne_of_gt hg)
      have hg := Real.Gamma_add_one (by norm_num : -(1 / 3 : ℝ) ≠ 0)
      rw [show -(1 / 3 : ℝ) + 1 = 2 / 3 by ring] at hg
      rw [show a.1 + 1 / 3 + 2 / 3 = a.1 + 1 by ring, Real.Gamma_add_one ha, hg]
      field_simp
      ring
    have hc : 0 < a.1 + 1 / 3 := by linarith [a.2.1]
    have hi := (tendsto_connectionIntegral_zero (a.1 + 1 / 3) hc
      (by linarith [a.2.2])).const_mul (Real.Gamma (a.1 + 1 / 3))⁻¹
    rw [integral_connectionKernel_gamma] at hi
    have hg := ne_of_gt (Real.Gamma_pos_of_pos hc)
    have he : (Real.Gamma (a.1 + 1 / 3))⁻¹ *
        (Real.Gamma (a.1 + 1 / 3) * Real.Gamma (-(1 / 3 : ℝ)) / Real.Gamma a.1) =
          Real.Gamma (-(1 / 3 : ℝ)) / Real.Gamma a.1 := by
      rw [← mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hg, one_mul]
    rw [he] at hi
    apply hi.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [UNr_connection_decomposition a z hz]
    have hp := ne_of_gt (Real.rpow_pos_of_pos hz (1 / 3 : ℝ))
    field_simp [hp]
    ring
  have tendsto_UNr_zero :
      Tendsto (UNr a) (𝓝[>] 0)
      (𝓝 (Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3))) := by
    have hc : 0 < a.1 + 1 / 3 := by linarith [a.2.1]
    have hp : Tendsto (fun z : ℝ => z ^ (1 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
      simpa using (Real.continuousAt_rpow_const 0 (1 / 3 : ℝ)
        (Or.inr (by norm_num))).tendsto.mono_left nhdsWithin_le_nhds
    have hl := (tendsto_const_nhds (x :=
      Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3))).add
      ((hp.mul_const (Real.Gamma (a.1 + 1 / 3))⁻¹).mul (tendsto_connectionIntegral_zero (a.1 + 1 / 3) hc (by linarith [a.2.2])))
    simp only [zero_mul, add_zero] at hl
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (UNr_connection_decomposition a z hz).symm
  have exists_secondM_coefficient (f : ℝ → ℝ) (F : ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ioi 0)) (ho : ∀ z > 0, z * deriv (deriv f) z + (2 / 3 - z) * deriv f z - a.1 * f z = 0) (hlim : Tendsto f (𝓝[>] 0) (𝓝 F)) (hdlim : Tendsto (fun z : ℝ => z * deriv f z) (𝓝[>] 0) (𝓝 0)) :
      ∃ B : ℝ, ∀ z > 0, f z = F * M a.1 b23 z + B * secondM a.1 z := by
    have weightedWronskian_secondM_eq (a : ℝ) (f : ℝ → ℝ) (F : ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ioi 0)) (ho : ∀ z > 0, z * deriv (deriv f) z + (2 / 3 - z) * deriv f z - a * f z = 0) (hlim : Tendsto f (𝓝[>] 0) (𝓝 F)) (hdlim : Tendsto (fun z : ℝ => z * deriv f z) (𝓝[>] 0) (𝓝 0)) (z : ℝ) (hz : 0 < z) :
        weightedWronskian (2 / 3) f (secondM a) z = -(1 / 3 : ℝ) * F := by
      have tendsto_weightedWronskian_secondM_zero (hf : Tendsto f (𝓝[>] 0) (𝓝 F)) (hf' : Tendsto (fun z : ℝ => z * deriv f z) (𝓝[>] 0) (𝓝 0)) :
          Tendsto (weightedWronskian (2 / 3) f (secondM a)) (𝓝[>] 0)
          (𝓝 (-(1 / 3 : ℝ) * F)) := by
        have weightedWronskian_secondM (z : ℝ) (hz : 0 < z) :
            weightedWronskian (2 / 3) f (secondM a) z = Real.exp (-z) *
            (z * deriv f z * M (a + 1 / 3) b43 z -
              f z * ((1 / 3 : ℝ) * M (a + 1 / 3) b43 z +
                z * deriv (M (a + 1 / 3) b43) z)) := by
          have hd := hasDerivAt_power_mul (M (a + 1 / 3) b43) (1 / 3) z hz
            (hasDerivAt_M (a + 1 / 3) b43 z).differentiableAt.hasDerivAt
          have he : deriv (secondM a) z =
              (1 / 3 : ℝ) * z ^ ((1 / 3 : ℝ) - 1) * M (a + 1 / 3) b43 z +
                z ^ (1 / 3 : ℝ) * deriv (M (a + 1 / 3) b43) z := hd.deriv
          rw [weightedWronskian, he, secondM]
          have hp : z ^ (2 / 3 : ℝ) * z ^ (1 / 3 : ℝ) = z := by
            rw [← Real.rpow_add hz, show (2 / 3 : ℝ) + 1 / 3 = 1 by ring, Real.rpow_one]
          have hq : z ^ (2 / 3 : ℝ) * z ^ ((1 / 3 : ℝ) - 1) = 1 := by
            rw [← Real.rpow_add hz, show (2 / 3 : ℝ) + (1 / 3 - 1) = 0 by ring,
              Real.rpow_zero]
          calc
            _ = Real.exp (-z) *
              ((z ^ (2 / 3 : ℝ) * z ^ (1 / 3 : ℝ)) * deriv f z * M (a + 1 / 3) b43 z -
                f z * ((1 / 3 : ℝ) * (z ^ (2 / 3 : ℝ) * z ^ ((1 / 3 : ℝ) - 1)) *
                  M (a + 1 / 3) b43 z + (z ^ (2 / 3 : ℝ) * z ^ (1 / 3 : ℝ)) *
                  deriv (M (a + 1 / 3) b43) z)) := by ring
            _ = _ := by rw [hp, hq]; ring
        have hm : Tendsto (M (a + 1 / 3) b43) (𝓝[>] 0) (𝓝 1) := by
          simpa using (hasDerivAt_M (a + 1 / 3) b43 0).continuousAt.tendsto.mono_left
            nhdsWithin_le_nhds
        have hmd : ContinuousAt (deriv (M (a + 1 / 3) b43)) 0 := by
          have he : deriv (M (a + 1 / 3) b43) =
              fun z => ((a + 1 / 3) / b43.1) * M (a + 1 / 3 + 1) (next b43) z :=
            funext (deriv_M (a + 1 / 3) b43)
          rw [he]
          exact continuousAt_const.mul (hasDerivAt_M _ _ 0).continuousAt
        have hz : Tendsto (fun z : ℝ => z) (𝓝[>] 0) (𝓝 0) :=
          continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
        have he : Tendsto (fun z : ℝ => Real.exp (-z)) (𝓝[>] 0) (𝓝 1) := by
          have hc : ContinuousAt (fun z : ℝ => Real.exp (-z)) 0 := by fun_prop
          simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
        have hl := he.mul ((hf'.mul hm).sub
          (hf.mul ((hm.const_mul (1 / 3 : ℝ)).add
            (hz.mul (hmd.tendsto.mono_left nhdsWithin_le_nhds)))))
        simp only [zero_mul, mul_one, add_zero, one_mul, zero_sub] at hl
        have hl' : Tendsto (fun z => Real.exp (-z) *
            (z * deriv f z * M (a + 1 / 3) b43 z -
              f z * ((1 / 3 : ℝ) * M (a + 1 / 3) b43 z +
                z * deriv (M (a + 1 / 3) b43) z))) (𝓝[>] 0)
            (𝓝 (-(1 / 3 : ℝ) * F)) := by
          convert hl using 1
          congr 1
          ring
        apply hl'.congr'
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (weightedWronskian_secondM z hz).symm
      have hg := contDiffOn_secondM a
      have hc (x : ℝ) (hx : 0 < x) := weightedWronskian_eq a (2 / 3) f (secondM a)
        (hf.differentiableOn (by simp)) (hg.differentiableOn (by simp))
        ((hf.deriv_of_isOpen (m := 1) isOpen_Ioi (by simp)).differentiableOn (by simp))
        ((hg.deriv_of_isOpen (m := 1) isOpen_Ioi (by simp)).differentiableOn (by simp))
        ho (secondM_ode a) x z hx hz
      have hl := tendsto_weightedWronskian_secondM_zero hlim hdlim
      have hconst : Tendsto (weightedWronskian (2 / 3) f (secondM a)) (𝓝[>] 0)
          (𝓝 (weightedWronskian (2 / 3) f (secondM a) z)) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact (hc x hx).symm
      exact tendsto_nhds_unique hconst hl
    have hm : ContDiffOn ℝ (⊤ : ℕ∞) (M a.1 b23) (Ioi 0) :=
      ((analyticOnNhd_M a.1 b23).contDiffOn uniqueDiffOn_univ).mono (subset_univ _)
    have hm0 : Tendsto (M a.1 b23) (𝓝[>] 0) (𝓝 1) := by
      simpa using (hasDerivAt_M a.1 b23 0).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    have hwf (z : ℝ) (hz : 0 < z) :=
      weightedWronskian_secondM_eq a.1 f F hf ho hlim hdlim z hz
    have hwm (z : ℝ) (hz : 0 < z) := weightedWronskian_secondM_eq a.1 (M a.1 b23) 1 hm
      (by intro z _; simpa only [b23] using M_ode a.1 b23 z) hm0
        (tendsto_M_scaled_deriv_zero _ _) z hz
    let q : ℝ → ℝ := fun z => (f z - F * M a.1 b23 z) / secondM a.1 z
    have hd (z : ℝ) (hz : z ∈ Ioi (0 : ℝ)) : HasDerivAt q 0 z := by
      have hdf := (hf.differentiableOn (by simp)).differentiableAt
        (isOpen_Ioi.mem_nhds hz)
      have hdg := ((contDiffOn_secondM a.1).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioi.mem_nhds hz)
      have h := (hdf.hasDerivAt.sub (((hasDerivAt_M a.1 b23 z).differentiableAt).hasDerivAt.const_mul F)).div hdg.hasDerivAt
        (ne_of_gt (secondM_pos a z hz))
      convert h using 1
      · have hw : deriv f z * secondM a.1 z - f z * deriv (secondM a.1) z =
            F * (deriv (M a.1 b23) z * secondM a.1 z -
              M a.1 b23 z * deriv (secondM a.1) z) := by
          have he := hwf z hz
          have hm' := hwm z hz
          dsimp only [weightedWronskian] at he hm'
          have hp : Real.exp (-z) * z ^ (2 / 3 : ℝ) ≠ 0 := ne_of_gt
            (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hz _))
          apply (mul_left_cancel₀ hp)
          linear_combination he - F * hm'
        dsimp only [Pi.sub_apply]
        symm
        rw [div_eq_zero_iff]
        left
        linear_combination hw
    obtain ⟨B, hB⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero
      (convex_Ioi (0 : ℝ)).isPreconnected
      (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hd z hz).deriv)
    refine ⟨B, fun z hz => ?_⟩
    have h := hB z hz
    dsimp [q] at h
    have he := (div_eq_iff (ne_of_gt (secondM_pos a z hz))).mp h
    linarith only [he]
  let A : ℝ := Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3)
  obtain ⟨B, hB⟩ := exists_secondM_coefficient (UNr a) A (contDiffOn_UNr a)
    (UNr_ode a) (tendsto_UNr_zero) (tendsto_UNr_scaled_deriv_zero)
  have hm : Tendsto (M (a.1 + 1 / 3) b43) (𝓝[>] 0) (𝓝 1) := by
    simpa using (hasDerivAt_M (a.1 + 1 / 3) b43 0).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hl := ((tendsto_M_fractional_increment_zero a.1 b23).const_mul A).add
    (hm.const_mul B)
  simp at hl
  have he : Tendsto (fun w : ℝ => (UNr a w - A) / w ^ (1 / 3 : ℝ))
      (𝓝[>] 0) (𝓝 B) := by
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [hB w hw, secondM]
    have hp := ne_of_gt (Real.rpow_pos_of_pos hw (1 / 3 : ℝ))
    field_simp [hp]
    ring
  have hcoeff : B = Real.Gamma (-(1 / 3 : ℝ)) / Real.Gamma a.1 :=
    tendsto_nhds_unique he (tendsto_UNr_finitePart_zero)
  rw [hB z hz, hcoeff, secondM, Real.rpow_eq_pow]
  dsimp only [A]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set Filter
open scoped Topology ContDiff


/-- Join the positive-side function to the negative-side function at zero. -/
def scalarJoin (f g : ℝ → ℝ) (s : ℝ) : ℝ := if 0 < s then f s else g s

/-- The glued derivative at zero follows from the two one-sided derivatives. -/
theorem scalarJoin_hasDerivAt_zero (f g : ℝ → ℝ) (D : ℝ)
    (hf : HasDerivAt f D 0) (hg : HasDerivAt g D 0) (hfg : f 0 = g 0) :
    HasDerivAt (scalarJoin f g) D 0 := by
  have hr : HasDerivWithinAt (scalarJoin f g) D (Ici 0) 0 :=
    hf.hasDerivWithinAt.congr (by
      intro s hs
      rcases eq_or_lt_of_le hs with hs | hs
      · simp [← hs, scalarJoin, lt_self_iff_false, hfg]
      · simp [scalarJoin, hs])
      (by simp [scalarJoin, lt_self_iff_false, hfg])
  have hl : HasDerivWithinAt (scalarJoin f g) D (Iic 0) 0 :=
    hg.hasDerivWithinAt.congr (by
      intro s hs
      simp [scalarJoin, not_lt.mpr hs])
      (by simp [scalarJoin, lt_self_iff_false])
  have hu : Ici (0 : ℝ) ∪ Iic 0 = univ := by
    ext s
    simp only [mem_union, mem_Ici, mem_Iic, mem_univ, iff_true]
    exact le_total 0 s
  exact (hr.union hl).hasDerivAt (by rw [hu]; exact univ_mem)


/-- Matching first jets gives the global piecewise derivative identity. -/
theorem scalarJoin_deriv (f g : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfg : f 0 = g 0) (hdfg : deriv f 0 = deriv g 0) :
    deriv (scalarJoin f g) = scalarJoin (deriv f) (deriv g)  := by
  have scalarJoin_deriv_of_ne_zero (s : ℝ) (hs : s ≠ 0) :
      deriv (scalarJoin f g) s = scalarJoin (deriv f) (deriv g) s := by
    rcases lt_or_gt_of_ne hs with hs | hs
    · have he : scalarJoin f g =ᶠ[𝓝 s] g := by
        filter_upwards [Iio_mem_nhds hs] with t ht
        simp [scalarJoin, not_lt.mpr ht.le]
      rw [he.deriv_eq]
      simp [scalarJoin, not_lt.mpr hs.le]
    · have he : scalarJoin f g =ᶠ[𝓝 s] f := by
        filter_upwards [Ioi_mem_nhds hs] with t ht
        simp [scalarJoin, show 0 < t from ht]
      rw [he.deriv_eq]
      simp only [scalarJoin, hs, ↓reduceIte]
  funext s
  by_cases hs : s = 0
  · subst s
    have hd := scalarJoin_hasDerivAt_zero f g (deriv g 0)
      (by rw [← hdfg]; exact (hf 0).hasDerivAt) (hg 0).hasDerivAt hfg
    simpa only [scalarJoin, lt_self_iff_false, ↓reduceIte] using hd.deriv
  · exact scalarJoin_deriv_of_ne_zero s hs

/-- Matching first jets gives ordinary differentiability of the join. -/
theorem differentiable_scalarJoin (f g : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfg : f 0 = g 0) (hdfg : deriv f 0 = deriv g 0) :
    Differentiable ℝ (scalarJoin f g) := by
  intro s
  rcases lt_trichotomy s 0 with hs | hs | hs
  · apply (hg s).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hs] with t ht
    simp only [scalarJoin, not_lt.mpr ht.le, ↓reduceIte]
  · subst s
    exact (scalarJoin_hasDerivAt_zero f g (deriv g 0)
      (by rw [← hdfg]; exact (hf 0).hasDerivAt) (hg 0).hasDerivAt hfg).differentiableAt
  · apply (hf s).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hs] with t ht
    simp only [scalarJoin, show 0 < t from ht, ↓reduceIte]

/-- Matching values makes the join continuous. -/
theorem continuous_scalarJoin (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfg : f 0 = g 0) : Continuous (scalarJoin f g) := by
  classical
  have hb : ∀ s ∈ frontier (Ioi (0 : ℝ)), f s = g s := by
    intro s hs
    rw [frontier_Ioi] at hs
    simpa only [mem_singleton_iff.mp hs] using hfg
  have he : (Ioi (0 : ℝ)).piecewise f g = scalarJoin f g := by
    funext s
    simp only [Set.piecewise, mem_Ioi, scalarJoin]
  rw [← he]
  exact Continuous.piecewise hb hf hg

/-- Matching values and two derivatives suffices for global C² regularity. -/
theorem contDiff_two_scalarJoin (f g : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hfg : f 0 = g 0) (hdfg : deriv f 0 = deriv g 0)
    (hddfg : deriv (deriv f) 0 = deriv (deriv g) 0) :
    ContDiff ℝ 2 (scalarJoin f g) := by
  have hfd := hf.differentiable (by norm_num)
  have hgd := hg.differentiable (by norm_num)
  have he := scalarJoin_deriv f g hfd hgd hfg hdfg
  rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨differentiable_scalarJoin f g hfd hgd hfg hdfg, by norm_num, ?_⟩
  rw [he, contDiff_one_iff_deriv]
  have hfdd := hf.differentiable_deriv_two
  have hgdd := hg.differentiable_deriv_two
  refine ⟨differentiable_scalarJoin (deriv f) (deriv g) hfdd hgdd hdfg hddfg, ?_⟩
  rw [scalarJoin_deriv (deriv f) (deriv g) hfdd hgdd hdfg hddfg]
  have hfder : ContDiff ℝ 1 (deriv f) :=
    (show ContDiff ℝ (1 + 1) f from hf).deriv'
  have hgder : ContDiff ℝ 1 (deriv g) :=
    (show ContDiff ℝ (1 + 1) g from hg).deriv'
  exact continuous_scalarJoin _ _ (hfder.continuous_deriv (by norm_num))
    (hgder.continuous_deriv (by norm_num)) hddfg



/-- The entire local expression at diffusivity a, with the source linear normalization. -/
def scalarLocal (gamma : ScalarGamma) (Lam a s : ℝ) : ℝ :=
  gammaA gamma.1 * Kummer.M (-gamma.1) Kummer.b23 (scalarCubic a s) +
    gammaB gamma.1 * s / Real.rpow (9 * Lam) (1 / 3) *
      Kummer.M (1 / 3 - gamma.1) Kummer.b43 (scalarCubic a s)

/-- The literal local expression at diffusivity one is the negative piece. -/
theorem scalarLocal_one (gamma : ScalarGamma) (Lam : ℝ) :
    scalarLocal gamma Lam 1 = Fminus gamma Lam := by
  funext s
  simp only [scalarLocal, scalarCubic, mul_one, Fminus]

/-- Smoothness of the entire local expression. -/
theorem contDiff_scalarLocal (gamma : ScalarGamma) (Lam a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scalarLocal gamma Lam a) := by
  have hm (u : ℝ) (b : Kummer.Pos) : ContDiff ℝ (⊤ : ℕ∞) (Kummer.M u b) :=
    (Kummer.analyticOnNhd_M u b).contDiff
  exact (contDiff_const.mul ((hm _ _).comp (contDiff_scalarCubic a))).add
    (((contDiff_const.mul contDiff_id).div_const _).mul
      ((hm _ _).comp (contDiff_scalarCubic a)))

/-- The local expression has the source value at zero for every diffusivity. -/
@[simp] theorem scalarLocal_zero (gamma : ScalarGamma) (Lam a : ℝ) :
    scalarLocal gamma Lam a 0 = gammaA gamma.1 := by
  simp only [scalarLocal, scalarCubic, zero_pow (by decide : 3 ≠ 0), zero_div,
    Kummer.M_zero, mul_one, mul_zero, add_zero]

/-- Its first derivative at zero is independent of the branch diffusivity. -/
theorem scalarLocal_hasDerivAt_zero (gamma : ScalarGamma) (Lam a : ℝ) :
    HasDerivAt (scalarLocal gamma Lam a)
      (gammaB gamma.1 / Real.rpow (9 * Lam) (1 / 3)) 0 := by
  have hc : scalarCubic a 0 = 0 := by simp [scalarCubic]
  have hd (u : ℝ) (b : Kummer.Pos) : HasDerivAt
      (fun s => Kummer.M u b (scalarCubic a s)) 0 0 := by
    simpa only [Function.comp_def, hc, zero_pow (by decide : 2 ≠ 0), zero_div, mul_zero] using
      (Kummer.hasDerivAt_M u b (scalarCubic a 0)).comp 0 (hasDerivAt_scalarCubic a 0)
  have h := ((hd (-gamma.1) Kummer.b23).const_mul (gammaA gamma.1)).add
    ((((hasDerivAt_id (0 : ℝ)).const_mul (gammaB gamma.1)).div_const
      (Real.rpow (9 * Lam) (1 / 3))).mul (hd (1 / 3 - gamma.1) Kummer.b43))
  unfold scalarLocal
  simpa only [Pi.add_def, Pi.mul_def, id_eq, scalarCubic,
    zero_pow (by decide : 3 ≠ 0), zero_div, Kummer.M_zero, mul_zero, zero_mul,
    add_zero, zero_add, mul_one] using h


/-- Both local second derivatives vanish at zero by their actual differential equation. -/
theorem scalarLocal_deriv2_zero (gamma : ScalarGamma) (Lam a : ℝ) (ha : a ≠ 0) :
    deriv (deriv (scalarLocal gamma Lam a)) 0 = 0  := by
  have scalarLocal_ode (s : ℝ) :
      a * deriv (deriv (scalarLocal gamma Lam a)) s -
      s ^ 2 / 3 * deriv (scalarLocal gamma Lam a) s +
        gamma.1 * s * scalarLocal gamma Lam a s = 0 := by
    let f : ℝ → ℝ := fun t => Kummer.M (-gamma.1) Kummer.b23 (scalarCubic a t)
    let g : ℝ → ℝ := fun t => t *
      Kummer.M (1 / 3 - gamma.1) Kummer.b43 (scalarCubic a t)
    have hm (u : ℝ) (b : Kummer.Pos) : ContDiff ℝ 2 (Kummer.M u b) :=
      (Kummer.analyticOnNhd_M u b).contDiff
    have hc : ContDiff ℝ 2 (scalarCubic a) := (contDiff_scalarCubic a).of_le (by norm_num)
    have hf : ContDiff ℝ 2 f := (hm _ _).comp hc
    have hg : ContDiff ℝ 2 g := contDiff_id.mul ((hm _ _).comp hc)
    have hfo := scalarCubic_ode (Kummer.M (-gamma.1) Kummer.b23) gamma.1 a s ha
      (hm _ _).contDiffAt
      (by simpa only [Kummer.b23, neg_mul, sub_neg_eq_add] using
        Kummer.M_ode (-gamma.1) Kummer.b23 (scalarCubic a s))
    have hgo := scalarCubic_second_ode (Kummer.M (1 / 3 - gamma.1) Kummer.b43)
      gamma.1 a s ha (hm _ _)
      (by simpa only [Kummer.b43] using
        Kummer.M_ode (1 / 3 - gamma.1) Kummer.b43 (scalarCubic a s))
    have he : scalarLocal gamma Lam a = fun t => gammaA gamma.1 * f t +
        (gammaB gamma.1 / Real.rpow (9 * Lam) (1 / 3)) * g t := by
      funext t
      dsimp only [scalarLocal, f, g]
      ring
    rw [he]
    exact scalar_ode_linear_combination f g gamma.1 a (gammaA gamma.1)
      (gammaB gamma.1 / Real.rpow (9 * Lam) (1 / 3)) s hf hg hfo hgo
  have ho := scalarLocal_ode 0
  simp only [zero_pow (by decide : 2 ≠ 0), zero_div, zero_mul, mul_zero, sub_zero,
    add_zero] at ho
  exact (mul_eq_zero.mp ho).resolve_left ha


section Connection

variable (hconnection : ∀ a : Kummer.NegThird, ∀ z : ℝ, 0 < z →
  Kummer.UNr a z = Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3) *
    Kummer.M a.1 Kummer.b23 z +
  Real.Gamma (-(1 / 3)) / Real.Gamma a.1 * Real.rpow z (1 / 3) *
    Kummer.M (a.1 + 1 / 3) Kummer.b43 z)

include hconnection

/-- The source piecewise profile is the join of its two entire local expressions. -/
theorem F_eq_scalarJoin_of_connection (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    F gamma Lam = scalarJoin (scalarLocal gamma Lam Lam) (scalarLocal gamma Lam 1)  := by
  have Fplus_eq_scalarLocal_of_connection (hconnection : ∀ a : Kummer.NegThird, ∀ z : ℝ, 0 < z →
      Kummer.UNr a z = Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3) *
        Kummer.M a.1 Kummer.b23 z +
      Real.Gamma (-(1 / 3)) / Real.Gamma a.1 * Real.rpow z (1 / 3) *
        Kummer.M (a.1 + 1 / 3) Kummer.b43 z) (s : ℝ) (hs : 0 < s) :
      Fplus gamma Lam s = scalarLocal gamma Lam Lam s := by
    have hd : 0 < 9 * Lam := mul_pos (by norm_num) hLam
    have hp : (s ^ 3 / (9 * Lam)) ^ (1 / 3 : ℝ) = s / (9 * Lam) ^ (1 / 3 : ℝ) := by
      rw [Real.div_rpow (pow_nonneg hs.le _) hd.le,
        ← Real.rpow_natCast s 3, ← Real.rpow_mul hs.le]
      norm_num
    rw [Fplus, hconnection gamma.negative _ (div_pos (pow_pos hs _) hd)]
    dsimp only [ScalarGamma.negative, scalarLocal, scalarCubic, gammaA, gammaB]
    simp only [Real.rpow_eq_pow, hp]
    rw [show -gamma.1 + 1 / 3 = 1 / 3 - gamma.1 by ring]
    ring
  funext s
  unfold F scalarJoin
  by_cases hs : 0 < s
  · simp only [hs, ↓reduceIte]
    exact Fplus_eq_scalarLocal_of_connection hconnection s hs
  · simp only [hs, ↓reduceIte]
    rw [scalarLocal_one]
    by_cases hs0 : s < 0
    · simp only [hs0, ↓reduceIte]
    · have hz : s = 0 := le_antisymm (le_of_not_gt hs) (le_of_not_gt hs0)
      simp only [hz, lt_self_iff_false, ↓reduceIte, Fminus_zero]

/-- Exact C² matching at the scalar join, conditional only on the complete connection export. -/
theorem F_contDiff_two_of_connection (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    ContDiff ℝ 2 (F gamma Lam) := by
  rw [F_eq_scalarJoin_of_connection hconnection gamma Lam hLam]
  apply contDiff_two_scalarJoin
  · exact (contDiff_scalarLocal gamma Lam Lam).of_le (by norm_num)
  · exact (contDiff_scalarLocal gamma Lam 1).of_le (by norm_num)
  · rw [scalarLocal_zero, scalarLocal_zero]
  · rw [(scalarLocal_hasDerivAt_zero gamma Lam Lam).deriv,
      (scalarLocal_hasDerivAt_zero gamma Lam 1).deriv]
  · rw [scalarLocal_deriv2_zero gamma Lam Lam hLam.ne',
      scalarLocal_deriv2_zero gamma Lam 1 one_ne_zero]


/-- The glued profile solves the scalar equation, including its regular joining point. -/
theorem F_ode_of_connection (gamma : ScalarGamma) (Lam s : ℝ) (hLam : 0 < Lam) :
    (if 0 < s then Lam else 1) * deriv (deriv (F gamma Lam)) s -
      s ^ 2 / 3 * deriv (F gamma Lam) s + gamma.1 * s * F gamma Lam s = 0  := by
  have F_zero_jets_of_connection :
      F gamma Lam 0 = gammaA gamma.1 ∧
    deriv (F gamma Lam) 0 = gammaB gamma.1 / Real.rpow (9 * Lam) (1 / 3) ∧
    deriv (deriv (F gamma Lam)) 0 = 0 := by
    refine ⟨F_zero gamma Lam, ?_⟩
    have hf : Differentiable ℝ (scalarLocal gamma Lam Lam) :=
      (contDiff_scalarLocal gamma Lam Lam).differentiable (by norm_num)
    have hg : Differentiable ℝ (scalarLocal gamma Lam 1) :=
      (contDiff_scalarLocal gamma Lam 1).differentiable (by norm_num)
    have hfg : scalarLocal gamma Lam Lam 0 = scalarLocal gamma Lam 1 0 := by simp
    have hdfg : deriv (scalarLocal gamma Lam Lam) 0 =
        deriv (scalarLocal gamma Lam 1) 0 := by
      rw [(scalarLocal_hasDerivAt_zero gamma Lam Lam).deriv,
        (scalarLocal_hasDerivAt_zero gamma Lam 1).deriv]
    have hfdd := ((contDiff_scalarLocal gamma Lam Lam).of_le
      (by norm_num : (2 : ℕ∞ω) ≤ ∞)).differentiable_deriv_two
    have hgdd := ((contDiff_scalarLocal gamma Lam 1).of_le
      (by norm_num : (2 : ℕ∞ω) ≤ ∞)).differentiable_deriv_two
    have hddfg : deriv (deriv (scalarLocal gamma Lam Lam)) 0 =
        deriv (deriv (scalarLocal gamma Lam 1)) 0 := by
      rw [scalarLocal_deriv2_zero gamma Lam Lam hLam.ne',
        scalarLocal_deriv2_zero gamma Lam 1 one_ne_zero]
    rw [F_eq_scalarJoin_of_connection hconnection gamma Lam hLam,
      scalarJoin_deriv _ _ hf hg hfg hdfg]
    constructor
    · simp only [scalarJoin, lt_self_iff_false, ↓reduceIte]
      exact (scalarLocal_hasDerivAt_zero gamma Lam 1).deriv
    · rw [scalarJoin_deriv _ _ hfdd hgdd hdfg hddfg]
      simp only [scalarJoin, lt_self_iff_false, ↓reduceIte]
      exact scalarLocal_deriv2_zero gamma Lam 1 one_ne_zero
  rcases lt_trichotomy s 0 with hs | hs | hs
  · have he : F gamma Lam =ᶠ[𝓝 s] Fminus gamma Lam := by
      filter_upwards [Iio_mem_nhds hs] with t ht
      simp only [F, not_lt.mpr ht.le, show t < 0 from ht, ↓reduceIte]
    rw [ite_eq_right (not_lt.mpr hs.le), he.deriv.deriv_eq, he.deriv_eq,
      he.eq_of_nhds, one_mul]
    exact Fminus_ode gamma Lam s
  · subst s
    simp only [lt_self_iff_false, ↓reduceIte,
      (F_zero_jets_of_connection).2.2,
      zero_pow (by decide : 2 ≠ 0), zero_div, zero_mul, mul_zero, sub_zero, add_zero]
  · have he : F gamma Lam =ᶠ[𝓝 s] Fplus gamma Lam := by
      filter_upwards [Ioi_mem_nhds hs] with t ht
      simp only [F, show 0 < t from ht, ↓reduceIte]
    rw [ite_eq_left hs, he.deriv.deriv_eq, he.deriv_eq, he.eq_of_nhds]
    exact Fplus_ode gamma Lam s hLam hs

end Connection

/-- The two source branches match with global C² regularity. -/
theorem F_contDiff_two (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    ContDiff ℝ 2 (F gamma Lam) :=
  F_contDiff_two_of_connection Kummer.UNr_connection gamma Lam hLam

/-- The actual joined solution satisfies the piecewise scalar ODE everywhere. -/
theorem F_ode (gamma : ScalarGamma) (Lam s : ℝ) (hLam : 0 < Lam) :
    (if 0 < s then Lam else 1) * deriv (deriv (F gamma Lam)) s -
      s ^ 2 / 3 * deriv (F gamma Lam) s + gamma.1 * s * F gamma Lam s = 0 :=
  F_ode_of_connection Kummer.UNr_connection gamma Lam s hLam

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

