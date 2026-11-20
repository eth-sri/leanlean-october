module

public import RequestProject.HardyMoments
public import RequestProject.IntervalRegularity
public import RequestProject.DrivenGaugeOperator
public import RequestProject.Unitarity

/-! The positive gauge equations, their primitive, and the vanishing moments. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open AbsolutelyContinuousOnInterval
open scoped Topology ComplexConjugate

local notation "μB" => volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))

/-- Integration of the positive gauge equations against antiholomorphic powers.
The same argument works with a rough zeroth row. -/
theorem physicalDrivenMoment_eq_zero {γ : ℝ → ℂ} {E : ℝ} (hγ : ContDiff ℝ 1 γ)
    (hE : 0 < E) (u y : ℝ → Ell2)
    (hu : AbsolutelyContinuousOnInterval u 0 (2 * Real.pi))
    (hy : ∀ j, MemLp (physicalDrivenGauge γ E y j) 2 μB)
    (hpos : ∀ j θ, physicalDrivenGauge γ E u (j + 1) θ = physicalDrivenGauge γ E y (j + 1) θ)
    (hd : ∀ j, ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) → HasDerivAt (physicalDrivenGauge γ E u (j + 1))
      (physicalDrivenQ E ^ 2 * conj (deriv γ θ) * physicalDrivenGauge γ E y j θ) θ)
    (hend : ∀ j, physicalDrivenGauge γ E u (j + 1) 0 = 0 ∧
      physicalDrivenGauge γ E u (j + 1) (2 * Real.pi) = 0) (j k : ℕ) :
    physicalDrivenMoment γ E y j k = 0 := by
  have hrec (j k : ℕ) : physicalDrivenQ E ^ 2 * physicalDrivenMoment γ E y j k +
      (k : ℂ) * physicalDrivenMoment γ E y (j + 1) (k - 1) = 0 := by
    let z := fun θ => conj (physicalDrivenCentered γ θ)
    let f := physicalDrivenGauge γ E u (j + 1)
    let w := fun k θ => conj (deriv γ θ) * z θ ^ k
    let a := fun θ => w k θ * physicalDrivenGauge γ E y j θ
    let b := fun θ => w (k - 1) θ * physicalDrivenGauge γ E y (j + 1) θ
    let q := physicalDrivenQ E ^ 2
    have hz : ContDiff ℝ 1 z := Complex.conjCLE.contDiff.comp (hγ.sub contDiff_const)
    have hw (l : ℕ) :=
      (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul (hz.continuous.pow l)
    have ha := (hw k).continuousOn.mul_memLp_Ioc (hy j)
    have hb := (hw (k - 1)).continuousOn.mul_memLp_Ioc (hy (j + 1))
    have hi : IntegrableOn (fun θ => q * a θ + (k : ℂ) * b θ) (Icc 0 (2 * Real.pi)) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact ((ha.const_smul q).add (hb.const_smul (k : ℂ))).integrable (by norm_num)
    have hd' : ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
        HasDerivAt (fun s => f s * z s ^ k) (q * a θ + (k : ℂ) * b θ) θ := by
      filter_upwards [hd j] with θ hθ hmem
      have hdz : HasDerivAt z (conj (deriv γ θ)) θ := by
        simpa only [z, physicalDrivenCentered, Complex.star_def] using
          ((hγ.differentiable_one θ).hasDerivAt.sub_const (γ 0)).star
      convert (hθ hmem).mul (hdz.pow k) using 1
      simp only [hpos, a, b, w, q, Pi.pow_apply]
      ring
    have h := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
      ((physicalDrivenGauge_absolutelyContinuous hγ hu E (j + 1)).smul
        (hz.pow k).absolutelyContinuousOnInterval) hi hd' (2 * Real.pi) ⟨Real.two_pi_pos.le, le_rfl⟩
    change f (2 * Real.pi) * z (2 * Real.pi) ^ k =
      f 0 * z 0 ^ k + ∫ θ in 0..2 * Real.pi, (q * a θ + (k : ℂ) * b θ) at h
    have hf₀ : f 0 = 0 := (hend j).1
    have hf₁ : f (2 * Real.pi) = 0 := (hend j).2
    rw [hf₀, hf₁, zero_mul, zero_mul, zero_add] at h
    have hab (l : ℕ) (n : ℕ) : (∫ θ in (0 : ℝ)..(2 * Real.pi), w l θ * physicalDrivenGauge γ E y n θ) =
        physicalDrivenMoment γ E y n l := by
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [w]
      ring
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hab k j, hab (k - 1) (j + 1)] at h
    gcongr
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
      exact ((ha.const_smul q).integrable (by norm_num))
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
      exact ((hb.const_smul (k : ℂ)).integrable (by norm_num))
  induction k generalizing j with
  | zero =>
    simpa using (mul_eq_zero.mp (by grind)).resolve_left (physicalDrivenQ_sq_ne_zero hE)
  | succ k ih =>
    exact (mul_eq_zero.mp (by simpa [ih (j + 1)] using hrec j (k + 1))).resolve_left
      (physicalDrivenQ_sq_ne_zero hE)

section

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi))

local notation "y" => physicalDrivenVector W g
local notation "G" => physicalDrivenGauge γ E y


include hK hγ hW hg in
theorem physicalDrivenGauge_succ_ae_hasDerivAt_of_intervalIntegrable (j : ℕ) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) → HasDerivAt (G (j + 1))
      (physicalDrivenQ E ^ 2 * conj (deriv γ θ) * G j θ) θ := by
  filter_upwards [physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hg] with θ hθ hi
  have h := hasDerivAt_physicalDrivenGauge_succ (a := 0) (hγ.differentiable_one θ)
    (by simpa only [zero_smul, add_zero] using hθ hi) j
  simpa only [zero_smul, add_zero] using h

include hK hγ hW hg in
theorem physicalDrivenBackGauge_eq_integral {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    back (gaugeOp γ E θ (rowD (y θ))) = ∫ s in (0 : ℝ)..θ,
      (physicalDrivenQ E * conj (deriv γ s)) • gaugeOp γ E s (rowD (y s)) := by
  let X := fun t => gaugeOp γ E t (rowD (y t))
  have ha := gaugeVector_absolutelyContinuous hγ
    (physicalDrivenVector_absolutelyContinuous_of_intervalIntegrable hK hW g hg) E
  have hc :=
    (uIcc_of_le Real.two_pi_pos.le) ▸ (show ContinuousOn X (uIcc 0 (2 * Real.pi)) from ha.continuousOn)
  have hi : ContinuousOn (fun t => (physicalDrivenQ E * conj (deriv γ t)) • X t) (Icc 0 (2 * Real.pi)) :=
    (continuous_const.mul (Complex.continuous_conj.comp hγ.continuous_deriv_one)).continuousOn.smul hc
  have hd : ∀ᵐ t, t ∈ Ioo 0 (2 * Real.pi) → HasDerivAt (fun t => back (X t))
      ((physicalDrivenQ E * conj (deriv γ t)) • X t) t := by
    filter_upwards [physicalDrivenVector_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hg] with t ht hti
    have he := hasDerivAt_back_gauge (a := 0) (hγ.differentiable_one t)
      (by simpa only [zero_smul, add_zero] using ht hti)
    simpa only [X, zero_smul, add_zero] using he
  have he := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    (back.lipschitz.comp_absolutelyContinuousOnInterval ha) hi.integrableOn_Icc hd θ hθ
  simpa [X, physicalDrivenVector_zero W g] using he

include hK hγ hW hg in
theorem physicalDrivenMoment_eq_zero_of_intervalIntegrable (hE : 0 < E) (hO : observationAdj W g = 0)
    (j k : ℕ) : physicalDrivenMoment γ E y j k = 0 :=
  physicalDrivenMoment_eq_zero hγ hE y y
    (physicalDrivenVector_absolutelyContinuous_of_intervalIntegrable hK hW g hg)
    (fun l => (physicalDrivenGauge_continuousOn γ hγ.continuous E y
      (physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 g hg) l).memLp_Ioc)
    (fun _ _ => rfl) (physicalDrivenGauge_succ_ae_hasDerivAt_of_intervalIntegrable hK hγ hW g hg)
    (fun l => physicalDrivenGauge_actual_endpoints γ E W g hO (l + 1)) j k

end

theorem physicalDrivenPeriodicGauge_continuous_of_intervalIntegrable
    (γ : ℝ → ℂ) (hγ : Continuous γ) (E : ℝ)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * Real.pi)))
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (hO : observationAdj W g = 0) (j : ℕ) :
    Continuous (physicalDrivenPeriodicGauge γ E W g j) := by
  obtain ⟨h0, hL⟩ := physicalDrivenGauge_actual_endpoints γ E W g hO j
  exact (AddCircle.liftIco_zero_continuous (h0.trans hL.symm)
    (physicalDrivenGauge_continuousOn γ hγ E _
      (physicalDrivenVector_continuousOn_of_intervalIntegrable hW g hg) j)).comp (AddCircle.continuous_mk' _)

theorem localConformal_physicalDrivenGauge_nonpositive_of_intervalIntegrable
    {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
    {K : NNReal} (hK : LipschitzWith K (physicalCircleTrace F))
    {E : ℝ} (hE : 0 < E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport (physicalCircleTrace F) E W)
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume 0 (2 * Real.pi)) (hO : observationAdj W g = 0) (j : ℕ) :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos
      (physicalDrivenPeriodicGauge (physicalCircleTrace F) E W g j)) := by
  have hγ := contDiff_physicalCircleTrace_of_neighborhood coords.one_lt_radius F (coords.smooth.of_le (by simp))
  apply localConformal_physicalMoments_nonpositive coords _
    ((physicalDrivenPeriodicGauge_continuous_of_intervalIntegrable _ hγ.continuous E hW.1 g hg hO j).intervalIntegrable 0 (2 * Real.pi))
  intro m
  have hm := physicalDrivenMoment_eq_zero_of_intervalIntegrable hK hγ hW g hg hE hO j m
  calc
    _ = physicalDrivenMoment (physicalCircleTrace F) E (physicalDrivenVector W g) j m := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [uIcc_of_le Real.two_pi_pos.le] at hθ
      dsimp 
      rw [physicalDrivenPeriodicGauge_eqOn _ E W g hO j hθ]
      simp  [physicalDrivenCentered]
    _ = 0 := hm

/-- A genuine L² load on the physical parameter interval is integrable;
the interval has its actual finite Lebesgue measure. -/
theorem intervalIntegrable_boundary_of_memLp
    (g : ℝ → ℂ) (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * Real.pi)))) :
    IntervalIntegrable g volume 0 (2 * Real.pi) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le]
  exact MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hg

theorem intervalIntegrable_boundaryL2 (g : BoundaryL2) :
    IntervalIntegrable (g : ℝ → ℂ) volume 0 (2 * Real.pi) :=
  intervalIntegrable_boundary_of_memLp _ (Lp.memLp g)

end PolyaNeumann

end
