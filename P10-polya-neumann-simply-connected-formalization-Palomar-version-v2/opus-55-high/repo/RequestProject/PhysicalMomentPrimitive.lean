module

public import RequestProject.PhysicalMomentExterior
public import RequestProject.Driven
public import RequestProject.ArcLength
public import RequestProject.ExteriorConnected
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# A genuine C¹ density obtained from the physical moment identities

The actual interval primitive of `conj γ' * H` is C¹ when `γ` is C¹ and
`H` is continuous.  Its value at the boundary origin is zero.  The zeroth
physical moment makes the endpoint value zero; periodic input functions then
give an actual periodic primitive.  Integration by parts proves that this
primitive satisfies the same full complex physical antiholomorphic moments.

Thus the weighted Jordan Cauchy jump can be approached with a C¹ density
without assuming Hardy support, polynomial density, or elliptic regularity.
Differentiation of the actual Cauchy integral and the analytic identity
principle propagate its vanishing to the whole connected physical exterior.
This file does not assert the still-missing weighted jump theorem.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter
open scoped ComplexConjugate Topology

/-- The physical interval primitive, normalized at the supplied boundary origin. -/
def physicalMomentPrimitive (γ H : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..θ, conj (deriv γ s) * H s

variable (γ H : ℝ → ℂ) {Ω : Set ℂ}

@[simp] theorem physicalMomentPrimitive_zero (γ H : ℝ → ℂ) :
    physicalMomentPrimitive γ H 0 = 0 := by
  simp [physicalMomentPrimitive]

/-- The primitive has the actual physical differentiated density at every point. -/
theorem physicalMomentPrimitive_hasDerivAt (hγ : ContDiff ℝ 1 γ) (hH : Continuous H) (θ : ℝ) :
    HasDerivAt (physicalMomentPrimitive γ H) (conj (deriv γ θ) * H θ) θ :=
  (((Complex.continuous_conj.comp hγ.continuous_deriv_one).mul hH).integral_hasStrictDerivAt
    0 θ).hasDerivAt

theorem physicalMomentPrimitive_deriv (hγ : ContDiff ℝ 1 γ) (hH : Continuous H) (θ : ℝ) :
    deriv (physicalMomentPrimitive γ H) θ = conj (deriv γ θ) * H θ :=
  (physicalMomentPrimitive_hasDerivAt γ H hγ hH θ).deriv

/-- This is actual C¹ regularity of the density, not a Fourier regularity premise. -/
theorem contDiff_physicalMomentPrimitive (hγ : ContDiff ℝ 1 γ) (hH : Continuous H) :
    ContDiff ℝ 1 (physicalMomentPrimitive γ H) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun θ => (physicalMomentPrimitive_hasDerivAt γ H hγ hH θ).differentiableAt, ?_⟩
  have hd : deriv (physicalMomentPrimitive γ H) =
      fun θ => conj (deriv γ θ) * H θ := by
    funext θ
    exact physicalMomentPrimitive_deriv γ H hγ hH θ
  rw [hd]
  fun_prop

/-- The actual zero moment is precisely the zero endpoint value. -/
theorem physicalMomentPrimitive_endpoint (hmom0 : (∫ θ in 0..(2 * Real.pi), conj (deriv γ θ) * H θ) = 0) :
    physicalMomentPrimitive γ H (2 * Real.pi) = 0 := hmom0

/-- With periodic physical data, the zero moment makes the actual primitive periodic. -/
theorem physicalMomentPrimitive_periodic (hγ : ContDiff ℝ 1 γ) (hH : Continuous H)
    (hpγ : Function.Periodic γ (2 * Real.pi))
    (hpH : Function.Periodic H (2 * Real.pi))
    (hmom0 : (∫ θ in 0..(2 * Real.pi), conj (deriv γ θ) * H θ) = 0) :
    Function.Periodic (physicalMomentPrimitive γ H) (2 * Real.pi) := by
  let g  := fun θ => conj (deriv γ θ) * H θ
  have hg  :=
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul hH
  have hgp : Function.Periodic g (2 * Real.pi) := by
    intro θ
    simp [g, deriv_periodic hpγ θ, hpH θ]
  intro θ
  change (∫ s in 0..(θ + 2 * Real.pi), g s) = ∫ s in 0..θ, g s
  calc
    _ = (∫ s in 0..θ, g s) + ∫ s in θ..(θ + 2 * Real.pi), g s :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hg.intervalIntegrable 0 θ) (hg.intervalIntegrable θ _)).symm
    _ = (∫ s in 0..θ, g s) + ∫ s in 0..(2 * Real.pi), g s := by
      rw [← hgp.intervalIntegral_add_eq 0 θ, zero_add]
    _ = _ := by grind

/-- Integration by parts transfers every full complex physical moment to
the actual C¹ primitive.  The next input moment controls the output moment. -/
theorem physicalMomentPrimitive_moments (hγ : ContDiff ℝ 1 γ) (hH : Continuous H)
    (hmom : ∀ m : ℕ,
      (∫ θ in 0..(2 * Real.pi),
        (conj (deriv γ θ) * H θ) * (conj (γ θ) - conj (γ 0)) ^ m) = 0)
    (m : ℕ) :
    (∫ θ in 0..(2 * Real.pi),
      (conj (deriv γ θ) * physicalMomentPrimitive γ H θ) *
        (conj (γ θ) - conj (γ 0)) ^ m) = 0 := by
  let a  := fun θ => conj (deriv γ θ)
  let z  := fun θ => conj (γ θ) - conj (γ 0)
  let K := physicalMomentPrimitive γ H
  have ha  := Complex.continuous_conj.comp hγ.continuous_deriv_one
  have hz : Continuous z :=
    (Complex.continuous_conj.comp hγ.continuous).sub continuous_const
  have hK : ContDiff ℝ 1 K := contDiff_physicalMomentPrimitive γ H hγ hH
  have dz (θ : ℝ) : HasDerivAt z (a θ) θ := by
    simpa only [Complex.star_def] using
      ((hγ.differentiable_one θ).hasDerivAt.star).sub_const (conj (γ 0))
  have dv (θ : ℝ) : HasDerivAt (fun s => z s ^ (m + 1))
      ((m + 1 : ℕ) * z θ ^ m * a θ) θ := (dz θ).pow (m + 1)
  have hK0 : K 0 = 0 := physicalMomentPrimitive_zero γ H
  have hKL : K (2 * Real.pi) = 0 := by
    apply physicalMomentPrimitive_endpoint
    simpa only [pow_zero, mul_one] using hmom 0
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hK.continuous.continuousOn (hz.pow (m + 1)).continuousOn
    (fun θ _ => physicalMomentPrimitive_hasDerivAt γ H hγ hH θ)
    (fun θ _ => dv θ)
    ((ha.mul hH).intervalIntegrable 0 (2 * Real.pi))
    (((continuous_const.mul (hz.pow m)).mul ha).intervalIntegrable 0 (2 * Real.pi))
  have heq : (fun θ => K θ * ((m + 1 : ℕ) * z θ ^ m * a θ)) =
      (fun θ => (m + 1) * ((a θ * K θ) * z θ ^ m)) := by
    grind
  rw [heq, intervalIntegral.integral_const_mul, hKL, hK0, zero_mul, zero_mul,
    sub_self] at hi
  have hm' : (∫ θ in 0..(2 * Real.pi), conj (deriv γ θ) * H θ * (z ^ (m + 1)) θ) = 0 :=
    hmom (m + 1)
  rw [hm', sub_zero] at hi
  exact (mul_eq_zero.mp hi).resolve_left (by
    exact_mod_cast Nat.succ_ne_zero m)

/-- Conjugating the physical antiholomorphic transform gives this actual
holomorphic Cauchy transform, with all complex factors retained. -/
def physicalOrdinaryCauchy (γ H : ℝ → ℂ) (w : ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (deriv γ θ * conj (H θ)) / (w - γ θ)

theorem physicalOrdinaryCauchy_eq_conj (γ H : ℝ → ℂ) (w : ℂ) :
    physicalOrdinaryCauchy γ H w = conj (physicalExteriorCauchy γ H w) := by
  simp [physicalOrdinaryCauchy, physicalExteriorCauchy, ← intervalIntegral_conj] 

/-- Differentiation of the actual boundary integral away from the physical
curve.  Compact positive separation supplies an integrable uniform bound. -/
theorem physicalOrdinaryCauchy_hasDerivAt
    (hγ : ContDiff ℝ 1 γ) (hH : Continuous H) {w₀ : ℂ}
    (havoid : ∀ θ ∈ Icc 0 (2 * Real.pi), γ θ ≠ w₀) :
    HasDerivAt (physicalOrdinaryCauchy γ H)
      (∫ θ in 0..(2 * Real.pi),
        -(deriv γ θ * conj (H θ)) / (w₀ - γ θ) ^ 2) w₀ := by
  let g  := fun θ => deriv γ θ * conj (H θ)
  have hg  := hγ.continuous_deriv_one.mul (Complex.continuous_conj.comp hH)
  obtain ⟨d, hd, hdθ⟩ := exists_pos_le_norm_sub hγ.continuous havoid
  have hsep (θ : ℝ) (hθ : θ ∈ Icc 0 (2 * Real.pi))
      (w : ℂ) (hw : w ∈ Metric.ball w₀ (d / 2)) : d / 2 ≤ ‖w - γ θ‖ := by
    have hw' : ‖w - w₀‖ < d / 2 := by
      simp_all [dist_eq_norm]
    have hw'' : ‖w₀ - w‖ < d / 2 := by rwa [norm_sub_rev]
    have hlower : d ≤ ‖w₀ - γ θ‖ := by simp_all [norm_sub_rev]
    have htri : ‖w₀ - γ θ‖ ≤ ‖w₀ - w‖ + ‖w - γ θ‖ := by
      calc
        _ = ‖(w₀ - w) + (w - γ θ)‖ := by ring
        _ ≤ _ := norm_add_le _ _
    linarith
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
     hg.continuousOn
  have hFi : IntervalIntegrable (fun θ => g θ / (w₀ - γ θ)) volume 0 (2 * Real.pi) := by
    apply ContinuousOn.intervalIntegrable_of_Icc Real.two_pi_pos.le
    exact hg.continuousOn.div (continuous_const.sub hγ.continuous).continuousOn
      (fun θ hθ => sub_ne_zero.mpr (havoid θ hθ).symm)
  have hb : ∀ᵐ θ ∂volume.restrict (Ioc 0 (2 * Real.pi)),
      ∀ w ∈ Metric.ball w₀ (d / 2), ‖-g θ / (w - γ θ) ^ 2‖ ≤ M / (d / 2) ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    intro w hw
    have hθ' : θ ∈ Icc 0 (2 * Real.pi) := ⟨hθ.1.le, hθ.2⟩
    rw [norm_div, norm_neg, norm_pow]
    exact div_le_div₀ ((norm_nonneg (g 0)).trans (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)) (hM θ hθ') (sq_pos_of_pos (half_pos hd))
      ((sq_le_sq₀ (half_pos hd).le (norm_nonneg _)).mpr (hsep θ hθ' w hw))
  change HasDerivAt
    (fun w  => ∫ θ in 0..(2 * Real.pi), g θ / (w - γ θ))
    (∫ θ in 0..(2 * Real.pi), -g θ / (w₀ - γ θ) ^ 2) w₀
  simpa only [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    using (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    
    (F := fun w θ => g θ / (w - γ θ))
     
    (Metric.ball_mem_nhds w₀ (half_pos hd))
    (Eventually.of_forall fun w =>
      (hg.measurable.div (measurable_const.sub hγ.continuous.measurable)).aestronglyMeasurable)
    hFi.1
    (hg.measurable.neg.div
      ((measurable_const.sub hγ.continuous.measurable).pow_const 2)).aestronglyMeasurable
    hb intervalIntegrable_const.1 (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    intro w hw
    convert (hasDerivAt_const w (g θ)).div ((hasDerivAt_id w).sub_const (γ θ)) (norm_pos_iff.mp
      (lt_of_lt_of_le (half_pos hd) (hsep θ ⟨hθ.1.le, hθ.2⟩ w hw))) using 1 <;>
      first | rfl | simp)).2

/-- Actual moment vanishing propagates to every point of the connected
physical exterior.  Analyticity is proved from the boundary integral above;
only the already-proved exterior connectedness theorem is used. -/
theorem physicalExteriorCauchy_eq_zero_on_exterior_of_moments
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hfc : IsPreconnected (frontier Ω))
    (γ H : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (hH : Continuous H)
    (him : γ '' Icc 0 (2 * Real.pi) = frontier Ω)
    (hmom : ∀ m : ℕ,
      (∫ θ in 0..(2 * Real.pi),
        (conj (deriv γ θ) * H θ) * (conj (γ θ) - conj (γ 0)) ^ m) = 0) :
    ∀ w : ℂ, w ∉ closure Ω → physicalExteriorCauchy γ H w = 0 := by
  have hdiff : DifferentiableOn ℂ (physicalOrdinaryCauchy γ H) (closure Ω)ᶜ := by
    intro w hw
    apply (physicalOrdinaryCauchy_hasDerivAt γ H hγ hH ?_).differentiableAt.differentiableWithinAt
    intro θ hθ heq
    exact hw (heq ▸ frontier_subset_closure (by
      grind))
  obtain ⟨R, hR0, hfar⟩ :=
    exists_radius_physicalExteriorCauchy_eq_zero_of_moments γ H hγ hH hmom
  obtain ⟨B, hB⟩ := hb.closure.subset_ball (γ 0)
  let T  := max B R + 1
  let w₀  := γ 0 + T
  have hT : 0 < T := by
    positivity
  have hw₀norm : ‖w₀ - γ 0‖ = T := by
    rw [add_sub_cancel_left, Complex.norm_of_nonneg hT.le]
  have hw₀R : R < ‖w₀ - γ 0‖ := by
    grind
  intro w hw
  have hz := (hdiff.analyticOnNhd isClosed_closure.isOpen_compl).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isConnected_compl_closure_of_frontier hb hL hfc).isPreconnected (by
    intro hw₀
    have hnorm : ‖w₀ - γ 0‖ < B := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hB hw₀
    grind) (by
    filter_upwards [(isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).mem_nhds hw₀R] with w hw
    simp [physicalOrdinaryCauchy_eq_conj, hfar w hw]) hw
  simp_all [physicalOrdinaryCauchy_eq_conj]

/-- In particular the actual C¹ primitive's transform vanishes on the
whole physical exterior, with no weighted boundary-jump premise. -/
theorem physicalMomentPrimitive_exterior_eq_zero
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hfc : IsPreconnected (frontier Ω))
    (γ H : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (hH : Continuous H)
    (him : γ '' Icc 0 (2 * Real.pi) = frontier Ω)
    (hmom : ∀ m : ℕ,
      (∫ θ in 0..(2 * Real.pi),
        (conj (deriv γ θ) * H θ) * (conj (γ θ) - conj (γ 0)) ^ m) = 0) :
    ∀ w : ℂ, w ∉ closure Ω →
      physicalExteriorCauchy γ (physicalMomentPrimitive γ H) w = 0 :=
  physicalExteriorCauchy_eq_zero_on_exterior_of_moments hb hL hfc γ
    (physicalMomentPrimitive γ H) hγ (contDiff_physicalMomentPrimitive γ H hγ hH).continuous
    him (physicalMomentPrimitive_moments γ H hγ hH hmom)

end PolyaNeumann

end
