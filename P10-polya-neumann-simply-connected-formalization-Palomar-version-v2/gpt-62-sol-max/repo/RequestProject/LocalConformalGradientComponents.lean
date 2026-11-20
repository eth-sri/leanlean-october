module

public import RequestProject.LocalConformalMass
public import RequestProject.ConformalDiskCoordinates
public import RequestProject.ChainRule

/-!
# Weak Wirtinger derivatives in conformal coordinates

The Jacobian-weighted L² pullback preserves norm. The two weak Wirtinger
components transform by its composition with multiplication by the appropriate
unit phase of the conformal derivative. The pointwise chain rule on smooth
restrictions extends to all of H¹ by density.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped ComplexConjugate
open scoped Topology

local notation "D" => ball (0 : ℂ) 1

section

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
include coords

local notation "Ω" => F '' D
local notation "P" => coords.pullback
local notation "M" => localConformalMassPullback coords

/-- The Jacobian-weighted pullback on all of physical L². -/
def localConformalWeightedL2Pullback : L2 Ω →L[ℂ] L2 D :=
  (M).toLinearMap.extendOfNorm (h1Value Ω).toLinearMap

private theorem mass_norm_eq_value (u : NeumannH1 Ω) : ‖M u‖ = ‖h1Value Ω u‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (norm_sq_localConformalMassPullback coords u)

theorem localConformalWeightedL2Pullback_h1Value (u : NeumannH1 Ω) :
    localConformalWeightedL2Pullback coords (h1Value Ω u) = M u :=
  LinearMap.extendOfNorm_eq (f := (M).toLinearMap) (e := (h1Value Ω).toLinearMap)
    (h1Value_denseRange coords.lipschitz.1.1) ⟨1, fun w => by simp [mass_norm_eq_value coords w]⟩ u

private theorem norm_localConformalWeightedL2Pullback (v : L2 Ω) :
    ‖localConformalWeightedL2Pullback coords v‖ = ‖v‖ :=
  (h1Value_denseRange coords.lipschitz.1.1).induction_on v
    (isClosed_eq (localConformalWeightedL2Pullback coords).continuous.norm continuous_norm)
    fun u => by rw [localConformalWeightedL2Pullback_h1Value, mass_norm_eq_value]

theorem localConformalWeightedL2Pullback_injective :
    Function.Injective (localConformalWeightedL2Pullback coords) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← norm_localConformalWeightedL2Pullback coords, map_sub, huv, sub_self, norm_zero]

theorem localConformalWeightedL2Pullback_smooth_ae (f : smoothTraceTests) :
    (localConformalWeightedL2Pullback coords (h1Value Ω (smoothTraceH1 Ω f)) : ℂ → ℂ) =ᵐ[
      volume.restrict D] fun z => localConformalMassDensity F z * f (F z) := by
  rw [localConformalWeightedL2Pullback_h1Value]
  exact localConformalMassPullback_smooth_ae coords f

private theorem coordinate_fderiv_one_ne_zero {z : ℂ} (hz : z ∈ D) : fderiv ℝ F z 1 ≠ 0 := by
  simpa only [coords.real_fderiv_apply (ball_subset_closedBall hz), mul_one] using coords.deriv_ne_zero_closed (ball_subset_closedBall hz)

end

/-- The unit phase for each of the two Wirtinger components. The `true` component
uses the conjugate derivative. -/
def localConformalPhase (F : ℂ → ℂ) (s : Bool) (z : ℂ) : ℂ :=
  (if s then conj (fderiv ℝ F z 1) else fderiv ℝ F z 1) / (‖fderiv ℝ F z 1‖ : ℂ)

theorem phase_measurable (F : ℂ → ℂ) (s : Bool) : Measurable (localConformalPhase F s) := by
  have hd := measurable_fderiv_apply_const ℝ F (1 : ℂ)
  have hn := Complex.measurable_ofReal.comp hd.norm
  cases s
  · exact hd.div hn
  · exact (Complex.continuous_conj.measurable.comp hd).div hn

private theorem norm_phase (F : ℂ → ℂ) (s : Bool) (z : ℂ) :
    ‖localConformalPhase F s z‖ = ‖fderiv ℝ F z 1‖ / ‖fderiv ℝ F z 1‖ := by
  cases s <;> simp [localConformalPhase, norm_div]

theorem phase_bound (F : ℂ → ℂ) (s : Bool) (z : ℂ) : ‖localConformalPhase F s z‖ ≤ 1 := by
  rw [norm_phase]
  by_cases h : ‖fderiv ℝ F z 1‖ = 0 <;> simp [h]

def localConformalPhaseMultiplier (F : ℂ → ℂ) (s : Bool) : L2 D →L[ℂ] L2 D :=
  lpBoundedMultiplier (localConformalPhase F s) (phase_measurable F s).aestronglyMeasurable
    (.of_forall (phase_bound F s))

theorem localConformalPhaseMultiplier_ae (F : ℂ → ℂ) (s : Bool) (v : L2 D) :
    (localConformalPhaseMultiplier F s v : ℂ → ℂ) =ᵐ[volume.restrict D]
      fun z => localConformalPhase F s z * v z :=
  lpBoundedMultiplier_ae (localConformalPhase F s) (phase_measurable F s).aestronglyMeasurable
    (.of_forall (phase_bound F s)) v
private def wirtingerSign (s : Bool) : ℂ := if s then Complex.I else -Complex.I

private def h1Wirtinger (s : Bool) (U : Set ℂ) : NeumannH1 U →L[ℂ] L2 U :=
  h1Gradient U 0 + wirtingerSign s • h1Gradient U 1

private def wirtingerTest (s : Bool) (f : smoothTraceTests) : smoothTraceTests :=
  ⟨fun z => dirD (f : ℂ → ℂ) 1 z + wirtingerSign s * dirD (f : ℂ → ℂ) Complex.I z,
    (f.property.dirD 1).add ((f.property.dirD Complex.I).const_mul _)⟩

private theorem h1Wirtinger_smooth_ae (s : Bool) (U : Set ℂ) (f : smoothTraceTests) :
    (h1Wirtinger s U (smoothTraceH1 U f) : ℂ → ℂ) =ᵐ[volume.restrict U] wirtingerTest s f := by
  let g (i : Fin 2) := h1Gradient U i (smoothTraceH1 U f)
  have hg (i : Fin 2) : (g i : ℂ → ℂ) =ᵐ[volume.restrict U] dirD (f : ℂ → ℂ) (coordDir i) :=
    (smoothTraceTests_memLp_deriv U f i).coeFn_toLp
  change ((g 0 + wirtingerSign s • g 1 : L2 U) : ℂ → ℂ) =ᵐ[volume.restrict U] _
  filter_upwards [Lp.coeFn_add (g 0) (wirtingerSign s • g 1), Lp.coeFn_smul (wirtingerSign s) (g 1),
    hg 0, hg 1] with z ha hm h0 h1
  rw [ha, Pi.add_apply, hm, Pi.smul_apply, h0, h1]
  rfl

private theorem h1Wirtinger_smooth_eq_value (s : Bool) (U : Set ℂ) (f : smoothTraceTests) :
    h1Wirtinger s U (smoothTraceH1 U f) = h1Value U (smoothTraceH1 U (wirtingerTest s f)) := by
  apply Lp.ext
  exact (h1Wirtinger_smooth_ae s U f).trans (smoothTraceTests_memLp U (wirtingerTest s f)).coeFn_toLp.symm

private theorem wirtinger_factor (s : Bool) (A : ℂ →L[ℝ] ℂ) (c : ℂ) :
    A c + wirtingerSign s * A (c * Complex.I) =
      (if s then conj c else c) * (A 1 + wirtingerSign s * A Complex.I) := by
  rw [realCLM_apply_complex A c, realCLM_apply_complex A (c * Complex.I)]
  cases s <;> apply Complex.ext <;>
    simp [wirtingerSign, Complex.mul_re, Complex.mul_im] <;> ring


section

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
include coords

local notation "Ω" => F '' D
local notation "P" => coords.pullback

theorem localConformalPhase_mul_massDensity (s : Bool) {z : ℂ} (hz : z ∈ D) :
    localConformalPhase F s z * localConformalMassDensity F z =
      if s then conj (fderiv ℝ F z 1) else fderiv ℝ F z 1 :=
  div_mul_cancel₀ _ (by simpa using coordinate_fderiv_one_ne_zero coords hz)

theorem localConformalPhaseMultiplier_injective (s : Bool) :
    Function.Injective (localConformalPhaseMultiplier F s) := by
  intro u v h
  apply Lp.ext
  filter_upwards [localConformalPhaseMultiplier_ae F s u, localConformalPhaseMultiplier_ae F s v,
    ae_restrict_mem measurableSet_ball] with z hu hv hz
  have hn : ‖localConformalPhase F s z‖ = 1 := by
    rw [norm_phase, div_self (norm_ne_zero_iff.mpr (coordinate_fderiv_one_ne_zero coords hz))]
  apply mul_left_cancel₀ (norm_ne_zero_iff.mp (by rw [hn]; exact one_ne_zero))
  rw [← hu, ← hv, h]

private theorem wirtingerTest_pullback (s : Bool) (f : smoothTraceTests) {z : ℂ} (hz : z ∈ D) :
    wirtingerTest s (smoothDiskCompositionLin coords.one_lt_radius F coords.smooth f) z =
      (if s then conj (fderiv ℝ F z 1) else fderiv ℝ F z 1) * wirtingerTest s f (F z) := by
  change (fderiv ℝ _ z) 1 + wirtingerSign s * (fderiv ℝ _ z) Complex.I = _ *
    ((fderiv ℝ (f : ℂ → ℂ) (F z)) 1 + wirtingerSign s * (fderiv ℝ (f : ℂ → ℂ) (F z)) Complex.I)
  rw [fderiv_smoothDiskCompositionLin coords.one_lt_radius F coords.smooth f (ball_subset_closedBall hz)]
  simpa only [ContinuousLinearMap.comp_apply, coords.real_fderiv_apply (ball_subset_closedBall hz), mul_one] using
    wirtinger_factor s (fderiv ℝ (f : ℂ → ℂ) (F z)) (deriv F z)

/-- Both actual weak Wirtinger derivatives satisfy the conformal chain rule. -/
private theorem h1Wirtinger_pullback (s : Bool) (u : NeumannH1 Ω) :
    h1Wirtinger s D (P u) = localConformalPhaseMultiplier F s
      (localConformalWeightedL2Pullback coords (h1Wirtinger s Ω u)) := by
  let A := (h1Wirtinger s D).comp P
  let B := (localConformalPhaseMultiplier F s).comp ((localConformalWeightedL2Pullback coords).comp (h1Wirtinger s Ω))
  refine (denseRange_smoothTraceH1Lin coords.bounded coords.lipschitz).induction_on u
    (isClosed_eq A.continuous B.continuous) fun f => ?_
  change h1Wirtinger s D (P (smoothTraceH1 Ω f)) = localConformalPhaseMultiplier F s
    (localConformalWeightedL2Pullback coords (h1Wirtinger s Ω (smoothTraceH1 Ω f)))
  rw [localConformalH1Pullback_smooth coords.one_lt_radius F coords.smooth coords.bounded
    coords.lipschitz coords.holomorphic coords.injOn coords.lower,
    h1Wirtinger_smooth_eq_value s Ω]
  apply Lp.ext
  filter_upwards [h1Wirtinger_smooth_ae s D (smoothDiskCompositionLin coords.one_lt_radius F coords.smooth f),
    localConformalPhaseMultiplier_ae F s (localConformalWeightedL2Pullback coords
      (h1Value Ω (smoothTraceH1 Ω (wirtingerTest s f)))),
    localConformalWeightedL2Pullback_smooth_ae coords (wirtingerTest s f),
    ae_restrict_mem measurableSet_ball] with z ha hb hc hz
  rw [ha, hb, hc, ← mul_assoc, localConformalPhase_mul_massDensity coords s hz]
  exact wirtingerTest_pullback coords s f hz

theorem localConformalH1Pullback_antiholomorphic_iff (u : NeumannH1 Ω) :
    h1Gradient D 0 (P u) = Complex.I • h1Gradient D 1 (P u) ↔
      h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u := by
  have hs : h1Wirtinger false D (P u) = 0 ↔ h1Wirtinger false Ω u = 0 := by
    rw [h1Wirtinger_pullback coords, ← map_zero (localConformalPhaseMultiplier F false),
      (localConformalPhaseMultiplier_injective coords false).eq_iff,
      ← map_zero (localConformalWeightedL2Pullback coords),
      (localConformalWeightedL2Pullback_injective coords).eq_iff]
  simpa only [h1Wirtinger, wirtingerSign, Bool.false_eq_true, ite_false, add_apply,
    ContinuousLinearMap.smul_apply, neg_smul, ← sub_eq_add_neg, sub_eq_zero] using hs

/-- For antiholomorphic vectors the positive Wirtinger component is twice the x derivative. -/
theorem localConformalH1Pullback_gradient_antiholomorphic (u : NeumannH1 Ω)
    (hu : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u) :
    h1Gradient D 0 (P u) = localConformalPhaseMultiplier F true
      (localConformalWeightedL2Pullback coords (h1Gradient Ω 0 u)) := by
  have h2 {U : Set ℂ} {v : NeumannH1 U} (hv : h1Gradient U 0 v = Complex.I • h1Gradient U 1 v) :
      h1Wirtinger true U v = (2 : ℂ) • h1Gradient U 0 v := by
    change h1Gradient U 0 v + Complex.I • h1Gradient U 1 v = _
    rw [← hv, two_smul]
  have h := h1Wirtinger_pullback coords true u
  rw [h2 ((localConformalH1Pullback_antiholomorphic_iff coords u).mpr hu), h2 hu, map_smul, map_smul] at h
  exact smul_right_injective _ (two_ne_zero : (2 : ℂ) ≠ 0) h

end

end PolyaNeumann

end
