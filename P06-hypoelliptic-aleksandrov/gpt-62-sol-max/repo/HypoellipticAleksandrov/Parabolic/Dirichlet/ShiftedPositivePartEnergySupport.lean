module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandSteklov
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2Mass
public import Mathlib.Analysis.Calculus.Deriv.Slope
import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklovEnergy

/-!
# Shifted-positive-part energy support

This module proves the fixed-window energy identities for affine-threshold
shifted positive parts of forward and backward reverse-time Steklov averages.
The chain rule is derived from scalar convex support inequalities.  Its
differentiable pivot is the Gelfand curve corrected by the threshold times the
spatial-mass functional; no derivative of the nonlinear truncation is assumed.
-/

@[expose] public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Supporting-line inequality for the half square of the positive part. -/
theorem positivePart_mul_sub_le_half_sq_sub_sq (x z : ℝ) :
    max z 0 * (x - z) ≤ ((max x 0) ^ 2 - (max z 0) ^ 2) / 2 := by
  rcases le_total x 0 with hx | hx <;> rcases le_total z 0 with hz | hz <;>
    simp only [max_eq_left, max_eq_right, hx, hz] <;> nlinarith [sq_nonneg (x - z)]

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)

/-- Half the squared `L²` norm of an affine-threshold shifted positive part. -/
def shiftedPositivePartHalfEnergy
    (v : H10HilbertGraph hΩ) (k : ℝ≥0) : ℝ :=
  (1 / 2 : ℝ) * ‖shiftedPositivePartValue k (valueCLM hΩ v)‖ ^ 2

/-- Squared `L²` energy of the shifted positive part at an affine threshold. -/
def shiftedPositivePartEnergy
    (M N : ℝ≥0) (x : ℝ → H10HilbertGraph hΩ) (t : ℝ) : ℝ :=
  ‖valueCLM hΩ (h10ShiftedPositivePart hΩ (x t)
    (reverseTimeAffineThreshold M N t))‖ ^ 2

/-- Rate in the moving-threshold shifted-positive-part energy identity. -/
def shiftedPositivePartEnergyRate
    (hΩbounded : Bornology.IsBounded Ω) (M N : ℝ≥0)
    (x : ℝ → H10HilbertGraph hΩ) (y : ℝ → H10HilbertGraphDual hΩ)
    (t : ℝ) : ℝ :=
  y t (h10ShiftedPositivePart hΩ (x t) (reverseTimeAffineThreshold M N t)) -
    (N : ℝ) * spatialMassCLM hΩbounded
      (valueCLM hΩ (h10ShiftedPositivePart hΩ (x t)
        (reverseTimeAffineThreshold M N t)))

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (f : PDE.ScalarLp Ω (2 : ℝ≥0∞))

theorem scalarLp_norm_sq_eq_integral_sq :
    ‖f‖ ^ 2 = ∫ a, (f a) ^ 2 ∂(PDE.volumeOn Ω) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext a
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

theorem scalarLp_integrable_sq :
    Integrable (fun a => (f a) ^ 2) (PDE.volumeOn Ω) := (Lp.memLp f).integrable_sq

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩbounded : Bornology.IsBounded Ω) (f z : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (k l : ℝ≥0)
include hΩbounded

private theorem shiftedPositivePart_integral_support_lower :
    @inner ℝ (PDE.ScalarLp Ω (2 : ℝ≥0∞)) _
        (shiftedPositivePartValue l z) (f - z) -
      ((k : ℝ) - (l : ℝ)) *
        ∫ a, shiftedPositivePartValue l z a ∂PDE.volumeOn Ω ≤
      (1 / 2 : ℝ) * ‖shiftedPositivePartValue k f‖ ^ 2 -
        (1 / 2 : ℝ) * ‖shiftedPositivePartValue l z‖ ^ 2 := by
  letI : IsFiniteMeasure (PDE.volumeOn Ω) :=
    isFiniteMeasure_restrict.mpr hΩbounded.measure_lt_top.ne
  have hinner := L2.integrable_inner (𝕜 := ℝ) (shiftedPositivePartValue l z) (f - z)
  have hmass := ((MeasureTheory.Lp.memLp (shiftedPositivePartValue l z)).integrable
    (by norm_num)).const_mul ((k : ℝ) - (l : ℝ))
  have hf := (scalarLp_integrable_sq (shiftedPositivePartValue k f)).const_mul (1 / 2 : ℝ)
  have hz := (scalarLp_integrable_sq (shiftedPositivePartValue l z)).const_mul (1 / 2 : ℝ)
  rw [scalarLp_norm_sq_eq_integral_sq, scalarLp_norm_sq_eq_integral_sq, L2.inner_def,
    ← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_sub hinner hmass, ← integral_sub hf hz]
  apply integral_mono_ae (hinner.sub hmass) (hf.sub hz)
  filter_upwards [coeFn_shiftedPositivePartValue k f,
    coeFn_shiftedPositivePartValue l z, Lp.coeFn_sub f z] with a hxa hza hsub
  simp only [Pi.sub_apply, hxa, hza, hsub, RCLike.inner_apply, conj_trivial]
  nlinarith [positivePart_mul_sub_le_half_sq_sub_sq (f a - k) (z a - l)]

end

private theorem correctedDualPair_sub
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B Q : V) (k l : ℝ) :
    (A - k • Q) - (B - l • Q) = (A - B) - (k - l) • Q := by
  module

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
  (x z : H10HilbertGraph hΩ) (k l : ℝ≥0)

private theorem shiftedPositivePart_curve_support_lower :
    ((scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ x) -
        (k : ℝ) • (spatialMassCLM hΩbounded).comp (valueCLM hΩ)) -
      (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ z) -
        (l : ℝ) • (spatialMassCLM hΩbounded).comp (valueCLM hΩ)))
        (h10ShiftedPositivePart hΩ z l) ≤
      shiftedPositivePartHalfEnergy hΩ x k - shiftedPositivePartHalfEnergy hΩ z l := by
  rw [correctedDualPair_sub (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ x))
    (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ z))
    ((spatialMassCLM hΩbounded).comp (valueCLM hΩ)) (k : ℝ) (l : ℝ),
    ← (scalarLpToH10HilbertGraphDual hΩ).map_sub, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, scalarLpToH10HilbertGraphDual_apply,
    ContinuousLinearMap.comp_apply, valueCLM_h10ShiftedPositivePart, spatialMassCLM_apply]
  exact shiftedPositivePart_integral_support_lower hΩbounded (valueCLM hΩ x) (valueCLM hΩ z) k l

end

section
variable {V : Type*}

theorem slope_energy_error_le [NormedAddCommGroup V] [NormedSpace ℝ V]
    (E : ℝ → ℝ) (U : ℝ → V →L[ℝ] ℝ) (p : ℝ → V) {s t : ℝ}
    (hst : s ≠ t)
    (h0 : 0 ≤ (E s - E t) - (U s - U t) (p t))
    (h1 : (E s - E t) - (U s - U t) (p t) ≤
      (U s - U t) (p s - p t)) :
    |slope E t s - slope U t s (p t)| ≤
      |slope U t s (p s - p t)| := by
  have habs : |(E s - E t) - (U s - U t) (p t)| ≤
      |(U s - U t) (p s - p t)| := by
    rw [abs_of_nonneg h0]
    exact h1.trans (le_abs_self _)
  have hleft : slope E t s - slope U t s (p t) =
      (s - t)⁻¹ * ((E s - E t) - (U s - U t) (p t)) := by
    rw [slope_def_field, slope_def_module, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    field_simp [sub_ne_zero.mpr hst]
  have hright : slope U t s (p s - p t) =
      (s - t)⁻¹ * (U s - U t) (p s - p t) := by
    rw [slope_def_module, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hleft, hright, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left habs (abs_nonneg _)

theorem hasDerivAt_of_support_inequalities [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : ℝ → V →L[ℝ] ℝ) (p : ℝ → V) (E : ℝ → ℝ)
    (hp : Continuous p) (y : V →L[ℝ] ℝ) (t : ℝ)
    (hpivot : HasDerivAt U y t)
    (hlower : ∀ r s, (U r - U s) (p s) ≤ E r - E s) :
    HasDerivAt E (y (p t)) t := by
  have hSlopeU : Tendsto (slope U t) (𝓝[≠] t) (𝓝 y) := hpivot.tendsto_slope
  have hpDiff : Tendsto (fun s => p s - p t) (𝓝[≠] t) (𝓝 0) := by
    simpa only [sub_self] using
      ((hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => p t) (𝓝[≠] t) (𝓝 (p t))))
  have hSmall : Tendsto (fun s => slope U t s (p s - p t))
      (𝓝[≠] t) (𝓝 0) := by
    simpa only [map_zero] using tendsto_clm_apply hSlopeU hpDiff
  have hCompare : ∀ᶠ s in 𝓝[≠] t,
      |slope E t s - slope U t s (p t)| ≤
        |slope U t s (p s - p t)| := by
    filter_upwards [self_mem_nhdsWithin] with s hst
    have hLower := hlower s t
    have hUpper : E s - E t ≤ (U s - U t) (p s) := by
      simpa only [← ContinuousLinearMap.neg_apply, neg_sub] using neg_le_neg (hlower t s)
    apply slope_energy_error_le E U p hst (sub_nonneg.mpr hLower)
    have := sub_le_sub_right hUpper ((U s - U t) (p t))
    simpa only [ContinuousLinearMap.map_sub] using this
  have hErr : Tendsto (fun s => slope E t s - slope U t s (p t))
      (𝓝[≠] t) (𝓝 0) := by
    rw [Metric.tendsto_nhds] at hSmall ⊢
    intro ε hε
    filter_upwards [hCompare, hSmall ε hε] with s hcomp hsmall
    rw [Real.dist_eq]
    simpa only [sub_zero] using lt_of_le_of_lt hcomp
      (by simpa only [Real.dist_eq, sub_zero] using hsmall)
  have hEval : Tendsto (fun s => slope U t s (p t))
      (𝓝[≠] t) (𝓝 (y (p t))) :=
    tendsto_clm_apply hSlopeU tendsto_const_nhds
  apply hasDerivAt_iff_tendsto_slope.mpr
  simpa only [sub_add_cancel, zero_add] using hErr.add hEval

private theorem hasDerivAt_correctedPivot [NormedAddCommGroup V] [NormedSpace ℝ V]
    (M N : ℝ≥0) (U : ℝ → V) (y : V) (Q : V) (t : ℝ) (ht0 : 0 < t)
    (hx : HasDerivAt U y t) :
    HasDerivAt
      (fun s => U s - (reverseTimeAffineThreshold M N s : ℝ) • Q)
      (y - (N : ℝ) • Q) t := by
  have hk : HasDerivAt (fun s : ℝ => (M : ℝ) + s * (N : ℝ)) (N : ℝ) t := by
    convert (hasDerivAt_const t (M : ℝ)).add
      ((hasDerivAt_id t).mul_const (N : ℝ)) using 1
    all_goals first | (funext s; simp [Pi.add_def, mul_comm]) | ring
  have hkQ : HasDerivAt (fun s : ℝ => ((M : ℝ) + s * (N : ℝ)) • Q)
      ((N : ℝ) • Q) t := hk.smul_const Q
  have hraw := hx.sub hkQ
  apply hraw.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht0] with s hs
  rw [coe_reverseTimeAffineThreshold_of_nonneg M N hs.le]
  rfl

end

/-- The moving-threshold half-energy derivative obtained from convex support. -/
theorem hasDerivAt_shiftedPositivePartHalfEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (hΩbounded : Bornology.IsBounded Ω) (M N : ℝ≥0)
    (x : ℝ → H10HilbertGraph hΩ) (hx : Continuous x)
    (y : H10HilbertGraphDual hΩ) (t : ℝ) (ht0 : 0 < t)
    (hpivot : HasDerivAt
      (fun s => scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ (x s))) y t) :
    HasDerivAt
      (fun s => shiftedPositivePartHalfEnergy hΩ (x s)
        (reverseTimeAffineThreshold M N s))
      ((y - (N : ℝ) • (spatialMassCLM hΩbounded).comp (valueCLM hΩ))
        (h10ShiftedPositivePart hΩ (x t) (reverseTimeAffineThreshold M N t))) t := by
  let U : ℝ → H10HilbertGraphDual hΩ := fun s =>
    scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ (x s)) -
      (reverseTimeAffineThreshold M N s : ℝ) •
        (spatialMassCLM hΩbounded).comp (valueCLM hΩ)
  let p : ℝ → H10HilbertGraph hΩ := fun s =>
    h10ShiftedPositivePart hΩ (x s) (reverseTimeAffineThreshold M N s)
  let E : ℝ → ℝ := fun s =>
    shiftedPositivePartHalfEnergy hΩ (x s) (reverseTimeAffineThreshold M N s)
  have hk : Continuous (reverseTimeAffineThreshold M N) := by
    exact continuous_const.add (continuous_real_toNNReal.mul continuous_const)
  have hp : Continuous p := (continuous_h10ShiftedPositivePart hΩ).comp
    (hx.prodMk hk)
  exact hasDerivAt_of_support_inequalities U p E hp
    (y - (N : ℝ) • (spatialMassCLM hΩbounded).comp (valueCLM hΩ)) t
    (hasDerivAt_correctedPivot M N
      (fun s => scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ (x s))) y
      ((spatialMassCLM hΩbounded).comp (valueCLM hΩ)) t ht0 hpivot)
    (fun r s => shiftedPositivePart_curve_support_lower hΩ hΩbounded
      (x r) (x s) (reverseTimeAffineThreshold M N r)
      (reverseTimeAffineThreshold M N s))

end HypoellipticAleksandrov.Parabolic.Dirichlet
