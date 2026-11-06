module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandSteklov
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2Mass
public import Mathlib.Analysis.Calculus.Deriv.Slope

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

private theorem shiftedPositivePart_mul_sub_le_half_sq_sub_sq
    (x z k l : ℝ) :
    max (z - l) 0 * ((x - k) - (z - l)) ≤
      ((max (x - k) 0) ^ 2 - (max (z - l) 0) ^ 2) / 2 := by
  rcases le_total (x - k) 0 with hx | hx <;>
    rcases le_total (z - l) 0 with hz | hz <;>
    simp only [max_eq_left, max_eq_right, hx, hz] <;>
    nlinarith [sq_nonneg ((x - k) - (z - l))]

private theorem half_sq_sub_sq_le_shiftedPositivePart_mul_sub
    (x z k l : ℝ) :
    ((max (x - k) 0) ^ 2 - (max (z - l) 0) ^ 2) / 2 ≤
      max (x - k) 0 * ((x - k) - (z - l)) := by
  rcases le_total (x - k) 0 with hx | hx <;>
    rcases le_total (z - l) 0 with hz | hz <;>
    simp only [max_eq_left, max_eq_right, hx, hz] <;>
    nlinarith [sq_nonneg ((x - k) - (z - l))]

variable {d : ℕ} {Ω : Set (PDE.Vec d)} (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (x z : H10HilbertGraph hΩ) (k l : ℝ≥0)

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

theorem scalarLp_norm_sq_eq_integral_sq
     :
    ‖f‖ ^ 2 = ∫ a, (f a) ^ 2 ∂(PDE.volumeOn Ω) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

theorem scalarLp_integrable_sq
     :
    Integrable (fun a => (f a) ^ 2) (PDE.volumeOn Ω) := (Lp.memLp f).integrable_sq

private theorem correctedDual_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A Q : V →L[ℝ] ℝ) (c : ℝ) (v : V) :
    (A - c • Q) v = A v - c * Q v := by
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

private theorem spatialMassComp_shiftedPositivePart_apply
     (x : H10HilbertGraph hΩ) (m : ℝ≥0) :
    ((spatialMassCLM hΩbounded).comp (valueCLM hΩ))
        (h10ShiftedPositivePart hΩ x m) =
      spatialMassCLM hΩbounded (shiftedPositivePartValue m (valueCLM hΩ x)) := by
  rw [ContinuousLinearMap.comp_apply, valueCLM_h10ShiftedPositivePart]

private theorem scalarLpDual_shiftedPositivePart_apply
    
    (p x z : H10HilbertGraph hΩ) (m : ℝ≥0) :
    scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ x - valueCLM hΩ z)
        (h10ShiftedPositivePart hΩ p m) =
      @inner ℝ (PDE.ScalarLp Ω (2 : ℝ≥0∞)) _
        (shiftedPositivePartValue m (valueCLM hΩ p))
        (valueCLM hΩ x - valueCLM hΩ z) := by
  rw [scalarLpToH10HilbertGraphDual_apply,
    valueCLM_h10ShiftedPositivePart]

private theorem shiftedPositivePart_integral_support_lower
    
    (hΩbounded : Bornology.IsBounded Ω)
    (f z : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (k l : ℝ≥0) :
    @inner ℝ (PDE.ScalarLp Ω (2 : ℝ≥0∞)) _
        (shiftedPositivePartValue l z) (f - z) -
      ((k : ℝ) - (l : ℝ)) *
        ∫ a, shiftedPositivePartValue l z a ∂PDE.volumeOn Ω ≤
      (1 / 2 : ℝ) * ‖shiftedPositivePartValue k f‖ ^ 2 -
        (1 / 2 : ℝ) * ‖shiftedPositivePartValue l z‖ ^ 2 := by
  letI : IsFiniteMeasure (PDE.volumeOn Ω) :=
    isFiniteMeasure_restrict.mpr hΩbounded.measure_lt_top.ne
  rw [scalarLp_norm_sq_eq_integral_sq, scalarLp_norm_sq_eq_integral_sq,
    L2.inner_def]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_sub
      (L2.integrable_inner _ _)
      (((MeasureTheory.Lp.memLp (shiftedPositivePartValue l z)).integrable
        (by norm_num)).const_mul _),
    ← integral_sub
      ((scalarLp_integrable_sq _).const_mul _)
      ((scalarLp_integrable_sq _).const_mul _)]
  apply integral_mono_ae
    (L2.integrable_inner _ _ |>.sub
      ((MeasureTheory.Lp.memLp _).integrable
        (by norm_num) |>.const_mul _))
    (((scalarLp_integrable_sq _).const_mul _).sub
      ((scalarLp_integrable_sq _).const_mul _))
  filter_upwards [coeFn_shiftedPositivePartValue k f,
    coeFn_shiftedPositivePartValue l z, Lp.coeFn_sub f z] with a hxa hza hsub
  simp only [Pi.sub_apply, hxa, hza, hsub, RCLike.inner_apply, conj_trivial]
  nlinarith [shiftedPositivePart_mul_sub_le_half_sq_sub_sq
    (f a) (z a) k l]

private theorem shiftedPositivePart_integral_support_upper
    
    (hΩbounded : Bornology.IsBounded Ω)
    (f z : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (k l : ℝ≥0) :
    (1 / 2 : ℝ) * ‖shiftedPositivePartValue k f‖ ^ 2 -
        (1 / 2 : ℝ) * ‖shiftedPositivePartValue l z‖ ^ 2 ≤
    @inner ℝ (PDE.ScalarLp Ω (2 : ℝ≥0∞)) _
        (shiftedPositivePartValue k f) (f - z) -
      ((k : ℝ) - (l : ℝ)) *
        ∫ a, shiftedPositivePartValue k f a ∂PDE.volumeOn Ω := by
  letI : IsFiniteMeasure (PDE.volumeOn Ω) :=
    isFiniteMeasure_restrict.mpr hΩbounded.measure_lt_top.ne
  rw [scalarLp_norm_sq_eq_integral_sq, scalarLp_norm_sq_eq_integral_sq,
    L2.inner_def]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_sub
      ((scalarLp_integrable_sq _).const_mul _)
      ((scalarLp_integrable_sq _).const_mul _),
    ← integral_sub
      (L2.integrable_inner _ _)
      (((MeasureTheory.Lp.memLp (shiftedPositivePartValue k f)).integrable
        (by norm_num)).const_mul _)]
  apply integral_mono_ae
    (((scalarLp_integrable_sq _).const_mul _).sub
      ((scalarLp_integrable_sq _).const_mul _))
    (L2.integrable_inner _ _ |>.sub
      ((MeasureTheory.Lp.memLp _).integrable
        (by norm_num) |>.const_mul _))
  filter_upwards [coeFn_shiftedPositivePartValue k f,
    coeFn_shiftedPositivePartValue l z, Lp.coeFn_sub f z] with a hxa hza hsub
  simp only [Pi.sub_apply, hxa, hza, hsub, RCLike.inner_apply, conj_trivial]
  nlinarith [half_sq_sub_sq_le_shiftedPositivePart_mul_sub
    (f a) (z a) k l]

private theorem shiftedPositivePart_support_lower
     :
    (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ x - valueCLM hΩ z) -
      ((k : ℝ) - (l : ℝ)) • (spatialMassCLM hΩbounded).comp (valueCLM hΩ))
        (h10ShiftedPositivePart hΩ z l) ≤
      shiftedPositivePartHalfEnergy hΩ x k -
        shiftedPositivePartHalfEnergy hΩ z l := by
  have hmass := spatialMassCLM_apply hΩbounded
    (shiftedPositivePartValue l (valueCLM hΩ z))
  calc
    _ = scalarLpToH10HilbertGraphDual hΩ
          _ _ -
        (k - l) *
          ((spatialMassCLM hΩbounded).comp _)
            _ :=
      correctedDual_apply _ _ _ _
    _ = scalarLpToH10HilbertGraphDual hΩ
          _ _ -
        (k - l) * spatialMassCLM hΩbounded
          _ :=
      congrArg (fun q : ℝ =>
        scalarLpToH10HilbertGraphDual hΩ
            _ _ -
          (k - l) * q)
        (spatialMassComp_shiftedPositivePart_apply hΩ hΩbounded z l)
    _ = @inner ℝ _ _
          _
          _ -
        (k - l) * spatialMassCLM hΩbounded
          _ :=
      congrArg (fun q : ℝ => q - (k - l) * spatialMassCLM hΩbounded
        _)
        (scalarLpDual_shiftedPositivePart_apply hΩ z x z l)
    _ = @inner ℝ _ _
          _
          _ -
        (k - l) *
          ∫ a, shiftedPositivePartValue l _ a ∂PDE.volumeOn Ω :=
      congrArg (fun m : ℝ =>
        @inner ℝ _ _
            _
            _ -
          (k - l) * m) hmass
    _ ≤ _ := shiftedPositivePart_integral_support_lower hΩbounded
      _ _ k l

private theorem shiftedPositivePart_support_upper
     :
    shiftedPositivePartHalfEnergy hΩ x k -
        shiftedPositivePartHalfEnergy hΩ z l ≤
    (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ x - valueCLM hΩ z) -
      ((k : ℝ) - (l : ℝ)) • (spatialMassCLM hΩbounded).comp (valueCLM hΩ))
        (h10ShiftedPositivePart hΩ x k) := by
  have hmass := spatialMassCLM_apply hΩbounded
    (shiftedPositivePartValue k (valueCLM hΩ x))
  calc
    _ ≤ @inner ℝ _ _
          _
          _ -
        (k - l) *
          ∫ a, shiftedPositivePartValue k _ a ∂PDE.volumeOn Ω :=
      shiftedPositivePart_integral_support_upper hΩbounded
        _ _ k l
    _ = @inner ℝ _ _
          _
          _ -
        (k - l) * spatialMassCLM hΩbounded
          _ :=
      congrArg (fun m : ℝ =>
        @inner ℝ _ _
            _
            _ -
          (k - l) * m) hmass.symm
    _ = scalarLpToH10HilbertGraphDual hΩ
          _ _ -
        (k - l) * spatialMassCLM hΩbounded
          _ :=
      congrArg (fun q : ℝ => q - (k - l) * spatialMassCLM hΩbounded
        _)
        (scalarLpDual_shiftedPositivePart_apply hΩ x x z k).symm
    _ = scalarLpToH10HilbertGraphDual hΩ
          _ _ -
        (k - l) *
          ((spatialMassCLM hΩbounded).comp _)
            _ :=
      congrArg (fun q : ℝ =>
        scalarLpToH10HilbertGraphDual hΩ
            _ _ -
          (k - l) * q)
        (spatialMassComp_shiftedPositivePart_apply hΩ hΩbounded x k).symm
    _ = _ := (correctedDual_apply _ _ _ _).symm

private theorem correctedDualPair_sub
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A B Q : V) (k l : ℝ) :
    (A - k • Q) - (B - l • Q) = (A - B) - (k - l) • Q := by
  module

private theorem scalarLpDual_value_sub
     :
    scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ x) -
        scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ z) =
      scalarLpToH10HilbertGraphDual hΩ
        (valueCLM hΩ x - valueCLM hΩ z) := by
  rw [map_sub]

private theorem shiftedPositivePart_curve_support_lower
     :
    ((scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ x) -
        (k : ℝ) • (spatialMassCLM hΩbounded).comp (valueCLM hΩ)) -
      (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ z) -
        (l : ℝ) • (spatialMassCLM hΩbounded).comp (valueCLM hΩ)))
        (h10ShiftedPositivePart hΩ z l) ≤
      shiftedPositivePartHalfEnergy hΩ x k - shiftedPositivePartHalfEnergy hΩ z l := by
  have hmap :
      (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ x) -
          (k : ℝ) • (spatialMassCLM hΩbounded).comp (valueCLM hΩ)) -
        (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ z) -
          (l : ℝ) • (spatialMassCLM hΩbounded).comp (valueCLM hΩ)) =
      scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ x - valueCLM hΩ z) -
        (k - (l : ℝ)) •
          (spatialMassCLM hΩbounded).comp (valueCLM hΩ) := by
    calc
      _ = (scalarLpToH10HilbertGraphDual hΩ _ -
            scalarLpToH10HilbertGraphDual hΩ _) -
          (k - (l : ℝ)) •
            (spatialMassCLM hΩbounded).comp _ :=
        correctedDualPair_sub _ _ _ _ _
      _ = _ := congrArg (fun A : H10HilbertGraphDual hΩ =>
        A - (k - (l : ℝ)) •
          (spatialMassCLM hΩbounded).comp _)
        (scalarLpDual_value_sub hΩ x z)
  rw [hmap]
  exact shiftedPositivePart_support_lower hΩ hΩbounded x z k l

private theorem shiftedPositivePart_curve_support_upper
     :
    shiftedPositivePartHalfEnergy hΩ x k - shiftedPositivePartHalfEnergy hΩ z l ≤
    ((scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ x) -
        (k : ℝ) • (spatialMassCLM hΩbounded).comp (valueCLM hΩ)) -
      (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ z) -
        (l : ℝ) • (spatialMassCLM hΩbounded).comp (valueCLM hΩ)))
        (h10ShiftedPositivePart hΩ x k) := by
  have hmap :
      (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ x) -
          (k : ℝ) • (spatialMassCLM hΩbounded).comp (valueCLM hΩ)) -
        (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ z) -
          (l : ℝ) • (spatialMassCLM hΩbounded).comp (valueCLM hΩ)) =
      scalarLpToH10HilbertGraphDual hΩ
          (valueCLM hΩ x - valueCLM hΩ z) -
        (k - (l : ℝ)) •
          (spatialMassCLM hΩbounded).comp (valueCLM hΩ) := by
    calc
      _ = (scalarLpToH10HilbertGraphDual hΩ _ -
            scalarLpToH10HilbertGraphDual hΩ _) -
          (k - (l : ℝ)) •
            (spatialMassCLM hΩbounded).comp _ :=
        correctedDualPair_sub _ _ _ _ _
      _ = _ := congrArg (fun A : H10HilbertGraphDual hΩ =>
        A - (k - (l : ℝ)) •
          (spatialMassCLM hΩbounded).comp _)
        (scalarLpDual_value_sub hΩ x z)
  rw [hmap]
  exact shiftedPositivePart_support_upper hΩ hΩbounded x z k l

theorem tendsto_clm_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {L : Filter ℝ} {f : ℝ → V →L[ℝ] ℝ} {g : ℝ → V}
    {a : V →L[ℝ] ℝ} {b : V}
    (hf : Tendsto f L (𝓝 a)) (hg : Tendsto g L (𝓝 b)) :
    Tendsto (fun t => f t (g t)) L (𝓝 (a b)) := by
  simpa only [Function.comp_def] using
    (isBoundedBilinearMap_apply.continuous.tendsto _).comp (hf.prodMk_nhds hg)

theorem slope_energy_error_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
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
    field_simp [sub_ne_zero.mpr]
  have hright : slope U t s (p s - p t) =
      (s - t)⁻¹ * (U s - U t) (p s - p t) := by
    rw [slope_def_module, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hleft, hright, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left habs (abs_nonneg _)

theorem hasDerivAt_of_support_inequalities
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : ℝ → V →L[ℝ] ℝ) (p : ℝ → V) (E : ℝ → ℝ)
    (hp : Continuous p) (y : V →L[ℝ] ℝ) (t : ℝ)
    (hpivot : HasDerivAt U y t)
    (hlower : ∀ r s, (U r - U s) (p s) ≤ E r - E s)
    (hupper : ∀ r s, E r - E s ≤ (U r - U s) (p r)) :
    HasDerivAt E (y (p t)) t := by
  have hSlopeU : Tendsto (slope U t) (𝓝[≠] t) (𝓝 y) := hpivot.tendsto_slope
  have hpDiff : Tendsto (fun s => p s - p t) (𝓝[≠] t) (𝓝 0) := by
    simpa using
      ((hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).sub
        (tendsto_const_nhds : Tendsto _ (𝓝[≠] t) (𝓝 (p t))))
  have hSmall : Tendsto (fun s => slope U t s (p s - p t))
      (𝓝[≠] t) (𝓝 0) := by
    simpa using tendsto_clm_apply hSlopeU hpDiff
  have hCompare : ∀ᶠ s in 𝓝[≠] t,
      |slope E t s - slope U t s (p t)| ≤
        |slope U t s (p s - p t)| := by
    filter_upwards [self_mem_nhdsWithin] with s hst
    have hLower := hlower s t
    have hUpper := hupper s t
    apply slope_energy_error_le E U p hst (sub_nonneg.mpr hLower)
    have := sub_le_sub_right hUpper ((U s - U t) (p t))
    simpa only [ContinuousLinearMap.map_sub] using this
  have hErr : Tendsto (fun s => slope E t s - slope U t s (p t))
      (𝓝[≠] t) (𝓝 0) := by
    rw [Metric.tendsto_nhds] at hSmall ⊢
    intro ε hε
    filter_upwards [hCompare, hSmall ε hε] with s hcomp hsmall
    rw [Real.dist_eq]
    simpa using lt_of_le_of_lt hcomp
      (by simpa using hsmall)
  have hEval : Tendsto _
      _ (𝓝 (y (p t))) :=
    tendsto_clm_apply hSlopeU tendsto_const_nhds
  apply hasDerivAt_iff_tendsto_slope.mpr
  simpa using hErr.add hEval

private theorem hasDerivAt_correctedPivot
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (M N : ℝ≥0) (U : ℝ → V) (y : V) (Q : V) (t : ℝ) (ht0 : 0 < t)
    (hx : HasDerivAt U y t) :
    HasDerivAt
      (fun s => U s - (reverseTimeAffineThreshold M N s : ℝ) • Q)
      (y - (N : ℝ) • Q) t := by
  have hk : HasDerivAt (fun s : ℝ => M + s * N) N t := by
    convert (hasDerivAt_const t (M : ℝ)).add
      ((hasDerivAt_id t).mul_const N) using 1
    all_goals first | (simp [Pi.add_def]) | ring
  have hkQ : HasDerivAt (fun s : ℝ => (M + s * N) • Q)
      ((N : ℝ) • Q) t := hk.smul_const Q
  have hraw := hx.sub hkQ
  apply hraw.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht0] with s hs
  rw [coe_reverseTimeAffineThreshold_of_nonneg M N hs.le]
  rfl

/-- The moving-threshold half-energy derivative obtained from convex support. -/
theorem hasDerivAt_shiftedPositivePartHalfEnergy
     (M N : ℝ≥0)
    (x : ℝ → H10HilbertGraph hΩ) (hx : Continuous x)
    (y : H10HilbertGraphDual hΩ) (t : ℝ) (ht0 : 0 < t)
    (hpivot : HasDerivAt
      (fun s => scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ (x s))) y t) :
    HasDerivAt
      (fun s => shiftedPositivePartHalfEnergy hΩ (x s)
        (reverseTimeAffineThreshold M N s))
      ((y - (N : ℝ) • (spatialMassCLM hΩbounded).comp (valueCLM hΩ))
        (h10ShiftedPositivePart hΩ (x t) (reverseTimeAffineThreshold M N t))) t := by
  let U  := fun s =>
    scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ (x s)) -
      (reverseTimeAffineThreshold M N s : ℝ) •
        (spatialMassCLM hΩbounded).comp (valueCLM hΩ)
  let p  := fun s =>
    h10ShiftedPositivePart hΩ (x s) (reverseTimeAffineThreshold M N s)
  let E  := fun s =>
    shiftedPositivePartHalfEnergy hΩ (x s) (reverseTimeAffineThreshold M N s)
  have hk : Continuous (reverseTimeAffineThreshold M N) := continuous_const.add (continuous_real_toNNReal.mul continuous_const)
  have hp : Continuous p := (continuous_h10ShiftedPositivePart hΩ).comp
    (hx.prodMk hk)
  exact hasDerivAt_of_support_inequalities U p E hp
    _ t
    (hasDerivAt_correctedPivot M N
      _ y
      _ t ht0 hpivot)
    (fun r s => shiftedPositivePart_curve_support_lower hΩ hΩbounded
      _ _ _
      _)
    (fun r s => shiftedPositivePart_curve_support_upper hΩ hΩbounded
      _ _ _
      _)

end HypoellipticAleksandrov.Parabolic.Dirichlet
