module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10PositivePartContinuity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandSteklov
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimePositivePartPairingConvergence
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimePositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertTraces

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet
open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

private theorem positivePart_mul_sub_le_half_sq_sub_sq (x z : ℝ) :
    max z 0 * (x - z) ≤ ((max x 0) ^ 2 - (max z 0) ^ 2) / 2 := by
  rcases le_total x 0 with hx | hx <;> rcases le_total z 0 with hz | hz <;>
    simp only [max_eq_left, max_eq_right, hx, hz] <;>
    nlinarith [sq_nonneg (x - z)]

private theorem half_sq_sub_sq_le_positivePart_mul_sub (x z : ℝ) :
    ((max x 0) ^ 2 - (max z 0) ^ 2) / 2 ≤ max x 0 * (x - z) := by
  rcases le_total x 0 with hx | hx <;> rcases le_total z 0 with hz | hz <;>
    simp only [max_eq_left, max_eq_right, hx, hz] <;>
    nlinarith [sq_nonneg (x - z)]

/-- Half the squared pivot norm of the positive part. -/
def positivePartHalfEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (v : H10HilbertGraph hΩ) : ℝ :=
  (1 / 2 : ℝ) * ‖valueCLM hΩ (h10PositivePart hΩ v)‖ ^ 2

private theorem scalarLp_norm_sq_eq_integral_sq
    {d : ℕ} {Ω : Set (PDE.Vec d)} (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ‖f‖ ^ 2 = ∫ a, (f a) ^ 2 ∂(PDE.volumeOn Ω) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext a
  simp

private theorem scalarLp_integrable_sq
    {d : ℕ} {Ω : Set (PDE.Vec d)} (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    Integrable (fun a => (f a) ^ 2) (PDE.volumeOn Ω) := by
  exact (MeasureTheory.Lp.memLp f).integrable_sq

private theorem scalarLp_positivePart_support_lower
    {d : ℕ} {Ω : Set (PDE.Vec d)} (f z : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    inner ℝ (MeasureTheory.Lp.posPart z) (f - z) ≤
      (1 / 2 : ℝ) * ‖MeasureTheory.Lp.posPart f‖ ^ 2 -
        (1 / 2 : ℝ) * ‖MeasureTheory.Lp.posPart z‖ ^ 2 := by
  rw [scalarLp_norm_sq_eq_integral_sq (MeasureTheory.Lp.posPart f),
    scalarLp_norm_sq_eq_integral_sq (MeasureTheory.Lp.posPart z),
    L2.inner_def]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub
      ((scalarLp_integrable_sq (MeasureTheory.Lp.posPart f)).const_mul _)
      ((scalarLp_integrable_sq (MeasureTheory.Lp.posPart z)).const_mul _)]
  apply integral_mono_ae
    (L2.integrable_inner (MeasureTheory.Lp.posPart z) (f - z))
    (((scalarLp_integrable_sq (MeasureTheory.Lp.posPart f)).const_mul _).sub
      ((scalarLp_integrable_sq (MeasureTheory.Lp.posPart z)).const_mul _))
  filter_upwards [Lp.coeFn_posPart f, Lp.coeFn_posPart z,
    Lp.coeFn_sub f z] with a hfa hza hsub
  simp only [Pi.sub_apply, hfa, hza, hsub, RCLike.inner_apply, conj_trivial]
  nlinarith [positivePart_mul_sub_le_half_sq_sub_sq (f a) (z a)]

private theorem scalarLp_positivePart_support_upper
    {d : ℕ} {Ω : Set (PDE.Vec d)} (f z : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    (1 / 2 : ℝ) * ‖MeasureTheory.Lp.posPart f‖ ^ 2 -
        (1 / 2 : ℝ) * ‖MeasureTheory.Lp.posPart z‖ ^ 2 ≤
      inner ℝ (MeasureTheory.Lp.posPart f) (f - z) := by
  rw [scalarLp_norm_sq_eq_integral_sq (MeasureTheory.Lp.posPart f),
    scalarLp_norm_sq_eq_integral_sq (MeasureTheory.Lp.posPart z),
    L2.inner_def]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub
      ((scalarLp_integrable_sq (MeasureTheory.Lp.posPart f)).const_mul _)
      ((scalarLp_integrable_sq (MeasureTheory.Lp.posPart z)).const_mul _)]
  apply integral_mono_ae
    (((scalarLp_integrable_sq (MeasureTheory.Lp.posPart f)).const_mul _).sub
      ((scalarLp_integrable_sq (MeasureTheory.Lp.posPart z)).const_mul _))
    (L2.integrable_inner (MeasureTheory.Lp.posPart f) (f - z))
  filter_upwards [Lp.coeFn_posPart f, Lp.coeFn_posPart z,
    Lp.coeFn_sub f z] with a hfa hza hsub
  simp only [Pi.sub_apply, hfa, hza, hsub, RCLike.inner_apply, conj_trivial]
  nlinarith [half_sq_sub_sq_le_positivePart_mul_sub (f a) (z a)]

private theorem positivePart_support_lower
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (x z : H10HilbertGraph hΩ) :
    (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ x) -
        scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ z))
        (h10PositivePart hΩ z) ≤
      positivePartHalfEnergy hΩ x - positivePartHalfEnergy hΩ z := by
  rw [ContinuousLinearMap.sub_apply, scalarLpToH10HilbertGraphDual_apply,
    scalarLpToH10HilbertGraphDual_apply, valueCLM_h10PositivePart]
  simp only [positivePartHalfEnergy, valueCLM_h10PositivePart]
  rw [← inner_sub_right]
  exact scalarLp_positivePart_support_lower (valueCLM hΩ x) (valueCLM hΩ z)

private theorem positivePart_support_upper
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (x z : H10HilbertGraph hΩ) :
    positivePartHalfEnergy hΩ x - positivePartHalfEnergy hΩ z ≤
      (scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ x) -
        scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ z))
        (h10PositivePart hΩ x) := by
  rw [ContinuousLinearMap.sub_apply, scalarLpToH10HilbertGraphDual_apply,
    scalarLpToH10HilbertGraphDual_apply, valueCLM_h10PositivePart]
  simp only [positivePartHalfEnergy, valueCLM_h10PositivePart]
  rw [← inner_sub_right]
  exact scalarLp_positivePart_support_upper (valueCLM hΩ x) (valueCLM hΩ z)


private theorem slope_energy_error_le
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
    field_simp [sub_ne_zero.mpr hst]
  have hright : slope U t s (p s - p t) =
      (s - t)⁻¹ * (U s - U t) (p s - p t) := by
    rw [slope_def_module, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hleft, hright, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left habs (abs_nonneg _)

private theorem hasDerivAt_of_support_inequalities
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : ℝ → V →L[ℝ] ℝ) (p : ℝ → V) (E : ℝ → ℝ)
    (hp : Continuous p) (y : V →L[ℝ] ℝ) (t : ℝ)
    (hpivot : HasDerivAt U y t)
    (hlower : ∀ r s, (U r - U s) (p s) ≤ E r - E s)
    (hupper : ∀ r s, E r - E s ≤ (U r - U s) (p r)) :
    HasDerivAt E (y (p t)) t  := by
  have tendsto_clm_apply [NormedAddCommGroup V] [NormedSpace ℝ V] {L : Filter ℝ} {f : ℝ → V →L[ℝ] ℝ} {g : ℝ → V} {a : V →L[ℝ] ℝ} {b : V} (hf : Tendsto f L (𝓝 a)) (hg : Tendsto g L (𝓝 b)) :
      Tendsto (fun t => f t (g t)) L (𝓝 (a b)) := by
    simpa only [Function.comp_def] using
      (isBoundedBilinearMap_apply.continuous.tendsto (a, b)).comp (hf.prodMk_nhds hg)
  have hSlopeU := hpivot.tendsto_slope
  have hpDiff : Tendsto (fun s => p s - p t) (𝓝[≠] t) (𝓝 0) := by
    simpa using
      ((hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).sub
        (tendsto_const_nhds : Tendsto (fun _ => p t) (𝓝[≠] t) (𝓝 (p t))))
  have hSmall : Tendsto (fun s => slope U t s (p s - p t))
      (𝓝[≠] t) (𝓝 0) := by
    simpa using tendsto_clm_apply hSlopeU hpDiff
  have hCompare : ∀ᶠ s in 𝓝[≠] t,
      |slope E t s - slope U t s (p t)| ≤
        |slope U t s (p s - p t)| := by
    filter_upwards [self_mem_nhdsWithin] with s hst
    have hraw0 : 0 ≤ (E s - E t) - (U s - U t) (p t) := by
      exact sub_nonneg.mpr (hlower s t)
    have hraw1 : (E s - E t) - (U s - U t) (p t) ≤
        (U s - U t) (p s - p t) := by
      have := sub_le_sub_right (hupper s t) ((U s - U t) (p t))
      simpa only [ContinuousLinearMap.map_sub] using this
    exact slope_energy_error_le E U p hst hraw0 hraw1
  have hErr : Tendsto (fun s => slope E t s - slope U t s (p t))
      (𝓝[≠] t) (𝓝 0) := by
    rw [Metric.tendsto_nhds] at hSmall ⊢
    intro ε hε
    filter_upwards [hCompare, hSmall ε hε] with s hcomp hsmall
    rw [Real.dist_eq]
    simpa using lt_of_le_of_lt hcomp
      (by simpa [Real.dist_eq] using hsmall)
  have hEval : Tendsto (fun s => slope U t s (p t)) (𝓝[≠] t) (𝓝 (y (p t))) :=
    tendsto_clm_apply hSlopeU tendsto_const_nhds
  apply hasDerivAt_iff_tendsto_slope.mpr
  simpa [sub_add_cancel] using hErr.add hEval


/-- Fixed-window forward Steklov positive-part energy identity in the
reverse-time Gelfand triple. -/
theorem reverseTimeForwardSteklov_positivePart_energy_identity
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h a b : ℝ} (hh : 0 < h) (ha0 : 0 ≤ a) (hab : a ≤ b)
    (hbT : b + h ≤ T) :
    ‖valueCLM hΩ (h10PositivePart hΩ (reverseTimeForwardSteklov T h u b))‖ ^ 2 -
        ‖valueCLM hΩ (h10PositivePart hΩ (reverseTimeForwardSteklov T h u a))‖ ^ 2 =
      2 * (∫ t in Set.Icc a b, (reverseTimeForwardSteklov T h g t)
        (h10PositivePart hΩ (reverseTimeForwardSteklov T h u t)))  := by
  have hasDerivAt_positivePartHalfEnergy_of_pivoted_curve {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (x : ℝ → H10HilbertGraph hΩ) (hx : Continuous x) (y : H10HilbertGraphDual hΩ) (t : ℝ) (hpivot : HasDerivAt
      (fun s => scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ (x s))) y t) :
      HasDerivAt (fun s => positivePartHalfEnergy hΩ (x s))
      (y (h10PositivePart hΩ (x t))) t := by
    exact hasDerivAt_of_support_inequalities
      (fun s => scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ (x s)))
      (fun s => h10PositivePart hΩ (x s))
      (fun s => positivePartHalfEnergy hΩ (x s))
      ((continuous_h10PositivePart hΩ).comp hx) y t hpivot
      (fun r s => positivePart_support_lower hΩ (x r) (x s))
      (fun r s => positivePart_support_upper hΩ (x r) (x s))
  let x : ℝ → H10HilbertGraph hΩ := fun t => reverseTimeForwardSteklov T h u t
  let y : ℝ → H10HilbertGraphDual hΩ := fun t => reverseTimeForwardSteklov T h g t
  let E : ℝ → ℝ := fun t => positivePartHalfEnergy hΩ (x t)
  have hx := continuous_reverseTimeForwardSteklov T h hh u
  have hE : Continuous E := by
    exact continuous_const.mul ((continuous_norm.comp ((valueCLM hΩ).continuous.comp
      ((continuous_h10PositivePart hΩ).comp hx))).pow 2)
  have hpair :=
    (continuous_reverseTimeForwardSteklov T h hh g).clm_apply ((continuous_h10PositivePart hΩ).comp hx)
  have hderivE : ∀ t ∈ Ioo a b, HasDerivAt E
      (y t (h10PositivePart hΩ (x t))) t := by
    intro t ht
    exact hasDerivAt_positivePartHalfEnergy_of_pivoted_curve hΩ x hx (y t) t
      (hasDerivAt_reverseTimeForwardSteklov_gelfand hΩ T hT u g hderiv hh
        (by linarith [ha0, ht.1]) (by linarith [hbT, ht.2]))
  calc
    _ = 2 * (E b - E a) := by simp only [E, positivePartHalfEnergy]; ring
    _ = 2 * (∫ t in a..b, y t (h10PositivePart hΩ (x t))) := by rw [(intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hE.continuousOn hderivE (hpair.intervalIntegrable a b))]
    _ = 2 * (∫ t in Ioc a b, y t (h10PositivePart hΩ (x t))) := by
      rw [intervalIntegral.integral_of_le hab]
    _ = 2 * (∫ t in Icc a b, y t (h10PositivePart hΩ (x t))) := by
      rw [integral_Icc_eq_integral_Ioc]
    _ = _ := rfl



private noncomputable def rawPositivePartEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) : ℝ → ℝ :=
  fun t => ‖valueCLM hΩ (h10PositivePart hΩ (u t))‖ ^ 2

private noncomputable def rawPositivePartEnergyRate
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ :=
  fun t => 2 * (g t) (h10PositivePart hΩ (u t))

private noncomputable def reverseTimePositivePartEnergyPrimitive
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ :=
  fun t => ∫ r in Set.Ioc 0 t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T


private theorem integrable_rawPositivePartEnergyRate
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    Integrable (rawPositivePartEnergyRate hΩ T u g) (reverseTimeVolume T) := by
  exact ((integrable_reverseTimeDualPairing hΩ T
    (reverseTimePositivePart hΩ T u) g).const_mul 2).congr (by
      filter_upwards [coeFn_reverseTimePositivePart hΩ T u] with t ht
      simp only [rawPositivePartEnergyRate]
      rw [ht])




private theorem integral_reverseTime_eq_integral_Icc_of_tsupport_subset
    {T a b : ℝ} {F phi : ℝ → ℝ}
    (hK : Icc a b ⊆ Ioo (0 : ℝ) T) (hphi : tsupport phi ⊆ Ioo a b) :
    (∫ t, F t * phi t ∂reverseTimeVolume T) = ∫ t in Icc a b, F t * phi t := by
  change (∫ t in Ioo 0 T, F t * phi t) = ∫ t in Icc a b, F t * phi t
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioo hK
  intro t ht
  rw [image_eq_zero_of_notMem_tsupport (fun hts => ht.2
    ⟨le_of_lt (hphi hts).1, le_of_lt (hphi hts).2⟩)]
  ring

private theorem integral_energy_mul_deriv_eq_neg_integral_pairing_of_increment
    {a b : ℝ} {E Q : ℝ → ℝ} (hab : a ≤ b)
    (hE : Continuous E) (hQ : Continuous Q)
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      E t - E s = ∫ r in Icc s t, Q r)
    {eta : ℝ → ℝ} (heta : ContDiff ℝ 1 eta) (hsupp : tsupport eta ⊆ Ioo a b) :
    (∫ t in Icc a b, E t * deriv eta t) =
      -(∫ t in Icc a b, Q t * eta t) := by
  have hQIcc : IntegrableOn Q (Icc a b) volume := hQ.integrableOn_Icc
  have hEIcc : IntegrableOn E (Icc a b) volume := hE.integrableOn_Icc
  have hetaIcc : IntegrableOn eta (Icc a b) volume := heta.continuous.integrableOn_Icc
  have hderivIcc : IntegrableOn (deriv eta) (Icc a b) volume :=
    (heta.continuous_deriv (by simp)).integrableOn_Icc
  have hEformula : ∀ t ∈ Icc a b, E t = PDE.intervalPrimitive a Q t + E a := by
    intro t ht
    have h := hinc a ⟨le_rfl, hab⟩ t ht ht.1
    calc
      E t = (∫ r in Icc a t, Q r) + E a := by linarith
      _ = PDE.intervalPrimitive a Q t + E a := by
        rw [PDE.intervalPrimitive_eq_setIntegral_Icc ht.1]
  have hleft : (∫ t in Icc a b, E t * deriv eta t) =
      ∫ t in Icc a b, (PDE.intervalPrimitive a Q t + E a) * deriv eta t := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    change E t * deriv eta t = _
    rw [hEformula t ht]
  rw [hleft]
  calc
    (∫ t in Icc a b, (PDE.intervalPrimitive a Q t + E a) * deriv eta t) =
        ∫ t in Icc a b,
          PDE.intervalPrimitive a Q t * deriv eta t + E a * deriv eta t := by
            apply setIntegral_congr_fun measurableSet_Icc
            intro t _
            ring
    _ = (∫ t in Icc a b, PDE.intervalPrimitive a Q t * deriv eta t) +
        ∫ t in Icc a b, E a * deriv eta t := by
          rw [integral_add]
          · exact ((PDE.continuousOn_intervalPrimitive hab hQIcc).mul
              (heta.continuous_deriv (by simp)).continuousOn).integrableOn_Icc
          · simpa using hderivIcc.const_mul (E a)
    _ = -(∫ t in Icc a b, Q t * eta t) := by
      rw [PDE.intervalPrimitive_scalar_weak_identity_Icc hQIcc heta hsupp]
      have htail : ∫ t in Icc a b, deriv eta t = 0 := by
        rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le hab,
          intervalIntegral.integral_deriv_of_contDiffOn_Icc heta.contDiffOn hab]
        have ha : eta a = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          exact fun ht => (not_lt_of_ge le_rfl) (hsupp ht).1
        have hb : eta b = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          exact fun ht => (not_lt_of_ge le_rfl) (hsupp ht).2
        rw [ha, hb]
        ring
      rw [integral_const_mul, htail]
      ring

private theorem abs_sq_sub_le_of_bounds
    {a b N delta y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N)
    (hdelta : 0 ≤ delta) (hy : 0 ≤ y)
    (hdiff : |a - b| ≤ N * delta)
    (hsum : a + b ≤ N * delta + 2 * N * y) :
    |a ^ 2 - b ^ 2| ≤ N ^ 2 * delta ^ 2 + 2 * N ^ 2 * y * delta := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg ha hb)]
  calc
    (a + b) * |a - b| ≤ (N * delta + 2 * N * y) * (N * delta) := by
      exact mul_le_mul hsum hdiff (abs_nonneg _) (by positivity)
    _ = N ^ 2 * delta ^ 2 + 2 * N ^ 2 * y * delta := by ring

private theorem abs_sqNorm_valueCLM_sub_le
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (x y : H10HilbertGraph hΩ) :
    |‖valueCLM hΩ x‖ ^ 2 - ‖valueCLM hΩ y‖ ^ 2| ≤
      ‖valueCLM hΩ‖ ^ 2 * ‖x - y‖ ^ 2 +
        2 * ‖valueCLM hΩ‖ ^ 2 * ‖y‖ * ‖x - y‖ := by
  let L := valueCLM hΩ
  have hx : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    calc
      ‖x‖ = ‖(x - y) + y‖ := by
        congr 1
        abel
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
  have hLx' :=
    (L.le_opNorm x).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have hdiff : |‖L x‖ - ‖L y‖| ≤ ‖L‖ * ‖x - y‖ := by
    calc
      |‖L x‖ - ‖L y‖| ≤ ‖L x - L y‖ := abs_norm_sub_norm_le _ _
      _ = ‖L (x - y)‖ := by rw [L.map_sub]
      _ ≤ ‖L‖ * ‖x - y‖ := (L.le_opNorm (x - y))
  have hfactor : ‖L x‖ + ‖L y‖ ≤ ‖L‖ * ‖x - y‖ + 2 * ‖L‖ * ‖y‖ := by
    calc
      ‖L x‖ + ‖L y‖ ≤ ‖L‖ * (‖x - y‖ + ‖y‖) + ‖L‖ * ‖y‖ :=
        add_le_add hLx' (L.le_opNorm y)
      _ = ‖L‖ * ‖x - y‖ + 2 * ‖L‖ * ‖y‖ := by ring
  exact abs_sq_sub_le_of_bounds (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) hdiff hfactor

private theorem memLp_on_Icc_of_continuous
    {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (hf : Continuous f) (a b : ℝ) :
    MemLp f (2 : ℝ≥0∞) (volume.restrict (Icc a b)) := by
  refine (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr ?_
  exact (hf.norm.pow 2).integrableOn_Icc

private theorem eventually_memLp_reverseTimeForwardSteklov_on_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (f : MeasureTheory.Lp E 2 (reverseTimeVolume T)) (a b : ℝ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      MemLp (reverseTimeForwardSteklov T h f) 2
        (volume.restrict (Icc a b)) := by
  filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
    with h hh
  exact memLp_on_Icc_of_continuous _
    (continuous_reverseTimeForwardSteklov T h hh f) a b

private theorem memLp_restrict_Icc_of_subset
    {E : Type*} [NormedAddCommGroup E] (T : ℝ)
    (f : MeasureTheory.Lp E 2 (reverseTimeVolume T)) {a b : ℝ}
    (hK : Icc a b ⊆ Ioo (0 : ℝ) T) :
    MemLp (f : ℝ → E) 2 (volume.restrict (Icc a b)) := by
  dsimp only [reverseTimeVolume, reverseTimeOpenInterval]
  rw [← Measure.restrict_restrict_of_subset hK]
  exact (Lp.memLp f).restrict _


private theorem tendsto_integral_mul_of_tendsto_integral_abs
    {μ : Measure ℝ} {F : ℝ → ℝ → ℝ} {f phi : ℝ → ℝ}
    (hF : ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable (F h) μ)
    (hf : Integrable f μ) (hphi : AEStronglyMeasurable phi μ)
    (hbound : ∃ C : ℝ, ∀ t : ℝ, ‖phi t‖ ≤ C)
    (hlim : Tendsto (fun h : ℝ => ∫ t, |F h t - f t| ∂μ) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => ∫ t, F h t * phi t ∂μ) (𝓝[>] 0)
      (𝓝 (∫ t, f t * phi t ∂μ)) := by
  obtain ⟨C, hC⟩ := hbound
  have hCnorm : ∀ t : ℝ, ‖‖phi t‖‖ ≤ C := by
    intro t
    simpa only [norm_norm] using hC t
  have hC0 : 0 ≤ C := by
    have := hC 0
    exact (norm_nonneg _).trans this
  have herr : Tendsto (fun h => ∫ t, (F h t - f t) * phi t ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero'
    · filter_upwards with h
      exact norm_nonneg _
    · filter_upwards [hF] with h hF
      have hdiff := hF.sub hf
      have hprod :=
        hdiff.norm.mul_bdd hphi.norm (Eventually.of_forall fun t => hCnorm t)
      calc
        ‖∫ t, (F h t - f t) * phi t ∂μ‖ ≤
            ∫ t, ‖(F h t - f t) * phi t‖ ∂μ := norm_integral_le_integral_norm _
        _ = ∫ t, |F h t - f t| * ‖phi t‖ ∂μ := by
          apply integral_congr_ae
          filter_upwards with t
          rw [norm_mul, Real.norm_eq_abs]
        _ ≤ ∫ t, C * |F h t - f t| ∂μ := by
          apply integral_mono
          · exact hprod
          · exact hdiff.norm.const_mul C
          · intro t
            calc
              |F h t - f t| * ‖phi t‖ ≤ |F h t - f t| * C :=
                mul_le_mul_of_nonneg_left (hC t) (abs_nonneg _)
              _ = C * |F h t - f t| := mul_comm _ _
        _ = C * (∫ t, |F h t - f t| ∂μ) :=
          integral_const_mul C (fun t => |F h t - f t|)
    · simpa using tendsto_const_nhds.mul hlim
  have hsum : Tendsto (fun h =>
      (∫ t, (F h t - f t) * phi t ∂μ) + ∫ t, f t * phi t ∂μ)
      (𝓝[>] 0) (𝓝 (∫ t, f t * phi t ∂μ)) := by
    simpa using herr.add tendsto_const_nhds
  apply hsum.congr'
  filter_upwards [hF] with h hF
  have hprod : Integrable (fun t => (F h t - f t) * phi t) μ :=
    (hF.sub hf).mul_bdd hphi (Eventually.of_forall fun t => hC t)
  rw [← integral_add hprod (hf.mul_bdd hphi (Eventually.of_forall fun t => hC t))]
  apply integral_congr_ae
  filter_upwards with t
  ring

private noncomputable def forwardSteklovPositivePartEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T h : ℝ)
    (u : ReverseTimeL2V hΩ T) : ℝ → ℝ :=
  fun t => ‖valueCLM hΩ
    (h10PositivePart hΩ (reverseTimeForwardSteklov T h u t))‖ ^ 2

private noncomputable def forwardSteklovPositivePartEnergyRate
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T h : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ :=
  fun t => 2 * (reverseTimeForwardSteklov T h g t)
    (h10PositivePart hΩ (reverseTimeForwardSteklov T h u t))

private theorem abs_two_mul_sub (x y : ℝ) :
    |2 * x - 2 * y| = 2 * |x - y| := by
  rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]


private theorem forwardSteklovPositivePartEnergy_increment
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    {h a b s t : ℝ} (hh : 0 < h) (ha : 0 < a)
    (hsmall : h < T - b) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    forwardSteklovPositivePartEnergy hΩ T h u t -
        forwardSteklovPositivePartEnergy hΩ T h u s =
      ∫ r in Icc s t, forwardSteklovPositivePartEnergyRate hΩ T h u g r := by
  change ‖valueCLM hΩ (h10PositivePart hΩ (reverseTimeForwardSteklov T h u t))‖ ^ 2 -
      ‖valueCLM hΩ (h10PositivePart hΩ (reverseTimeForwardSteklov T h u s))‖ ^ 2 = _
  calc
    _ = 2 * (∫ r in Icc s t, (reverseTimeForwardSteklov T h g r)
        (h10PositivePart hΩ (reverseTimeForwardSteklov T h u r))) :=
      reverseTimeForwardSteklov_positivePart_energy_identity hΩ T hT u g hderiv hh
        (le_trans ha.le hs.1) hst (by linarith [ht.2, hsmall])
    _ = ∫ r in Icc s t, forwardSteklovPositivePartEnergyRate hΩ T h u g r := by
      change 2 * (∫ r in Icc s t, (reverseTimeForwardSteklov T h g r)
          (h10PositivePart hΩ (reverseTimeForwardSteklov T h u r))) =
        ∫ r in Icc s t, 2 * (reverseTimeForwardSteklov T h g r)
          (h10PositivePart hΩ (reverseTimeForwardSteklov T h u r))
      rw [integral_const_mul]










/-- Positive-part energy increment for the canonical closed-time Hilbert representative. -/
theorem reverseTimeHilbertRepresentative_posPart_norm_sq_increment
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (s t : ℝ) (hs : s ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T)
    (hst : s ≤ t) :
    ‖MeasureTheory.Lp.posPart
        (reverseTimeHilbertRepresentative hΩ T hT u g hderiv ⟨t, ht⟩)‖ ^ 2 -
      ‖MeasureTheory.Lp.posPart
        (reverseTimeHilbertRepresentative hΩ T hT u g hderiv ⟨s, hs⟩)‖ ^ 2 =
      2 * (∫ r in Set.Ioc s t,
        (g r) (h10PositivePart hΩ (u r)) ∂reverseTimeVolume T)    := by
  have continuousOn_reverseTimePositivePartEnergyPrimitive {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
      ContinuousOn (reverseTimePositivePartEnergyPrimitive hΩ T u g) (Icc 0 T) := by
    letI : NullSingletonClass (reverseTimeVolume T) := by
      change NullSingletonClass (volume.restrict (Ioo 0 T))
      infer_instance
    exact intervalIntegral.continuousOn_primitive
      (integrable_rawPositivePartEnergyRate hΩ T u g).integrableOn
  have integrable_rawPositivePartEnergy {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T) :
      Integrable (rawPositivePartEnergy hΩ T u) (reverseTimeVolume T) := by
    letI : IsFiniteMeasure (reverseTimeVolume T) := by
      change IsFiniteMeasure (volume.restrict (Ioo 0 T))
      infer_instance
    have hu :=
      memLp_congr_ae (by
          filter_upwards [coeFn_reverseTimePositivePart hΩ T u] with t ht
          exact congrArg (valueCLM hΩ) ht) |>.mp
        ((MeasureTheory.Lp.memLp (reverseTimePositivePart hΩ T u)).continuousLinearMap_comp
          (valueCLM hΩ))
    exact hu.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have exists_continuous_reverseTimePositivePartEnergyRepresentative {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
      ∃ e : ℝ → ℝ,
      ContinuousOn e (Set.Icc 0 T) ∧
      (∀ t : ℝ, t ∈ Set.Icc 0 T → 0 ≤ e t) ∧
      (fun t => e t) =ᵐ[reverseTimeVolume T]
        (fun t => ‖valueCLM hΩ (h10PositivePart hΩ (u t))‖ ^ 2) ∧
      ∀ s t : ℝ, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T → s ≤ t →
        e t - e s =
          2 * (∫ r in Set.Ioc s t,
            (g r) (h10PositivePart hΩ (u r)) ∂reverseTimeVolume T) := by
    have exists_continuous_reverseTimePositivePartEnergyRepresentative_raw {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
        ∃ e : ℝ → ℝ,
        ContinuousOn e (Icc 0 T) ∧
        (∀ t : ℝ, t ∈ Icc 0 T → 0 ≤ e t) ∧
        (fun t => e t) =ᵐ[reverseTimeVolume T] rawPositivePartEnergy hΩ T u ∧
        ∀ s t : ℝ, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t →
          e t - e s = ∫ r in Ioc s t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T := by
      have reverseTimePositivePartEnergyPrimitive_test_deriv {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (eta : ReverseTimeScalarTest T) :
          (∫ t, reverseTimePositivePartEnergyPrimitive hΩ T u g t * eta.deriv t
          ∂reverseTimeVolume T) =
          -(∫ t, rawPositivePartEnergyRate hΩ T u g t * eta t ∂reverseTimeVolume T) := by
        have hrateIcc : IntegrableOn (rawPositivePartEnergyRate hΩ T u g) (Icc 0 T) volume := by
          change Integrable (rawPositivePartEnergyRate hΩ T u g) (volume.restrict (Icc 0 T))
          simpa only [reverseTimeVolume, reverseTimeOpenInterval,
            restrict_Ioo_eq_restrict_Icc] using (integrable_rawPositivePartEnergyRate hΩ T u g)
        have hae : (fun t => reverseTimePositivePartEnergyPrimitive hΩ T u g t * eta.deriv t) =ᵐ[
            reverseTimeVolume T] fun t =>
              PDE.intervalPrimitive 0 (rawPositivePartEnergyRate hΩ T u g) t * _root_.deriv eta t := by
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
          change (∫ r in Ioc 0 t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T) *
              eta.deriv t = _
          rw [show (∫ r in Ioc 0 t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T) =
              ∫ r in Ioc 0 t, rawPositivePartEnergyRate hΩ T u g r ∂volume by
            simp only [reverseTimeVolume, reverseTimeOpenInterval,
              Measure.restrict_restrict measurableSet_Ioc]
            rw [inter_eq_left.mpr]
            intro r hr
            exact ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩,
            (intervalIntegral.integral_of_le (le_of_lt ht.1)).symm, eta.deriv_apply,
            PDE.intervalPrimitive]
        calc
          (∫ t, reverseTimePositivePartEnergyPrimitive hΩ T u g t * eta.deriv t
            ∂reverseTimeVolume T) =
              ∫ t, PDE.intervalPrimitive 0 (rawPositivePartEnergyRate hΩ T u g) t * _root_.deriv eta t
                ∂reverseTimeVolume T := integral_congr_ae hae
          _ = -(∫ t, rawPositivePartEnergyRate hΩ T u g t * eta t ∂reverseTimeVolume T) := by
            simpa only [reverseTimeVolume, reverseTimeOpenInterval] using
              PDE.intervalPrimitive_scalar_weak_identity_Ioo hrateIcc
                (eta.contDiff.of_le (by simp)) eta.tsupport_subset
      have integrable_mul_reverseTimeScalarTest_deriv {T : ℝ} {f : ℝ → ℝ} (hf : Integrable f (reverseTimeVolume T)) (eta : ReverseTimeScalarTest T) :
          Integrable (fun t => f t * eta.deriv t) (reverseTimeVolume T) := by
        obtain ⟨C, hC⟩ := eta.exists_norm_deriv_le
        apply hf.mul_bdd eta.contDiff_deriv.continuous.aestronglyMeasurable
        filter_upwards with t
        exact hC t
      have integrable_reverseTimePositivePartEnergyPrimitive {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
          Integrable (reverseTimePositivePartEnergyPrimitive hΩ T u g) (reverseTimeVolume T) := by
        change IntegrableOn (reverseTimePositivePartEnergyPrimitive hΩ T u g) (Ioo 0 T) volume
        exact (continuousOn_reverseTimePositivePartEnergyPrimitive hΩ T u g).integrableOn_Icc.mono_set
          Ioo_subset_Icc_self
      have rawPositivePartEnergy_test_deriv {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) (eta : ReverseTimeScalarTest T) :
          (∫ t, rawPositivePartEnergy hΩ T u t * eta.deriv t ∂reverseTimeVolume T) =
          -(∫ t, rawPositivePartEnergyRate hΩ T u g t * eta t ∂reverseTimeVolume T) := by
        have tendsto_forwardSteklov_positivePartEnergyRate_test {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (eta : ReverseTimeScalarTest T) {a : ℝ} {b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) (hK : Icc a b ⊆ Ioo 0 T) :
            Tendsto (fun h => ∫ t in Icc a b,
            forwardSteklovPositivePartEnergyRate hΩ T h u g t * eta t)
            (𝓝[>] 0) (𝓝 (∫ t in Icc a b,
              rawPositivePartEnergyRate hΩ T u g t * eta t)) := by
          have abs_forwardSteklovPositivePartEnergyRate_sub_eq {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (h : ℝ) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (t : ℝ) :
              |forwardSteklovPositivePartEnergyRate hΩ T h u g t - rawPositivePartEnergyRate hΩ T u g t| =
              2 * |(reverseTimeForwardSteklov T h g t)
                (h10PositivePart hΩ (reverseTimeForwardSteklov T h u t)) -
                  (g t) (h10PositivePart hΩ (u t))| := by
            change |2 * (reverseTimeForwardSteklov T h g t)
                (h10PositivePart hΩ (reverseTimeForwardSteklov T h u t)) -
                  2 * (g t) (h10PositivePart hΩ (u t))| = _
            exact abs_two_mul_sub _ _
          have hpair : Integrable (fun t => (g t) (h10PositivePart hΩ (u t)))
              (volume.restrict (Icc a b)) := by
            dsimp only [reverseTimeVolume, reverseTimeOpenInterval]
            rw [← Measure.restrict_restrict_of_subset hK]
            exact (integrable_reverseTimeDualPairing_positivePart hΩ T u g).restrict
          have hforward : ∀ᶠ h : ℝ in 𝓝[>] 0,
              Integrable (forwardSteklovPositivePartEnergyRate hΩ T h u g)
                (volume.restrict (Icc a b)) := by
            filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
              with h hh
            exact (continuous_const.mul
              ((continuous_reverseTimeForwardSteklov T h hh g).clm_apply
                ((continuous_h10PositivePart hΩ).comp
                  (continuous_reverseTimeForwardSteklov T h hh u)))).integrableOn_Icc
          let μ : Measure ℝ := volume.restrict (Icc a b)
          let up : ℝ → H10HilbertGraph hΩ := fun t => h10PositivePart hΩ (u t)
          let uhp : ℝ → ℝ → H10HilbertGraph hΩ := fun h t =>
            h10PositivePart hΩ (reverseTimeForwardSteklov T h u t)
          have huLocal : MemLp (u : ℝ → H10HilbertGraph hΩ) 2 μ := by
            simpa only [μ] using memLp_restrict_Icc_of_subset T u hK
          have hgLocal : MemLp (g : ℝ → H10HilbertGraphDual hΩ) 2 μ := by
            simpa only [μ] using memLp_restrict_Icc_of_subset T g hK
          have huh : ∀ᶠ h : ℝ in 𝓝[>] 0,
              MemLp (reverseTimeForwardSteklov T h u) 2 μ := by
            simpa only [μ] using eventually_memLp_reverseTimeForwardSteklov_on_Icc T u a b
          have hgh : ∀ᶠ h : ℝ in 𝓝[>] 0,
              MemLp (reverseTimeForwardSteklov T h g) 2 μ := by
            simpa only [μ] using eventually_memLp_reverseTimeForwardSteklov_on_Icc T g a b
          have hUraw := tendsto_forwardSteklov_sqNorm_integral_on_Icc T u ha hab.le hb
          have hQabs :=
            tendsto_dualPairing_positivePart_of_sqNorm hΩ μ
              (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ)
              (fun h r => reverseTimeForwardSteklov T h u r)
              (fun h r => reverseTimeForwardSteklov T h g r)
              huLocal hgLocal huh hgh hUraw (tendsto_forwardSteklov_sqNorm_integral_on_Icc T g ha hab.le hb)
          have hQabs2 : Tendsto (fun h => ∫ t in Icc a b,
              |forwardSteklovPositivePartEnergyRate hΩ T h u g t -
                rawPositivePartEnergyRate hΩ T u g t|) (𝓝[>] 0) (𝓝 0) := by
            convert tendsto_const_nhds.mul hQabs using 1
            · funext h
              rw [← integral_const_mul]
              apply integral_congr_ae
              filter_upwards with t
              exact abs_forwardSteklovPositivePartEnergyRate_sub_eq hΩ T h u g t
            · norm_num
          exact tendsto_integral_mul_of_tendsto_integral_abs hforward (hpair.const_mul 2)
            eta.contDiff.continuous.aestronglyMeasurable eta.exists_norm_le hQabs2
        have tendsto_forwardSteklov_positivePartEnergy_test {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T) (eta : ReverseTimeScalarTest T) {a : ℝ} {b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) (hK : Icc a b ⊆ Ioo 0 T) :
            Tendsto (fun h => ∫ t in Icc a b,
            forwardSteklovPositivePartEnergy hΩ T h u t * eta.deriv t)
            (𝓝[>] 0) (𝓝 (∫ t in Icc a b,
              rawPositivePartEnergy hΩ T u t * eta.deriv t)) := by
          have tendsto_integral_abs_valueSq_of_sqNorm {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (μ : Measure ℝ) (u : ℝ → H10HilbertGraph hΩ) (uh : ℝ → ℝ → H10HilbertGraph hΩ) (hu : MemLp u 2 μ) (huh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (uh h) 2 μ) (hU : Tendsto (fun h => ∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)
              (𝓝[>] 0) (𝓝 0)) :
              Tendsto (fun h => ∫ t,
              |‖valueCLM hΩ (uh h t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2| ∂μ)
              (𝓝[>] 0) (𝓝 0) := by
            let C : ℝ := ‖valueCLM hΩ‖ ^ 2
            have hUsqrt : Tendsto (fun h =>
                √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) := by
              simpa only [Real.sqrt_zero] using hU.sqrt
            have hfirst : Tendsto (fun h =>
                C * (∫ t, ‖uh h t - u t‖ ^ 2 ∂μ))
                (𝓝[>] 0) (𝓝 0) := by
              simpa using tendsto_const_nhds.mul hU
            have hsecond : Tendsto (fun h =>
                2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ) *
                  √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) := by
              have hconst : Tendsto (fun _ : ℝ =>
                  2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ))
                  (𝓝[>] 0) (𝓝 (2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ)) : Filter ℝ) :=
                tendsto_const_nhds
              simpa using hconst.mul hUsqrt
            apply squeeze_zero'
            · filter_upwards with h
              exact integral_nonneg fun _ => abs_nonneg _
            · filter_upwards [huh] with h huh
              have hdu : MemLp (fun t => uh h t - u t) 2 μ := huh.sub hu
              have hLuh : MemLp (fun t => valueCLM hΩ (uh h t)) 2 μ :=
                huh.continuousLinearMap_comp (valueCLM hΩ)
              have hLu : MemLp (fun t => valueCLM hΩ (u t)) 2 μ :=
                hu.continuousLinearMap_comp (valueCLM hΩ)
              have hleft : Integrable (fun t =>
                  |‖valueCLM hΩ (uh h t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2|) μ := by
                simpa [Pi.sub_def] using
                  ((hLuh.integrable_norm_pow (by norm_num : 2 ≠ 0)).sub
                    (hLu.integrable_norm_pow (by norm_num : 2 ≠ 0))).norm
              have hterm1 : Integrable (fun t =>
                  C * ‖uh h t - u t‖ ^ 2) μ :=
                (hdu.integrable_norm_pow (by norm_num : 2 ≠ 0)).const_mul _
              have hterm2 : Integrable (fun t =>
                  2 * C * ‖u t‖ * ‖uh h t - u t‖) μ :=
                by
                  apply ((hu.norm).integrable_mul hdu.norm).const_mul (2 * C) |>.congr
                  filter_upwards with t
                  change 2 * C *
                    ((fun x => ‖u x‖) * fun x => ‖uh h x - u x‖) t = _
                  simp
                  ring
              have hpoint : ∀ t : ℝ,
                  |‖valueCLM hΩ (uh h t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2| ≤
                    C * ‖uh h t - u t‖ ^ 2 + 2 * C * ‖u t‖ * ‖uh h t - u t‖ := by
                intro t
                simpa only [C] using abs_sqNorm_valueCLM_sub_le hΩ (uh h t) (u t)
              have hmono := integral_mono hleft (hterm1.add hterm2) hpoint
              have hholder := integral_mul_norm_le_sqrt_mul_sqrt
                u (fun t => uh h t - u t) hu hdu
              have hterm2_eq : (∫ t,
                  2 * C * ‖u t‖ * ‖uh h t - u t‖ ∂μ) =
                  2 * C *
                    (∫ t, ‖u t‖ * ‖uh h t - u t‖ ∂μ) := by
                rw [show (fun t =>
                    2 * C * ‖u t‖ * ‖uh h t - u t‖) =
                    fun t => (2 * C) *
                      (‖u t‖ * ‖uh h t - u t‖) by
                      funext t
                      ring, integral_const_mul]
              calc
                (∫ t, |‖valueCLM hΩ (uh h t)‖ ^ 2 - ‖valueCLM hΩ (u t)‖ ^ 2| ∂μ) ≤
                    ∫ t, C * ‖uh h t - u t‖ ^ 2 +
                      2 * C * ‖u t‖ * ‖uh h t - u t‖ ∂μ := hmono
                _ = C * (∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) +
                    (∫ t, 2 * C * ‖u t‖ * ‖uh h t - u t‖ ∂μ) := by
                      rw [integral_add hterm1 hterm2, integral_const_mul]
                _ = C * (∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) +
                    2 * C *
                      (∫ t, ‖u t‖ * ‖uh h t - u t‖ ∂μ) := by
                      rw [hterm2_eq]
                _ ≤ C * (∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) +
                    2 * C * √(∫ t, ‖u t‖ ^ 2 ∂μ) *
                      √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) := by
                      apply add_le_add_right
                      simpa only [mul_assoc] using
                        mul_le_mul_of_nonneg_left hholder (by positivity : 0 ≤ 2 * C)
            · simpa using hfirst.add hsecond
          have hraw : Integrable (rawPositivePartEnergy hΩ T u) (volume.restrict (Icc a b)) := by
            rw [← Measure.restrict_restrict_of_subset hK]
            exact (integrable_rawPositivePartEnergy hΩ T u).restrict
          have hforward : ∀ᶠ h : ℝ in 𝓝[>] 0,
              Integrable (forwardSteklovPositivePartEnergy hΩ T h u)
                (volume.restrict (Icc a b)) := by
            filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
              with h hh
            exact ((valueCLM hΩ).continuous.comp ((continuous_h10PositivePart hΩ).comp
              (continuous_reverseTimeForwardSteklov T h hh u))).norm.pow 2 |>.integrableOn_Icc
          let μ : Measure ℝ := volume.restrict (Icc a b)
          let up : ℝ → H10HilbertGraph hΩ := fun t => h10PositivePart hΩ (u t)
          let uhp : ℝ → ℝ → H10HilbertGraph hΩ := fun h t =>
            h10PositivePart hΩ (reverseTimeForwardSteklov T h u t)
          have huLocal : MemLp (u : ℝ → H10HilbertGraph hΩ) 2 μ := by
            simpa only [μ] using memLp_restrict_Icc_of_subset T u hK
          have hup : MemLp up 2 μ := by
            apply MemLp.of_le huLocal
            · exact (continuous_h10PositivePart hΩ).comp_aestronglyMeasurable
                huLocal.aestronglyMeasurable
            · filter_upwards with r
              exact norm_h10PositivePart_le hΩ _
          have huh : ∀ᶠ h : ℝ in 𝓝[>] 0,
              MemLp (reverseTimeForwardSteklov T h u) 2 μ := by
            simpa only [μ] using eventually_memLp_reverseTimeForwardSteklov_on_Icc T u a b
          have huhp : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (uhp h) 2 μ := by
            filter_upwards [huh] with h hh
            apply MemLp.of_le hh
            · exact (continuous_h10PositivePart hΩ).comp_aestronglyMeasurable
                hh.aestronglyMeasurable
            · filter_upwards with r
              exact norm_h10PositivePart_le hΩ _
          have hUraw := tendsto_forwardSteklov_sqNorm_integral_on_Icc T u ha hab.le hb
          have hUpos := tendsto_positivePart_sqNorm_integral_of_sqNorm hΩ μ
            (u : ℝ → H10HilbertGraph hΩ) (fun h r => reverseTimeForwardSteklov T h u r)
            huLocal huh hUraw
          have hEabs : Tendsto (fun h => ∫ r in Icc a b,
              |‖valueCLM hΩ (uhp h r)‖ ^ 2 - ‖valueCLM hΩ (up r)‖ ^ 2|)
              (𝓝[>] 0) (𝓝 0) :=
            tendsto_integral_abs_valueSq_of_sqNorm hΩ μ up uhp hup huhp hUpos
          exact tendsto_integral_mul_of_tendsto_integral_abs hforward hraw
            eta.contDiff_deriv.continuous.aestronglyMeasurable eta.exists_norm_deriv_le hEabs
        have eventually_forwardSteklov_positivePartEnergy_test_identity {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) (eta : ReverseTimeScalarTest T) {a : ℝ} {b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < T) (heta : tsupport (eta : ℝ → ℝ) ⊆ Ioo a b) (hetaDeriv : tsupport eta.deriv ⊆ Ioo a b) :
            ∀ᶠ h : ℝ in 𝓝[>] 0,
            (∫ t, forwardSteklovPositivePartEnergy hΩ T h u t * eta.deriv t
              ∂reverseTimeVolume T) =
            -(∫ t, forwardSteklovPositivePartEnergyRate hΩ T h u g t * eta t
              ∂reverseTimeVolume T) := by
          have hK : Icc a b ⊆ Ioo 0 T := by
            intro t ht
            exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
          filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin,
            (eventually_lt_nhds (show 0 < T - b by linarith)).filter_mono nhdsWithin_le_nhds]
            with h hh hsmall
          have hE : Continuous (forwardSteklovPositivePartEnergy hΩ T h u) := by
            exact ((valueCLM hΩ).continuous.comp ((continuous_h10PositivePart hΩ).comp
              (continuous_reverseTimeForwardSteklov T h hh u))).norm.pow 2
          have hQ : Continuous (forwardSteklovPositivePartEnergyRate hΩ T h u g) := by
            exact continuous_const.mul
              ((continuous_reverseTimeForwardSteklov T h hh g).clm_apply
                ((continuous_h10PositivePart hΩ).comp
                  (continuous_reverseTimeForwardSteklov T h hh u)))
          have hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
              forwardSteklovPositivePartEnergy hΩ T h u t - forwardSteklovPositivePartEnergy hΩ T h u s =
                ∫ r in Icc s t, forwardSteklovPositivePartEnergyRate hΩ T h u g r := by
            intro s hs t ht hst
            exact forwardSteklovPositivePartEnergy_increment hΩ T hT u g hderiv hh ha hsmall
              hs ht hst
          rw [integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
            integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
          exact integral_energy_mul_deriv_eq_neg_integral_pairing_of_increment hab.le hE hQ hinc
            (eta.contDiff.of_le (by simp)) heta
        have exists_strict_test_collar :
            ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < T ∧
            tsupport (eta : ℝ → ℝ) ⊆ Ioo a b ∧ tsupport eta.deriv ⊆ Ioo a b := by
          by_cases hsupport : (tsupport (eta : ℝ → ℝ)).Nonempty
          · obtain ⟨lo, hlo, hloMin⟩ :=
              eta.hasCompactSupport.exists_isMinOn hsupport continuousOn_id
            obtain ⟨hi, hhi, hhiMax⟩ :=
              eta.hasCompactSupport.exists_isMaxOn hsupport continuousOn_id
            have hloIoo : lo ∈ Ioo 0 T := eta.tsupport_subset hlo
            have hhiIoo : hi ∈ Ioo 0 T := eta.tsupport_subset hhi
            obtain ⟨a, ha0, halo⟩ := exists_between hloIoo.1
            obtain ⟨b, hhib, hbT⟩ := exists_between hhiIoo.2
            have hlohi : lo ≤ hi := hloMin hhi
            refine ⟨a, b, ha0, ?_, hbT, ?_, ?_⟩
            · exact lt_of_lt_of_le halo (hlohi.trans_lt hhib).le
            · intro t ht
              have hlot : lo ≤ t := hloMin ht
              have hthi : t ≤ hi := hhiMax ht
              exact ⟨lt_of_lt_of_le halo hlot, lt_of_le_of_lt hthi hhib⟩
            · have hderivSupport : tsupport eta.deriv ⊆ tsupport (eta : ℝ → ℝ) := by
                rw [ReverseTimeScalarTest.deriv, tsupport]
                exact closure_minimal support_deriv_subset (isClosed_tsupport _)
              exact hderivSupport.trans (by
                intro t ht
                have hlot : lo ≤ t := hloMin ht
                have hthi : t ≤ hi := hhiMax ht
                exact ⟨lt_of_lt_of_le halo hlot, lt_of_le_of_lt hthi hhib⟩)
          · have heta : (eta : ℝ → ℝ) = 0 := by
              funext t
              apply image_eq_zero_of_notMem_tsupport
              exact fun ht => hsupport ⟨t, ht⟩
            have hderiv : eta.deriv = 0 := by
              apply funext
              intro t
              rw [eta.deriv_apply, heta]
              simp
            refine ⟨T / 3, 2 * T / 3, by linarith, by linarith, by linarith, ?_, ?_⟩
            · rw [heta]
              simp
            · rw [hderiv]
              simp
        obtain ⟨a, b, ha, hab, hb, heta, hetaDeriv⟩ := exists_strict_test_collar
        have hK : Icc a b ⊆ Ioo 0 T := by
          intro t ht
          exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
        have hforward := eventually_forwardSteklov_positivePartEnergy_test_identity
          hΩ T hT u g hderiv eta ha hab hb heta hetaDeriv
        have hEtest := tendsto_forwardSteklov_positivePartEnergy_test
          hΩ T u eta ha hab hb hK
        have hQtest := tendsto_forwardSteklov_positivePartEnergyRate_test
          hΩ T u g eta ha hab hb hK
        have hforwardIcc : ∀ᶠ h : ℝ in 𝓝[>] 0,
            (∫ t in Icc a b, forwardSteklovPositivePartEnergy hΩ T h u t * eta.deriv t) =
              -(∫ t in Icc a b,
                forwardSteklovPositivePartEnergyRate hΩ T h u g t * eta t) := by
          filter_upwards [hforward] with h hh
          rw [← integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
            ← integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
          exact hh
        have hConst : Tendsto (fun _ : ℝ => 0) (𝓝[>] 0)
            (𝓝 ((∫ t in Icc a b, rawPositivePartEnergy hΩ T u t * eta.deriv t) +
              ∫ t in Icc a b, rawPositivePartEnergyRate hΩ T u g t * eta t)) := by
          apply (hEtest.add hQtest).congr'
          filter_upwards [hforwardIcc] with h hh
          exact (eq_neg_iff_add_eq_zero).mp hh
        have hzeroIcc : (∫ t in Icc a b,
            rawPositivePartEnergy hΩ T u t * eta.deriv t) +
            ∫ t in Icc a b, rawPositivePartEnergyRate hΩ T u g t * eta t = 0 :=
          tendsto_nhds_unique hConst tendsto_const_nhds
        rw [integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
          integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
        exact (eq_neg_iff_add_eq_zero).mpr hzeroIcc
      have reverseTimePositivePartEnergyPrimitive_sub {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) {s : ℝ} {t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
          reverseTimePositivePartEnergyPrimitive hΩ T u g t -
            reverseTimePositivePartEnergyPrimitive hΩ T u g s =
          ∫ r in Ioc s t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T := by
        change (∫ r in Ioc 0 t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T) -
            ∫ r in Ioc 0 s, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T = _
        rw [← intervalIntegral.integral_of_le ht.1,
          ← intervalIntegral.integral_of_le hs.1,
          intervalIntegral.integral_interval_sub_left
            (integrable_rawPositivePartEnergyRate hΩ T u g).intervalIntegrable
            (integrable_rawPositivePartEnergyRate hΩ T u g).intervalIntegrable,
          intervalIntegral.integral_of_le hst]
      let defect : ℝ → ℝ := fun t =>
        rawPositivePartEnergy hΩ T u t - reverseTimePositivePartEnergyPrimitive hΩ T u g t
      have hdefInt : Integrable defect (reverseTimeVolume T) :=
        (integrable_rawPositivePartEnergy hΩ T u).sub
          (integrable_reverseTimePositivePartEnergyPrimitive hΩ T u g)
      have hdefZero : ∀ eta : ReverseTimeScalarTest T,
          (∫ t, defect t * eta.deriv t ∂reverseTimeVolume T) = 0 := by
        intro eta
        have hrawInt := integrable_mul_reverseTimeScalarTest_deriv
          (integrable_rawPositivePartEnergy hΩ T u) eta
        have hprimInt := integrable_mul_reverseTimeScalarTest_deriv
          (integrable_reverseTimePositivePartEnergyPrimitive hΩ T u g) eta
        rw [show (∫ t, defect t * eta.deriv t ∂reverseTimeVolume T) =
            (∫ t, rawPositivePartEnergy hΩ T u t * eta.deriv t ∂reverseTimeVolume T) -
              ∫ t, reverseTimePositivePartEnergyPrimitive hΩ T u g t * eta.deriv t
                ∂reverseTimeVolume T by
          rw [← integral_sub hrawInt hprimInt]
          apply integral_congr_ae
          filter_upwards with t
          dsimp only [defect]
          ring,
          rawPositivePartEnergy_test_deriv hΩ T hT u g hderiv eta,
          reverseTimePositivePartEnergyPrimitive_test_deriv hΩ T u g eta]
        ring
      obtain ⟨c, hc⟩ := exists_ae_eq_const_of_integral_deriv_eq_zero T hT hdefInt hdefZero
      let e : ℝ → ℝ := fun t => reverseTimePositivePartEnergyPrimitive hΩ T u g t + c
      have heCont : ContinuousOn e (Icc 0 T) :=
        (continuousOn_reverseTimePositivePartEnergyPrimitive hΩ T u g).add continuousOn_const
      have heAE : e =ᵐ[reverseTimeVolume T] rawPositivePartEnergy hΩ T u := by
        filter_upwards [hc] with t ht
        dsimp only [defect] at ht
        dsimp only [e]
        linarith
      have heNonneg : ∀ t : ℝ, t ∈ Icc 0 T → 0 ≤ e t := by
        have heIcc : e =ᵐ[volume.restrict (Icc 0 T)] rawPositivePartEnergy hΩ T u := by
          simpa only [reverseTimeVolume, reverseTimeOpenInterval,
            restrict_Ioo_eq_restrict_Icc] using heAE
        have hmaxAE : e =ᵐ[volume.restrict (Icc 0 T)] fun t => max (e t) 0 := by
          filter_upwards [heIcc] with t ht
          rw [ht]
          simp only [rawPositivePartEnergy, max_eq_left (sq_nonneg _)]
        have hmaxCont : ContinuousOn (fun t => max (e t) 0) (Icc 0 T) := by
          exact heCont.sup continuousOn_const
        have heEqOn := Measure.eqOn_Icc_of_ae_eq volume hT.ne hmaxAE heCont hmaxCont
        intro t ht
        rw [heEqOn ht]
        exact le_max_right _ _
      refine ⟨e, heCont, heNonneg, heAE, ?_⟩
      intro s t hs ht hst
      calc
        e t - e s = reverseTimePositivePartEnergyPrimitive hΩ T u g t -
            reverseTimePositivePartEnergyPrimitive hΩ T u g s := by
              dsimp only [e]
              ring
        _ = ∫ r in Ioc s t, rawPositivePartEnergyRate hΩ T u g r ∂reverseTimeVolume T :=
          reverseTimePositivePartEnergyPrimitive_sub hΩ T u g hs ht hst
    obtain ⟨e, heCont, heNonneg, heAE, heSub⟩ :=
      exists_continuous_reverseTimePositivePartEnergyRepresentative_raw hΩ T hT u g hderiv
    refine ⟨e, heCont, heNonneg, ?_, ?_⟩
    · exact heAE
    · intro s t hs ht hst
      rw [heSub s t hs ht hst]
      simp only [rawPositivePartEnergyRate, integral_const_mul]
  obtain ⟨e, heCont, _heNonneg, heAE, heInc⟩ :=
    exists_continuous_reverseTimePositivePartEnergyRepresentative hΩ T hT u g hderiv
  let Ubar := reverseTimeHilbertRepresentative hΩ T hT u g hderiv
  let E : ℝ → ℝ := fun r => if hr : r ∈ Icc 0 T then
    ‖MeasureTheory.Lp.posPart (Ubar ⟨r, hr⟩)‖ ^ 2 else 0
  have hECont : ContinuousOn E (Icc 0 T) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : (Icc 0 T).domRestrict E = fun r =>
        ‖MeasureTheory.Lp.posPart (Ubar r)‖ ^ 2 := by
      funext r
      simp only [Set.domRestrict_apply, E, dif_pos r.2]
    rw [hEq]
    exact (continuous_norm.comp
      (MeasureTheory.Lp.continuous_posPart.comp Ubar.continuous)).pow 2
  have hrep := (reverseTimeHilbertRepresentative_spec hΩ T hT u g hderiv).1
  have hAE : E =ᵐ[volume.restrict (Icc 0 T)] e := by
    have hrep' : ∀ᵐ r ∂volume.restrict (Icc 0 T),
        ∀ hr : r ∈ Ioo 0 T, Ubar ⟨r, ⟨hr.1.le, hr.2.le⟩⟩ = valueCLM hΩ (u r) := by
      simpa only [Ubar, ReverseTimeHilbertRepresentativeAgrees, reverseTimeVolume,
        reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc] using hrep
    have he' : e =ᵐ[volume.restrict (Icc 0 T)] rawPositivePartEnergy hΩ T u := by
      have heRaw : e =ᵐ[reverseTimeVolume T] rawPositivePartEnergy hΩ T u := heAE
      simpa only [reverseTimeVolume, reverseTimeOpenInterval,
        restrict_Ioo_eq_restrict_Icc] using heRaw
    have hi : ∀ᵐ r ∂volume.restrict (Icc 0 T), r ∈ Ioo 0 T := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hrep', he', hi] with r hU he hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1.le, hr.2.le⟩
    change (if h : r ∈ Icc 0 T then ‖MeasureTheory.Lp.posPart (Ubar ⟨r, h⟩)‖ ^ 2
      else 0) = e r
    rw [dif_pos hr', hU hr, ← valueCLM_h10PositivePart]
    exact he.symm
  have hEqOn : EqOn E e (Icc 0 T) :=
    Measure.eqOn_Icc_of_ae_eq volume hT.ne hAE hECont heCont
  calc
    _ = E t - E s := by
      change ‖MeasureTheory.Lp.posPart (Ubar ⟨t, ht⟩)‖ ^ 2 -
        ‖MeasureTheory.Lp.posPart (Ubar ⟨s, hs⟩)‖ ^ 2 = _
      dsimp only [E]
      rw [dif_pos ht, dif_pos hs]
    _ = e t - e s := congrArg₂ (· - ·) (hEqOn ht) (hEqOn hs)
    _ = _ := heInc s t hs ht hst

end HypoellipticAleksandrov.Parabolic.Dirichlet

