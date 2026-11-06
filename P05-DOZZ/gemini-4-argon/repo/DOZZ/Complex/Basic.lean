/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Complex.Defs
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Elementary complex analysis

The dominated-integral theorem propagates integrability from the center by the
mean value inequality on the real-convex polydisc. Meromorphic normal forms
supply gluing and the dense-period identity while retaining the punctured-germ
formulation. Quantitative real layer cake supplies the uniform-family boundary
limit, and rational residue lemmas support the Mellin transform arguments.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The finite-coordinate polydisc is open, including in dimension zero. -/
theorem isOpen_complexPolydisc {N} (a : Fin N → ℂ) R :
    IsOpen (complexPolydisc a R) := by
  rw [(show complexPolydisc a R = ⋂ i, {z : Fin N → ℂ | ‖z i - a i‖ < R i} by ext z; simp [complexPolydisc])]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt ((continuous_apply i).sub continuous_const).norm continuous_const

/-- Positive radii put the center in the polydisc. -/
theorem mem_complexPolydisc_center {N} a (R : Fin N → ℝ)
    (hR : ∀ i, 0 < R i) : a ∈ complexPolydisc a R := by
  simpa [complexPolydisc] using hR


/-- Proof of `DOZZ.differentiableOn_integral_polydisc`: dominated differentiation on a polydisc. -/
theorem differentiableOn_integral_polydisc {Ω : Type*} [MeasurableSpace Ω]
    {N} (P : Measure Ω) (a : Fin N → ℂ) (R : Fin N → ℝ)
    (hR : ∀ i, 0 < R i) (F : (Fin N → ℂ) → Ω → ℂ)
    (F' : (Fin N → ℂ) → Ω → ((Fin N → ℂ) →L[ℂ] ℂ)) (bound : Ω → ℝ)
    (hF : ∀ z ∈ complexPolydisc a R, AEStronglyMeasurable (F z) P)
    (hF' : ∀ z ∈ complexPolydisc a R, AEStronglyMeasurable (F' z) P)
    (hbase : Integrable (F a) P) (hbound : Integrable bound P)
    (hdom : ∀ᵐ ω ∂P, ∀ z ∈ complexPolydisc a R, ‖F' z ω‖ ≤ bound ω)
    (hderiv : ∀ᵐ ω ∂P, ∀ z ∈ complexPolydisc a R,
      HasFDerivAt (fun w => F w ω) (F' z ω) z) :
    DifferentiableOn ℂ (fun z => ∫ ω, F z ω ∂P) (complexPolydisc a R) ∧
      ∀ z ∈ complexPolydisc a R,
        Integrable (F z) P ∧ Integrable (F' z) P ∧
        HasFDerivAt (fun w => ∫ ω, F w ω ∂P) (∫ ω, F' z ω ∂P) z := by
  have hint : ∀ z ∈ complexPolydisc a R, Integrable (F z) P := by
    intro z hz
    have hdiff : Integrable (fun ω => F z ω - F a ω) P := by
      apply (hbound.norm.mul_const ‖z - a‖).mono' ((hF z hz).sub hbase.aestronglyMeasurable)
      filter_upwards [hdom, hderiv] with ω hb hd
      exact (Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun w hw => (hd w hw).hasFDerivWithinAt) hb
        ((by rw [(show complexPolydisc a R = Set.pi Set.univ (fun i => Metric.ball (a i) (R i)) by ext z; simp [complexPolydisc, Metric.mem_ball, dist_eq_norm])]; exact convex_pi fun i _ => convex_ball (a i) (R i))) (mem_complexPolydisc_center a R hR) hz).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
    convert hdiff.add hbase using 1
    ext ω
    exact (sub_add_cancel _ _).symm
  have hresult : ∀ z ∈ complexPolydisc a R,
      Integrable (F z) P ∧ Integrable (F' z) P ∧
      HasFDerivAt (fun w => ∫ ω, F w ω ∂P) (∫ ω, F' z ω ∂P) z := by
    intro z hz
    have hnhds := (isOpen_complexPolydisc a R).mem_nhds hz
    exact ⟨hint z hz, (by apply hbound.norm.mono' (hF' z hz); filter_upwards [hdom] with ω hb; exact (hb z hz).trans (le_abs_self _)),
      hasFDerivAt_integral_of_dominated_of_fderiv_le hnhds
        (Filter.eventually_of_mem hnhds fun w hw => hF w hw) (hint z hz) (hF' z hz) hdom hbound hderiv⟩
  exact ⟨fun z hz => (hresult z hz).2.2.differentiableAt.differentiableWithinAt, hresult⟩



/-- Proof of `DOZZ.exists_meromorphicOn_strip_gluing`: strip gluing, including uniqueness at the
level of germs. -/
theorem exists_meromorphicOn_strip_gluing {ι : Type*}
    h (hh : 0 < h) (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = horizontalStrip h) (f : ι → ℂ → ℂ)
    (hf : ∀ i, MeromorphicOn (f i) (U i))
    (hcompat : ∀ i j z, z ∈ U i → z ∈ U j → f i =ᶠ[𝓝[≠] z] f j) :
    ∃ F : ℂ → ℂ, MeromorphicOn F (horizontalStrip h) ∧
      (∀ i z, z ∈ U i → F =ᶠ[𝓝[≠] z] f i) ∧
      (∀ G : ℂ → ℂ, MeromorphicOn G (horizontalStrip h) →
        (∀ i z, z ∈ U i → G =ᶠ[𝓝[≠] z] f i) →
        ∀ z ∈ horizontalStrip h, F =ᶠ[𝓝[≠] z] G) := by
  have exists_meromorphicOn_iUnion_gluing : ∃ F : ℂ → ℂ, MeromorphicOn F (⋃ i, U i) ∧ (∀ i z, z ∈ U i → F =ᶠ[𝓝[≠] z] f i) := by
    classical
    have normalized_eq_of_compatible_germs i j z (hi : z ∈ U i) (hj : z ∈ U j) := (((meromorphicNFOn_toMeromorphicNFOn (f i) (U i) hi).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (meromorphicNFOn_toMeromorphicNFOn (f j) (U j) hj)).mp (((hf i).toMeromorphicNFOn_eq_self_on_nhdsNE hi).trans ((hcompat i j z hi hj).trans ((hf j).toMeromorphicNFOn_eq_self_on_nhdsNE hj).symm))).eq_of_nhds
    let index (z : ℂ) (hz : z ∈ ⋃ i, U i) := Classical.choose (mem_iUnion.mp hz)
    let F : ℂ → ℂ := fun z => if hz : z ∈ ⋃ i, U i then
      toMeromorphicNFOn (f (index z hz)) (U (index z hz)) z else 0
    have heq i z (hz : z ∈ U i) :
        F z = toMeromorphicNFOn (f i) (U i) z := by
      have hzu := mem_iUnion.mpr ⟨i, hz⟩
      simp only [F, dite_eq_left hzu]
      exact normalized_eq_of_compatible_germs _ i z ((fun z hz => Classical.choose_spec (mem_iUnion.mp hz)) z hzu) hz
    have hlocal i z (hz : z ∈ U i) :
        F =ᶠ[𝓝 z] toMeromorphicNFOn (f i) (U i) :=
      Filter.eventually_of_mem ((hU i).mem_nhds hz) fun w hw => heq i w hw
    have hpiece i z (hz : z ∈ U i) : F =ᶠ[𝓝[≠] z] f i :=
      ((hlocal i z hz).filter_mono nhdsWithin_le_nhds).trans
        ((hf i).toMeromorphicNFOn_eq_self_on_nhdsNE hz)
    refine ⟨F, ?_, hpiece⟩
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact (MeromorphicAt.meromorphicAt_congr (hpiece i z hi)).mpr (hf i z hi)
  obtain ⟨F, hF, hpiece⟩ := exists_meromorphicOn_iUnion_gluing
  refine ⟨F, hcover ▸ hF, hpiece, ?_⟩
  intro G _ hG z hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ hz)
  exact (hpiece i z hi).trans (hG i z hi).symm

/-- Real translations preserve the strip, in both directions. -/
@[simp] theorem add_real_mem_horizontalStrip h z (t : ℝ) :
    z + (t : ℂ) ∈ horizontalStrip h ↔ z ∈ horizontalStrip h := by
  simp [horizontalStrip]

/-- The strip is open. -/
theorem isOpen_horizontalStrip h : IsOpen (horizontalStrip h) :=
  isOpen_lt Complex.continuous_im.abs continuous_const

/-- The strip is convex over the reals. -/
theorem convex_horizontalStrip h : Convex ℝ (horizontalStrip h) := by
  rw [(show horizontalStrip h = Complex.imCLM ⁻¹' Ioo (-h) h by ext z; simp [horizontalStrip, abs_lt])]
  exact (convex_Ioo (-h) h).linear_preimage Complex.imCLM.toLinearMap



/-- The real value periods on a strip form an additive subgroup. -/
def stripPeriodSubgroup (h : ℝ) (g : ℂ → ℂ) : AddSubgroup ℝ where
  carrier := {t | ∀ z ∈ horizontalStrip h, g (z + (t : ℂ)) = g z}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb z hz
    calc
      g (z + ((a + b : ℝ) : ℂ)) = g ((z + (a : ℂ)) + (b : ℂ)) := by
        rw [Complex.ofReal_add, add_assoc]
      _ = g (z + (a : ℂ)) := hb _ ((add_real_mem_horizontalStrip h z a).mpr hz)
      _ = g z := ha z hz
  neg_mem' := by
    intro a ha z hz
    have hz' := (add_real_mem_horizontalStrip h z (-a)).mpr hz
    have heq := ha (z + ((-a : ℝ) : ℂ)) hz'
    simpa using heq.symm



/-- Proof of `DOZZ.meromorphicOn_strip_constant_of_dense_periods`: the dense-period identity, with
uniqueness of the constant germ. -/
theorem meromorphicOn_strip_constant_of_dense_periods
    h (hh : 0 < h) (f : ℂ → ℂ) (hf : MeromorphicOn f (horizontalStrip h))
    (T₁ T₂ : ℝ) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (hirr : ∀ q : ℚ, T₁ / T₂ ≠ (q : ℝ))
    (hp₁ : ∀ z ∈ horizontalStrip h,
      (fun w => f (w + (T₁ : ℂ))) =ᶠ[𝓝[≠] z] f)
    (hp₂ : ∀ z ∈ horizontalStrip h,
      (fun w => f (w + (T₂ : ℂ))) =ᶠ[𝓝[≠] z] f) :
    ∃! c : ℂ, ∀ z ∈ horizontalStrip h, f =ᶠ[𝓝[≠] z] (fun _ => c) := by
  have normalized_period_on_strip (t : ℝ) (hp : ∀ z ∈ horizontalStrip h, (fun w => f (w + (t : ℂ))) =ᶠ[𝓝[≠] z] f) : ∀ z ∈ horizontalStrip h, toMeromorphicNFOn f (horizontalStrip h) (z + (t : ℂ)) = toMeromorphicNFOn f (horizontalStrip h) z := by
    intro z hz
    let g := toMeromorphicNFOn f (horizontalStrip h)
    have hshift := (add_real_mem_horizontalStrip h z t).mpr hz
    have hn := meromorphicNFOn_toMeromorphicNFOn f (horizontalStrip h)
    exact ((((hn hshift).comp_analyticAt (g := fun w => w + (t : ℂ)) (by fun_prop)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hn hz)).mp (((hf.toMeromorphicNFOn_eq_self_on_nhdsNE hshift).comp_tendsto (by change Filter.map (Homeomorph.addRight (t : ℂ)) (𝓝[≠] z) ≤ _; rw [Homeomorph.map_punctured_nhds_eq]; exact le_rfl)).trans ((hp z hz).trans (hf.toMeromorphicNFOn_eq_self_on_nhdsNE hz).symm))).eq_of_nhds
  have locally_constant_of_dense_stripPeriods (g : ℂ → ℂ) (hg : MeromorphicNFOn g (horizontalStrip h)) (hdense : Dense (stripPeriodSubgroup h g : Set ℝ)) : ∀ z ∈ horizontalStrip h, g =ᶠ[𝓝 z] (fun _ => g z) := by
    have frequently_eq_of_dense_stripPeriods z (hz : z ∈ horizontalStrip h) : ∃ᶠ w in 𝓝[≠] z, g w = g z := by
      rw [Filter.frequently_iff]
      intro V hV
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hV
      obtain ⟨t, ht, htpos, htlt⟩ := hdense.exists_mem_open isOpen_Ioo
        (show (Ioo (0 : ℝ) ε).Nonempty from ⟨ε / 2, by constructor <;> linarith⟩)
      refine ⟨z + (t : ℂ), hball ⟨?_, ?_⟩, ht z hz⟩
      · simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
        exact htlt
      · simp only [mem_compl_iff, mem_singleton_iff, add_eq_left]
        exact_mod_cast htpos.ne'
    intro z hz
    exact ((hg hz).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      analyticAt_const.meromorphicNFAt).mp (((hg hz).meromorphicAt.frequently_eq_iff_eventuallyEq analyticAt_const.meromorphicAt).mp (frequently_eq_of_dense_stripPeriods z hz))
  have zero_mem_horizontalStrip : (0 : ℂ) ∈ horizontalStrip h := by
    simpa [horizontalStrip] using hh
  let g := toMeromorphicNFOn f (horizontalStrip h)
  have h₁ : T₁ ∈ stripPeriodSubgroup h g := normalized_period_on_strip T₁ hp₁
  have h₂ : T₂ ∈ stripPeriodSubgroup h g := normalized_period_on_strip T₂ hp₂
  have hirr' : Irrational (T₁ / T₂) := by
    rintro ⟨q, hq⟩
    exact hirr q hq.symm
  have hder : ∀ z ∈ horizontalStrip h, HasDerivAt g 0 z := fun z hz =>
    ((locally_constant_of_dense_stripPeriods g (meromorphicNFOn_toMeromorphicNFOn f (horizontalStrip h)) ((dense_addSubgroupClosure_pair_iff.mpr hirr').mono ((AddSubgroup.closure_le _).mpr (by simpa only [pair_subset_iff, SetLike.mem_coe] using And.intro h₁ h₂)))) z hz).hasDerivAt_iff.mpr (hasDerivAt_const z (g z))
  have hopen := isOpen_horizontalStrip h
  have hzero := zero_mem_horizontalStrip
  have hconstant : ∀ z ∈ horizontalStrip h, f =ᶠ[𝓝[≠] z] (fun _ => g 0) := by
    intro z hz
    exact (hf.toMeromorphicNFOn_eq_self_on_nhdsNE hz).symm.trans
      ((Filter.eventually_of_mem (hopen.mem_nhds hz) fun w hw => (fun z hz => hopen.is_const_of_deriv_eq_zero ((convex_horizontalStrip h).isPreconnected) (fun w hw => (hder w hw).differentiableAt.differentiableWithinAt) (fun w hw => (hder w hw).deriv) hz hzero) w hw).filter_mono nhdsWithin_le_nhds)
  refine ⟨g 0, hconstant, ?_⟩
  intro c hc
  obtain ⟨w, hw⟩ := ((hc 0 hzero).symm.trans (hconstant 0 hzero)).exists
  exact hw

theorem measurable_realUpperTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P) :
    Measurable (realUpperTail P Y hY) := by
  exact (show Antitone (fun t => P {ω | t < Y ω}) from
    fun _ _ hst => measure_mono fun _ hy => hst.trans_lt hy).measurable.ennreal_toReal

/-- The tail is nonnegative and at most one. -/
theorem realUpperTail_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P) t :
    0 ≤ realUpperTail P Y hY t ∧ realUpperTail P Y hY t ≤ 1 :=
  ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩

/-- Positive-order layer cake, with integrability deduced from the weighted tail.

This bridges Mathlib's nonnegative extended integral to an ordinary integral.
It requires only a.e. measurability of the random variable. Integrability is
proved before the ordinary integral is used.
-/
theorem integral_rpow_eq_tail_of_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P)
    (hpos : ∀ᵐ ω ∂P, 0 ≤ Y ω) p (hp : 0 < p)
    (htail : IntegrableOn (fun t => realUpperTail P Y hY t * t ^ (p - 1)) (Ioi 0)) :
    Integrable (fun ω => Y ω ^ p) P ∧
      (∫ ω, Y ω ^ p ∂P) = p * ∫ t in Ioi 0, realUpperTail P Y hY t * t ^ (p - 1) := by
  have hynn := hpos.mono fun ω hω => Real.rpow_nonneg hω p
  have hym := (hY.pow_const p).aestronglyMeasurable
  have htnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => realUpperTail P Y hY t * t ^ (p - 1)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg ht.le _)
  have heq : (∫⁻ t in Ioi (0 : ℝ), P {ω | t < Y ω} * ENNReal.ofReal (t ^ (p - 1))) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (realUpperTail P Y hY t * t ^ (p - 1)) := by
    apply lintegral_congr
    intro t
    unfold realUpperTail
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (measure_ne_top P _)]
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul P hpos hY hp
  rw [heq] at hlayer
  have hint : Integrable (fun ω => Y ω ^ p) P := by
    refine ⟨hym, (hasFiniteIntegral_iff_ofReal hynn).mpr ?_⟩
    rw [hlayer]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((hasFiniteIntegral_iff_ofReal htnn).mp htail.hasFiniteIntegral)
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hynn hym, hlayer, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hp.le]
  rw [← integral_eq_lintegral_of_nonneg_ae htnn htail.aestronglyMeasurable]

/-- A strict power tail gives a finite moment and a quantitative subtraction error.

The bounded-mass contribution costs at most one. The error on `(1, ∞)`
costs `C * p / (β + η - p)`. This bound is uniform in the distribution and
its tail coefficient, which is the input needed for the family bridge.
-/
theorem realMoment_tail_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P)
    (hpos : ∀ᵐ ω ∂P, 0 ≤ Y ω) (c β η C p : ℝ)
    (hp : 0 < p) (hpβ : p < β) (hη : 0 < η) (_hC : 0 ≤ C)
    (htail : ∀ t : ℝ, 1 ≤ t →
      |realUpperTail P Y hY t - c * t ^ (-β)| ≤ C * t ^ (-β - η)) :
    Integrable (fun ω => Y ω ^ p) P ∧
      |(∫ ω, Y ω ^ p ∂P) - c * p / (β - p)| ≤ 1 + C * p / (β + η - p) := by
  let T := fun t => realUpperTail P Y hY t * t ^ (p - 1)
  let E := fun t => (realUpperTail P Y hY t - c * t ^ (-β)) * t ^ (p - 1)
  let M := fun t : ℝ => c * t ^ (p - 1 - β)
  have hlowPow : IntegrableOn (fun t : ℝ => t ^ (p - 1)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith)
  have hlowDom : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1), ‖T t‖ ≤ t ^ (p - 1) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    have hb := realUpperTail_bounds P Y hY t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 (Real.rpow_nonneg ht.1.le _))]
    exact mul_le_of_le_one_left (Real.rpow_nonneg ht.1.le _) hb.2
  have hlow : IntegrableOn T (Ioc 0 1) := hlowPow.mono' ((measurable_realUpperTail P Y hY).mul (measurable_id.pow_const _)).aestronglyMeasurable.restrict hlowDom
  have hEPow := (integrableOn_Ioi_rpow_of_lt (by linarith : p - 1 - β - η < -1) zero_lt_one).const_mul C
  have hEDom : ∀ᵐ t ∂volume.restrict (Ioi (1 : ℝ)), ‖E t‖ ≤ C * t ^ (p - 1 - β - η) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 := zero_lt_one.trans ht
    calc
      ‖E t‖ = |realUpperTail P Y hY t - c * t ^ (-β)| * t ^ (p - 1) := by
        dsimp only [E]
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      _ ≤ (C * t ^ (-β - η)) * t ^ (p - 1) :=
        mul_le_mul_of_nonneg_right (htail t ht.le) (Real.rpow_nonneg ht0.le _)
      _ = C * t ^ (p - 1 - β - η) := by
        rw [mul_assoc, ← Real.rpow_add ht0]
        congr 2
        ring
  have hE : IntegrableOn E (Ioi 1) := hEPow.mono' (((measurable_realUpperTail P Y hY).sub ((measurable_id.pow_const _).const_mul c)).mul (measurable_id.pow_const _)).aestronglyMeasurable.restrict hEDom
  have hM := (integrableOn_Ioi_rpow_of_lt (by linarith : p - 1 - β < -1) zero_lt_one).const_mul c
  have hdecomp : EqOn (fun t => E t + M t) T (Ioi 1) := by
    intro t ht
    have hpow : t ^ (-β) * t ^ (p - 1) = t ^ (p - 1 - β) := by
      rw [← Real.rpow_add (zero_lt_one.trans ht)]
      congr 1
      ring
    dsimp [E, M, T]
    rw [sub_mul, mul_assoc, hpow]
    ring
  have hhigh := (hE.add hM).congr_fun hdecomp measurableSet_Ioi
  obtain ⟨hint, hmoment⟩ := integral_rpow_eq_tail_of_integrable P Y hY hpos p hp (by rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one), integrableOn_union]; exact ⟨hlow, hhigh⟩)
  have hpowHigh a (ha : a < -1) :
      (∫ t : ℝ in Ioi 1, t ^ a) = -1 / (a + 1) := by
    simpa using integral_Ioi_rpow_of_lt ha zero_lt_one
  have hMint : (∫ t in Ioi 1, M t) = c / (β - p) := by
    dsimp only [M]
    rw [integral_const_mul, hpowHigh _ (by linarith), (show p - 1 - β + 1 = -(β - p) by ring)]
    field_simp
  have hEbound : |∫ t in Ioi 1, E t| ≤ C / (β + η - p) := by
    have hb := norm_integral_le_of_norm_le hEPow hEDom
    rw [Real.norm_eq_abs, integral_const_mul, hpowHigh _ (by linarith)] at hb
    rw [(show p - 1 - β - η + 1 = -(β + η - p) by ring)] at hb
    rwa [(show C * (-1 / -(β + η - p)) = C / (β + η - p) by simp only [div_neg, neg_div, neg_neg, mul_one_div])] at hb
  have hsplit : (∫ t in Ioi 0, T t) =
      (∫ t in Ioc 0 1, T t) + (∫ t in Ioi 1, E t) + c / (β - p) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one),
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hlow hhigh]
    rw [← setIntegral_congr_fun measurableSet_Ioi hdecomp, integral_add hE hM, hMint]
    ring
  refine ⟨hint, ?_⟩
  calc
    |(∫ ω, Y ω ^ p ∂P) - c * p / (β - p)| =
        p * |(∫ t in Ioc 0 1, T t) + (∫ t in Ioi 1, E t)| := by
      rw [hmoment, hsplit, (show p * (((∫ t in Ioc 0 1, T t) + (∫ t in Ioi 1, E t)) + c / (β - p)) - c * p / (β - p) = p * ((∫ t in Ioc 0 1, T t) + (∫ t in Ioi 1, E t)) by ring), abs_mul, abs_of_pos hp]
    _ ≤ p * (|∫ t in Ioc 0 1, T t| + |∫ t in Ioi 1, E t|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hp.le
    _ ≤ p * (1 / p + C / (β + η - p)) :=
      mul_le_mul_of_nonneg_left (add_le_add (by simpa only [Real.norm_eq_abs, (show (∫ t : ℝ in Ioc 0 1, t ^ (p - 1)) = 1 / p by rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 from zero_le_one), integral_rpow (Or.inl (by linarith : -1 < p - 1))]; simp [Real.zero_rpow hp.ne', sub_add_cancel])] using norm_integral_le_of_norm_le hlowPow hlowDom) hEbound) hp.le
    _ = 1 + C * p / (β + η - p) := by
      rw [mul_add, mul_one_div_cancel hp.ne']
      ring

/-- Exact uniform-family bridge; the proof first controls real moments uniformly. -/
theorem complexMoment_uniform_tail_bridge {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℝ → Ω → ℝ)
    (c : ℝ → ℝ) (c₀ β η γ d₀ C : ℝ)
    (hβ : 0 < β) (hη : 0 < η) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hC : 0 ≤ C)
    (hY : ∀ d : ℝ, 0 < d → d < d₀ → AEMeasurable (Y d) P)
    (hpos : ∀ d : ℝ, 0 < d → d < d₀ → ∀ᵐ ω ∂P, 0 ≤ Y d ω)
    (hc : Tendsto c (𝓝[>] 0) (𝓝 c₀))
    (htail : ∀ (d : ℝ) (hd : 0 < d) (hd' : d < d₀) (t : ℝ), 1 ≤ t →
      |realUpperTail P (Y d) (hY d hd hd') t - c d * t ^ (-β)| ≤ C * t ^ (-β - η)) :
    (∀ d : ℝ, 0 < d → d < min d₀ (γ * β) →
      Integrable (fun ω => (Y d ω : ℂ) ^ ((β - d / γ : ℝ) : ℂ)) P) ∧
    Tendsto (fun d : ℝ => (d : ℂ) *
      (∫ ω, (Y d ω : ℂ) ^ ((β - d / γ : ℝ) : ℂ) ∂P))
      (𝓝[>] 0) (𝓝 ((γ * β * c₀ : ℝ) : ℂ)) := by
  let p : ℝ → ℝ := fun d => β - d / γ
  let m : ℝ → ℝ := fun d => ∫ ω, Y d ω ^ p d ∂P
  have hexp d (hd : 0 < d) (hd' : d < min d₀ (γ * β)) :
      0 < p d ∧ p d < β := by
    have : d / γ < β := (div_lt_iff₀ hγ).mpr (by simpa [mul_comm] using (lt_min_iff.mp hd').2)
    have := div_pos hd hγ
    dsimp [p]
    constructor <;> linarith
  have hmoment d (hd : 0 < d) (hd' : d < min d₀ (γ * β)) :
      Integrable (fun ω => Y d ω ^ p d) P ∧
      |m d - c d * p d / (β - p d)| ≤ 1 + C * p d / (β + η - p d) := by
    have hd₀' := (lt_min_iff.mp hd').1
    exact realMoment_tail_error P (Y d) (hY d hd hd₀') (hpos d hd hd₀')
      (c d) β η C (p d) (hexp d hd hd').1 (hexp d hd hd').2 hη hC (htail d hd hd₀')
  have hcpow (d : ℝ) (hd : 0 < d) (hd' : d < d₀) :
      (fun ω => (Y d ω : ℂ) ^ ((p d : ℝ) : ℂ)) =ᵐ[P]
        (fun ω => ((Y d ω ^ p d : ℝ) : ℂ)) :=
    (hpos d hd hd').mono fun ω hω => (Complex.ofReal_cpow hω (p d)).symm
  have hnear : ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d ∧ d < min d₀ (γ * β) := by
    filter_upwards [self_mem_nhdsWithin,
      (Filter.eventually_of_mem (Iio_mem_nhds (lt_min hd₀ (mul_pos hγ hβ))) fun d hd => hd).filter_mono nhdsWithin_le_nhds]
      with d hd hd' using ⟨hd, hd'⟩
  have herrBound : ∀ᶠ d : ℝ in 𝓝[>] 0,
      ‖d * m d - γ * p d * c d‖ ≤ d * (1 + C * β / η) := by
    filter_upwards [hnear] with d hd
    have hpd := hexp d hd.1 hd.2
    have halg : d * m d - γ * p d * c d =
        d * (m d - c d * p d / (β - p d)) := by
      dsimp only [p]
      field_simp [hd.1.ne', hγ.ne']
      ring
    rw [halg, Real.norm_eq_abs, abs_mul, abs_of_pos hd.1]
    calc
      d * |m d - c d * p d / (β - p d)| ≤
          d * (1 + C * p d / (β + η - p d)) :=
        mul_le_mul_of_nonneg_left (hmoment d hd.1 hd.2).2 hd.1.le
      _ ≤ d * (1 + C * β / η) := by
        apply mul_le_mul_of_nonneg_left _ hd.1.le
        exact add_le_add le_rfl (by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_left hpd.1.le hη (by linarith)).trans (div_le_div_of_nonneg_right hpd.2.le hη.le)) hC)
  have hdlim : Tendsto (fun d => d) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  refine ⟨?_, ?_⟩
  · intro d hd hd'
    exact (Complex.ofRealCLM.integrable_comp (hmoment d hd hd').1).congr
      (hcpow d hd (lt_min_iff.mp hd').1).symm
  · have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp (by simpa only [sub_add_cancel, zero_add] using (squeeze_zero_norm' herrBound (by simpa using hdlim.mul_const (1 + C * β / η)) : Tendsto (fun d => d * m d - γ * p d * c d) (𝓝[>] 0) (𝓝 (0 : ℝ))).add ((tendsto_const_nhds.mul (by simpa [p] using tendsto_const_nhds.sub (hdlim.div_const γ))).mul hc : Tendsto (fun d => γ * p d * c d) (𝓝[>] 0) (𝓝 (γ * β * c₀))))
    apply hcomplex.congr'
    filter_upwards [hnear] with d hd
    rw [integral_congr_ae (hcpow d hd.1 (lt_min_iff.mp hd.2).1), integral_complex_ofReal]
    exact Complex.ofReal_mul d (m d)

end DOZZ.Proofs
