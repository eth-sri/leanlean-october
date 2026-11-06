/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.CircleCovariance
public import Mathlib.Probability.Process.Kolmogorov
public import DOZZ.GFFStructure.HolderVersions
public import Mathlib.Analysis.InnerProductSpace.ProdL2
/-!
# Continuous circle-average versions

The unit-mass pinning terms cancel from circle increments. Truncated logarithmic potentials control
their variances, and Gaussian scaling gives all even moment bounds. Width-one radius strips satisfy
the dimension-three Kolmogorov condition with exponents eight and four. The literal closed
covariance is jointly continuous, including all intersecting circle branches. Its continuity follows
from the given L² field rather than from separate branchwise derivatives. Clamped strip processes
admit Hölder modifications in a three-dimensional Hilbert carrier. A countable overlapping cover and
one measurable agreement event give a jointly measurable global version retaining the given witness.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal
namespace DOZZ.Proofs

/-- The radius-truncated logarithmic potential has an explicit transport error bound. -/
theorem integral_circle_logmax_sub_le x y r s :
    (∫ z, Real.log (max (Real.exp (-s)) ‖y - z‖) ∂circleMeasure x r) -
      Real.log (Real.exp (-s)) ≤
        (‖x - y‖ + |Real.exp (-r) - Real.exp (-s)|) / Real.exp (-s) := by
  let _ := circleMeasure_isProbability x r
  let a := Real.exp (-r)
  let b := Real.exp (-s)
  let D := ‖x - y‖ + |a - b|
  have hb : 0 < b := Real.exp_pos _
  have hD : 0 ≤ D := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hlog : Continuous (fun z => Real.log (max b ‖y - z‖)) :=
    (continuous_const.max (continuous_const.sub continuous_id).norm).log
      (fun _ => ne_of_gt (hb.trans_le (le_max_left _ _)))
  have hpoint : ∀ᵐ z ∂circleMeasure x r, Real.log (max b ‖y - z‖) ≤ Real.log (b + D) := by
    filter_upwards [ae_norm_sub_center_circleMeasure x r] with z hz
    apply Real.log_le_log (hb.trans_le (le_max_left _ _))
    apply max_le (le_add_of_nonneg_right hD)
    have : ‖y - z‖ ≤ ‖x - y‖ + a := by
      calc
        ‖y - z‖ = ‖(y - x) + (x - z)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖y - x‖ + ‖x - z‖ := norm_add_le _ _
        _ = ‖x - y‖ + a := by rw [norm_sub_rev y x, norm_sub_rev x z, hz]
    have := le_abs_self (a - b)
    dsimp [D]
    linarith
  have hmean := integral_mono_ae (integrable_circleMeasure_of_circleIntegrable x r hlog.measurable hlog.continuousOn.circleIntegrable') (integrable_const (Real.log (b + D))) hpoint
  rw [integral_const, probReal_univ, one_smul] at hmean
  have hratio : Real.log (b + D) - Real.log b ≤ D / b := by
    have h := Real.log_le_sub_one_of_pos (div_pos (add_pos_of_pos_of_nonneg hb hD) hb)
    rw [Real.log_div (ne_of_gt (add_pos_of_pos_of_nonneg hb hD)) (ne_of_gt hb)] at h
    rwa [(show (b + D) / b - 1 = D / b by field_simp; ring)] at h
  exact (sub_le_sub_right hmean _).trans hratio


/-- Quantitative second moment bound for moving both the center and logarithmic radius. -/
theorem circleAverage_increment_variance_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X Xc
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) x y r s :
    variance (fun ω => Xc ω x r - Xc ω y s) P ≤ |r - s| +
      2 * (‖x - y‖ + |Real.exp (-r) - Real.exp (-s)|) / Real.exp (-s) := by
  have circleAverage_increment_variance x y r s : variance (fun ω => Xc ω x r - Xc ω y s) P = r + s + 2 * (∫ z, Real.log (max (Real.exp (-s)) ‖y - z‖) ∂circleMeasure x r) := by
    let _ := hX.1
    have hm : AEMeasurable (fun ω => Xc ω x r - Xc ω y s) P :=
      ((hc.2.1 x r).sub (hc.2.1 y s)).aemeasurable
    rw [← covariance_self hm,
      covariance_fun_sub_fun_sub (hc.2.1 x r) (hc.2.1 y s) (hc.2.1 x r) (hc.2.1 y s),
      circleAverage_covariance_self X Xc hX hc,
      circleAverage_covariance_self X Xc hX hc, covariance_comm (fun ω => Xc ω y s),
      circleAverage_covariance_integral P X Xc hX hc,
      integral_integral_gffKernel_eq_logmax, circleSelfEnergy_eq, circleSelfEnergy_eq]
    ring
  rw [circleAverage_increment_variance]
  have h := integral_circle_logmax_sub_le x y r s
  rw [Real.log_exp] at h
  have := le_abs_self (r - s)
  simp only [div_eq_mul_inv] at h ⊢
  linarith

/-- The original circle witness as an element of the given probability space's L². -/
noncomputable def circleAverageL2 {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → Distr} {Xc : Ω → ℂ → ℝ → ℝ}
    (hc : IsCircleAverage P X Xc) (p : ℂ × ℝ) : Lp ℝ 2 P :=
  (hc.2.1 p.1 p.2).toLp (fun ω => Xc ω p.1 p.2)

/-- The chosen L² representative agrees with the original coordinate almost surely. -/
theorem circleAverageL2_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → Distr} {Xc : Ω → ℂ → ℝ → ℝ}
    (hc : IsCircleAverage P X Xc) (p : ℂ × ℝ) :
    circleAverageL2 hc p =ᵐ[P] fun ω => Xc ω p.1 p.2 :=
  MemLp.coeFn_toLp _


/-- Circle averages depend continuously on center and radius in L², before construction of
an almost surely continuous sample version. -/
theorem continuous_circleAverageL2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) :
    Continuous (circleAverageL2 hc) := by
  have circleAverageL2_norm_sub_sq (p : ℂ × ℝ) (q : ℂ × ℝ) : ‖circleAverageL2 hc p - circleAverageL2 hc q‖ ^ 2 = variance (fun ω => Xc ω p.1 p.2 - Xc ω q.1 q.2) P := by
    let _ := hX.1
    let D := circleAverageL2 hc p - circleAverageL2 hc q
    have hae : D =ᵐ[P] fun ω => Xc ω p.1 p.2 - Xc ω q.1 q.2 := by
      filter_upwards [Lp.coeFn_sub (circleAverageL2 hc p) (circleAverageL2 hc q),
        circleAverageL2_ae_eq hc p, circleAverageL2_ae_eq hc q] with ω hD hp hq
      rw [hD, Pi.sub_apply, hp, hq]
    have hm : AEMeasurable (fun ω => Xc ω p.1 p.2 - Xc ω q.1 q.2) P :=
      ((hc.2.1 p.1 p.2).sub (hc.2.1 q.1 q.2)).aemeasurable
    have hcov := covariance_L2_eq D D
    rw [(show (∫ ω, D ω ∂P) = 0 by rw [integral_congr_ae hae]; rw [(integral_sub ((hc.2.1 p.1 p.2).integrable (by norm_num)) ((hc.2.1 q.1 q.2).integrable (by norm_num))), (circleAverage_isGaussianProcess P X Xc hX hc).2, (circleAverage_isGaussianProcess P X Xc hX hc).2, sub_self]), zero_mul, sub_zero, real_inner_self_eq_norm_sq] at hcov
    rw [← covariance_self hm, ← covariance_congr_ae hae hae, hcov]
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using (Real.continuous_sqrt.continuousAt.tendsto.comp (squeeze_zero (fun q : ℂ × ℝ => sq_nonneg ‖circleAverageL2 hc q - circleAverageL2 hc p‖) (fun q => by rw [circleAverageL2_norm_sub_sq]; exact circleAverage_increment_variance_le P X Xc hX hc q.1 p.1 q.2 p.2) (show Tendsto (fun q : ℂ × ℝ => |q.2 - p.2| + 2 * (‖q.1 - p.1‖ + |Real.exp (-q.2) - Real.exp (-p.2)|) / Real.exp (-p.2)) (𝓝 p) (𝓝 0) by simpa only [sub_self, norm_zero, abs_zero, zero_add, mul_zero, zero_div, add_zero] using (show Continuous (fun q : ℂ × ℝ => |q.2 - p.2| + 2 * (‖q.1 - p.1‖ + |Real.exp (-q.2) - Real.exp (-p.2)|) / Real.exp (-p.2)) by fun_prop).continuousAt.tendsto (x := p))))

/-- Coordinatewise modifications preserve the energy-limit clause of `DOZZ.IsCircleAverage` and L²
membership; the only separate requirement is its literal measurability clause. -/
theorem isCircleAverage_of_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc Y : Ω → ℂ → ℝ → ℝ)
    (hc : IsCircleAverage P X Xc)
    (hmeas : ∀ r, Measurable (fun p : Ω × ℂ => Y p.1 p.2 r))
    (heq : ∀ x r, (fun ω => Y ω x r) =ᵐ[P] (fun ω => Xc ω x r)) :
    IsCircleAverage P X Y := by
  refine ⟨hmeas, (fun x r => MemLp.ae_eq (heq x r).symm (hc.2.1 x r)), ?_⟩
  intro x r f hf
  have hn n : eLpNorm (fun ω => X ω (f n) - Y ω x r) 2 P =
      eLpNorm (fun ω => X ω (f n) - Xc ω x r) 2 P := by
    apply eLpNorm_congr_ae
    filter_upwards [heq x r] with ω hω
    rw [hω]
  simpa only [hn] using hc.2.2 x r f hf




/-- Gaussian even moments are controlled by any nonnegative variance bound. -/
theorem hasGaussianLaw_integral_abs_pow_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (U : Ω → ℝ) (hG : HasGaussianLaw U P)
    (hmean : (∫ ω, U ω ∂P) = 0) m {B}
    (hB : variance U P ≤ B) :
    (∫ ω, |U ω| ^ (2 * m) ∂P) ≤
      B ^ m * (∫ x : ℝ, |x| ^ (2 * m) ∂gaussianReal 0 1) := by
  have integral_abs_pow_gaussianReal (v : ℝ≥0) m : (∫ x : ℝ, |x| ^ (2 * m) ∂gaussianReal 0 v) = (v : ℝ) ^ m * (∫ x : ℝ, |x| ^ (2 * m) ∂gaussianReal 0 1) := by
    let a := Real.sqrt (v : ℝ)
    have ha2 := Real.sq_sqrt v.coe_nonneg
    have he : (gaussianReal 0 1).map (fun x => a * x) = gaussianReal 0 v := by
      rw [gaussianReal_map_const_mul, mul_zero, mul_one]
      congr 1
      exact NNReal.eq ha2
    rw [← he, integral_map (by fun_prop) (by fun_prop)]
    have hp x : |a * x| ^ (2 * m) = (v : ℝ) ^ m * |x| ^ (2 * m) := by
      rw [abs_mul, mul_pow, abs_of_nonneg (Real.sqrt_nonneg _), pow_mul, ha2]
    simp_rw [hp]
    exact integral_const_mul _ _
  have he : (∫ ω, |U ω| ^ (2 * m) ∂P) =
      (variance U P) ^ m * (∫ x : ℝ, |x| ^ (2 * m) ∂gaussianReal 0 1) := by
    have hi := integral_map hG.aemeasurable
      (show AEStronglyMeasurable (fun x => |x| ^ (2 * m)) (P.map U) by fun_prop)
    rw [hG.map_eq_gaussianReal, hmean, integral_abs_pow_gaussianReal,
      Real.coe_toNNReal _ (variance_nonneg _ _)] at hi
    exact hi.symm
  rw [he]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (variance_nonneg _ _) hB _)
    (integral_nonneg (fun x => pow_nonneg (abs_nonneg x) _))



/-- Every L² circle representative has zero expectation. -/
theorem circleAverageL2_integral_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (p : ℂ × ℝ) :
    (∫ ω, circleAverageL2 hc p ω ∂P) = 0 := by
  rw [integral_congr_ae (circleAverageL2_ae_eq hc p)]
  exact (circleAverage_isGaussianProcess P X Xc hX hc).2 p.1 p.2


/-- Hilbert coordinates for the three-dimensional circle parameter space. -/
abbrev CircleParameter := WithLp 2 (ℂ × ℝ)

/-- Clamp the logarithmic radius to a width-one closed strip. -/
def circleStripParameter (S : ℝ) (p : CircleParameter) :
    {p : ℂ × ℝ // p.2 ∈ Icc S (S+1)} :=
  ⟨(p.fst, max S (min p.snd (S+1))), by
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩⟩


/-- Pulling a Kolmogorov process back through a contraction preserves its constants. -/
theorem IsKolmogorovProcess.comp_one {T U Ω E : Type*} [PseudoEMetricSpace T]
    [PseudoEMetricSpace U] [PseudoEMetricSpace E] [MeasurableSpace Ω]
    {X : T → Ω → E} {P : Measure Ω} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) {f : U → T} (hf : LipschitzWith 1 f) :
    IsKolmogorovProcess (fun t => X (f t)) P p q M := by
  refine ⟨fun s t => hX.measurablePair (f s) (f t), ?_, hX.p_pos, hX.q_pos⟩
  intro s t
  apply (hX.kolmogorovCondition (f s) (f t)).trans
  exact mul_le_mul le_rfl (ENNReal.rpow_le_rpow (by simpa only [ENNReal.coe_one, one_mul] using hf s t) hX.q_pos.le) zero_le zero_le



/-- A countable overlapping open radius cover, with a quarter-unit interior margin. -/
def circleVersionStrip (k : ℤ) : Set (ℂ × ℝ) :=
  {p | (k : ℝ)/2-1/4 < p.2 ∧ p.2 < (k : ℝ)/2+3/4}




/-- Jointly continuous modification of the given witness (see [KRV, §2.1]). Continuity is not
asserted for an arbitrary original witness. -/
theorem exists_continuous_circleAverage {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X Xc
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) :
    ∃ Y : Ω → ℂ → ℝ → ℝ,
      IsCircleAverage P X Y ∧
      Measurable (fun p : Ω × (ℂ × ℝ) => Y p.1 p.2.1 p.2.2) ∧
      (∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Y ω p.1 p.2)) ∧
      (∀ x r, (fun ω => Y ω x r) =ᵐ[P] (fun ω => Xc ω x r)) := by
  have circleVersionStrip_clamp_eq {k : ℤ} {p : ℂ × ℝ} (hp : p ∈ circleVersionStrip k) : max ((k : ℝ)/2-1/4) (min p.2 (((k : ℝ)/2-1/4)+1)) = p.2 := by
    rw [min_eq_left (by change p.2 ≤ _; dsimp [circleVersionStrip] at hp; linarith [hp.2]),
      max_eq_right hp.1.le]
  have exists_mem_circleVersionStrip p : ∃ k, p ∈ circleVersionStrip k := by
    refine ⟨⌊2*p.2⌋, ?_⟩
    have := Int.floor_le (2*p.2)
    have := Int.lt_floor_add_one (2*p.2)
    change (⌊2*p.2⌋ : ℝ)/2-1/4 < p.2 ∧ p.2 < (⌊2*p.2⌋ : ℝ)/2+3/4
    constructor <;> linarith
  have isOpen_circleVersionStrip k : IsOpen (circleVersionStrip k) := by
    exact (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)
  have exists_continuous_clamped_circleAverage (S : ℝ) : ∃ Z : (ℂ × ℝ) → Ω → ℝ, (∀ p, Measurable (Z p)) ∧ (∀ ω, Continuous (fun p => Z p ω)) ∧ ∀ p, Z p =ᵐ[P] fun ω => Xc ω p.1 (max S (min p.2 (S+1))) := by
    have finrank_circleParameter : Module.finrank ℝ CircleParameter = 3 := by
      rw [(WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).finrank_eq, Module.finrank_prod]
      norm_num
    have circleStripParameter_lipschitz : LipschitzWith 1 (circleStripParameter S) := by
      intro p q
      change edist (p.fst, max S (min p.snd (S+1)))
        (q.fst, max S (min q.snd (S+1))) ≤ (1 : ℝ≥0∞) * edist p q
      simpa only [max_self, ENNReal.coe_one] using ((LipschitzWith.of_edist_le (WithLp.edist_fst_le (p := 2))).prodMk (show LipschitzWith 1 (fun p : CircleParameter => max S (min p.snd (S+1))) by simpa only [max_comm] using ((LipschitzWith.of_edist_le (WithLp.edist_snd_le (p := 2))).min_const (S+1)).max_const S)) p q
    have circleAverage_isKolmogorovProcess_on_strip : ∃ M : ℝ≥0, IsKolmogorovProcess (fun p : {p : ℂ × ℝ // p.2 ∈ Icc S (S + 1)} => fun ω => Xc ω p.val.1 p.val.2) P 8 4 M := by
      have circleAverage_increment_variance_le_dist_on_strip (p : {p : ℂ × ℝ // p.2 ∈ Icc S (S + 1)}) (q : {p : ℂ × ℝ // p.2 ∈ Icc S (S + 1)}) : variance (fun ω => Xc ω p.val.1 p.val.2 - Xc ω q.val.1 q.val.2) P ≤ (2 * (5 + 2 * Real.exp (S + 1))) * dist p q := by
        have circleAverage_increment_variance_le_on_strip x y r s S (hs : s ≤ S) (hrs : |r - s| ≤ 1) : variance (fun ω => Xc ω x r - Xc ω y s) P ≤ (5 + 2 * Real.exp S) * (‖x - y‖ + |r - s|) := by
          have exp_neg_relative_error_le : |Real.exp (-r) - Real.exp (-s)| / Real.exp (-s) ≤ 2 * |r - s| := by
            have h := Real.abs_exp_sub_one_le (x := s - r) (by simpa only [abs_sub_comm] using hrs)
            rw [← (show (Real.exp (-r) - Real.exp (-s)) / Real.exp (-s) = Real.exp (s - r) - 1 by rw [sub_div, div_self (Real.exp_ne_zero _), ← Real.exp_sub, show -r - -s = s - r by ring]), abs_div, abs_of_pos (Real.exp_pos _)] at h
            simpa only [abs_sub_comm] using h
          have h := circleAverage_increment_variance_le P X Xc hX hc x y r s
          have := exp_neg_relative_error_le
          have : ‖x - y‖ / Real.exp (-s) ≤ Real.exp S * ‖x - y‖ := by
            rw [div_eq_mul_inv, ← Real.exp_neg, neg_neg, mul_comm]
            exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hs) (norm_nonneg _)
          have hsplit : 2 * (‖x - y‖ + |Real.exp (-r) - Real.exp (-s)|) / Real.exp (-s) =
              2 * (‖x - y‖ / Real.exp (-s)) +
              2 * (|Real.exp (-r) - Real.exp (-s)| / Real.exp (-s)) := by ring
          rw [hsplit] at h
          have := norm_nonneg (x - y)
          have := abs_nonneg (r - s)
          have he := Real.exp_pos S
          nlinarith
        have hsum : ‖p.val.1 - q.val.1‖ + |p.val.2 - q.val.2| ≤ 2 * dist p q := by
          change _ ≤ 2 * max (dist p.val.1 q.val.1) (dist p.val.2 q.val.2)
          rw [dist_eq_norm, Real.dist_eq]
          have := le_max_left ‖p.val.1 - q.val.1‖ |p.val.2 - q.val.2|
          have h2 := le_max_right ‖p.val.1 - q.val.1‖ |p.val.2 - q.val.2|
          linarith
        exact (circleAverage_increment_variance_le_on_strip p.val.1 q.val.1 p.val.2 q.val.2 (S + 1) q.property.2 (by apply abs_le.mpr; constructor <;> linarith [p.property.1, p.property.2, q.property.1, q.property.2])).trans ((mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring))
      let _ := hX.1
      let C := 2 * (5 + 2 * Real.exp (S + 1))
      let A := ∫ x : ℝ, |x| ^ 8 ∂gaussianReal 0 1
      have hC : 0 ≤ C := by dsimp [C]; positivity
      have hA : 0 ≤ A := integral_nonneg (fun x => pow_nonneg (abs_nonneg x) _)
      let M : ℝ≥0 := ⟨C ^ 4 * A, mul_nonneg (pow_nonneg hC _) hA⟩
      refine ⟨M, IsKolmogorovProcess.mk_of_secondCountableTopology
        (fun p => circleAverage_measurable_eval X Xc hc p.val.1 p.val.2) ?_ (by norm_num) (by norm_num)⟩
      intro p q
      let U : Ω → ℝ := fun ω => Xc ω p.val.1 p.val.2 - Xc ω q.val.1 q.val.2
      have hG := (circleAverage_isGaussianProcess P X Xc hX hc).1.hasGaussianLaw_fun_sub
          (s := p.val) (t := q.val)
      have hmoment : (∫ ω, |U ω| ^ 8 ∂P) ≤ (C ^ 4 * A) * dist p q ^ 4 := by
        have hm := hasGaussianLaw_integral_abs_pow_le U hG (by rw [(integral_sub ((hc.2.1 p.val.1 p.val.2).integrable (by norm_num)) ((hc.2.1 q.val.1 q.val.2).integrable (by norm_num))), (circleAverage_isGaussianProcess P X Xc hX hc).2, (circleAverage_isGaussianProcess P X Xc hX hc).2, sub_self]) 4
          (circleAverage_increment_variance_le_dist_on_strip p q)
        change _ ≤ (C * dist p q) ^ 4 * A at hm
        exact hm.trans_eq (by ring)
      have hconv : (∫⁻ ω, edist (Xc ω p.val.1 p.val.2) (Xc ω q.val.1 q.val.2) ^ (8 : ℝ) ∂P) =
          ENNReal.ofReal (∫ ω, |U ω| ^ 8 ∂P) := by
        rw [(ofReal_integral_eq_lintegral_ofReal (show Integrable (fun ω => |U ω| ^ 8) P by simpa only [Real.norm_eq_abs] using (hG.memLp (p := (8 : ℝ≥0∞)) (by norm_num)).integrable_norm_pow') (Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg (U ω)) 8)))]
        apply lintegral_congr
        intro ω
        rw [edist_dist, Real.dist_eq]
        simpa only [ENNReal.rpow_ofNat, U] using (ENNReal.ofReal_pow (abs_nonneg (U ω)) 8).symm
      rw [hconv]
      have hb := ENNReal.ofReal_le_ofReal hmoment
      rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hC _) hA),
        ENNReal.ofReal_pow (dist_nonneg : 0 ≤ dist p q) 4] at hb
      change _ ≤ ENNReal.ofReal (C ^ 4 * A) * ENNReal.ofReal (dist p q) ^ 4 at hb
      rw [edist_dist, ENNReal.rpow_ofNat, ← ENNReal.ofReal_coe_nnreal (p := M)]
      exact hb
    let _ := hX.1
    obtain ⟨M, hM⟩ := circleAverage_isKolmogorovProcess_on_strip
    have hcover := isCoverWithBoundedCoveringNumber_balls CircleParameter
    rw [finrank_circleParameter] at hcover
    obtain ⟨Y, hYmeas, hYeq, hYholder⟩ := exists_modification_holder' hcover
      (DOZZ.Proofs.IsKolmogorovProcess.comp_one hM (circleStripParameter_lipschitz)).IsAEKolmogorovProcess (fun n => by finiteness) (by norm_num) (by norm_num)
    have hYcont ω : Continuous (fun p => Y p ω) := by
      apply continuous_iff_continuousAt.mpr
      intro p
      obtain ⟨U, hU, hholder⟩ := hYholder ω p
      obtain ⟨C, hC⟩ := hholder (1/16) (by norm_num) (by norm_num)
      exact (hC.continuousOn (by norm_num)).continuousAt hU
    refine ⟨fun p => Y (WithLp.toLp 2 p), fun p => hYmeas _,
      fun ω => (hYcont ω).comp (WithLp.prod_continuous_toLp 2 ℂ ℝ), ?_⟩
    intro p
    exact hYeq (WithLp.toLp 2 p)
  have continuous_circleAverage_version_spec (Y : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc) (hmeas : Measurable (fun p : Ω × (ℂ × ℝ) => Y p.1 p.2.1 p.2.2)) (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Y ω p.1 p.2)) (heq : ∀ x r, (fun ω => Y ω x r) =ᵐ[P] (fun ω => Xc ω x r)) : IsCircleAverage P X Y ∧ Measurable (fun p : Ω × (ℂ × ℝ) => Y p.1 p.2.1 p.2.2) ∧ (∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Y ω p.1 p.2)) ∧ (∀ x r, (fun ω => Y ω x r) =ᵐ[P] (fun ω => Xc ω x r)) := by
    refine ⟨isCircleAverage_of_ae_eq P X Xc Y hc ?_ heq, hmeas, hcont, heq⟩
    intro r
    exact hmeas.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  have hlocal (k : ℤ) := exists_continuous_clamped_circleAverage ((k : ℝ)/2-1/4)
  choose Z hZmeas hZcont hZeq using hlocal
  obtain ⟨Y, hYmeas, hYcont, hYeq, hYjoint⟩ :=
    exists_continuous_modification_of_open_cover P (fun p ω => Xc ω p.1 p.2)
      circleVersionStrip isOpen_circleVersionStrip exists_mem_circleVersionStrip
      Z hZmeas hZcont (fun k p hp => by simpa only [circleVersionStrip_clamp_eq hp] using hZeq k p)
  exact ⟨fun ω x r => Y (x,r) ω,
    continuous_circleAverage_version_spec (fun ω x r => Y (x,r) ω)
      hc hYjoint (ae_of_all P hYcont) (fun x r => hYeq (x,r))⟩

end DOZZ.Proofs
