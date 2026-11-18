module

public import BergmanWeakType.Boundary.Sharpness
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.Compact

@[expose] public section

noncomputable section

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

namespace BergmanWeakType

def radialComponent (w : ℂ) (θ : ℝ) : ℝ := w.re * cos θ + w.im * sin θ
def angularComponent (w : ℂ) (θ : ℝ) : ℝ := w.im * cos θ - w.re * sin θ

def polarDenominator (w : ℂ) (r θ : ℝ) : ℝ :=
  ‖w‖ ^ 2 * r ^ 2 - 2 * r * radialComponent w θ + 1

def polarKernel (q : ℝ) (w : ℂ) (r θ : ℝ) : ℝ := polarDenominator w r θ ^ q

def polarKernelR (q : ℝ) (w : ℂ) (r θ : ℝ) : ℝ :=
  2 * q * (‖w‖ ^ 2 * r - radialComponent w θ) * polarKernel (q - 1) w r θ

def polarKernelRR (q : ℝ) (w : ℂ) (r θ : ℝ) : ℝ :=
  2 * q * ‖w‖ ^ 2 * polarKernel (q - 1) w r θ +
    4 * q * (q - 1) * (‖w‖ ^ 2 * r - radialComponent w θ) ^ 2 * polarKernel (q - 2) w r θ

def polarKernelT (q : ℝ) (w : ℂ) (r θ : ℝ) : ℝ :=
  -2 * q * r * angularComponent w θ * polarKernel (q - 1) w r θ

def polarKernelTT (q : ℝ) (w : ℂ) (r θ : ℝ) : ℝ :=
  2 * q * r * radialComponent w θ * polarKernel (q - 1) w r θ +
    4 * q * (q - 1) * r ^ 2 * angularComponent w θ ^ 2 * polarKernel (q - 2) w r θ

def polarOp (k r f fr frr ftt : ℝ) : ℝ :=
  frr + (1 / r - 2 * k * r / (1 - r ^ 2)) * fr + ftt / r ^ 2 - (k ^ 2 / (1 - r ^ 2)) * f

theorem integral_polarOp {X : Type*} [MeasurableSpace X] {μ : Measure X} (k r : ℝ)
    {g₀ g₁ g₂ g₃ : X → ℝ} (h₀ : Integrable g₀ μ) (h₁ : Integrable g₁ μ)
    (h₂ : Integrable g₂ μ) (h₃ : Integrable g₃ μ) :
    (∫ x, polarOp k r (g₀ x) (g₁ x) (g₂ x) (g₃ x) ∂μ) =
      polarOp k r (∫ x, g₀ x ∂μ) (∫ x, g₁ x ∂μ) (∫ x, g₂ x ∂μ) (∫ x, g₃ x ∂μ) := by
  unfold polarOp
  let a := 1 / r - 2 * k * r / (1 - r ^ 2); let b := k ^ 2 / (1 - r ^ 2)
  have hs1 := integral_add h₂ (h₁.const_mul a)
  have hs2 := integral_add (h₂.add (h₁.const_mul a)) (h₃.div_const (r ^ 2))
  have hs3 := integral_sub ((h₂.add (h₁.const_mul a)).add (h₃.div_const (r ^ 2))) (h₀.const_mul b)
  simp only [Pi.add_apply] at hs1 hs2 hs3
  rw [show (fun x ↦ g₂ x + a * g₁ x + g₃ x / r ^ 2 - b * g₀ x) = _ from rfl, hs3, hs2, hs1,
    integral_const_mul, integral_const_mul, integral_div]

theorem polarDenominator_eq_norm_sq (w : ℂ) (r θ : ℝ) :
    polarDenominator w r θ = ‖1 - circleMap 0 r θ * star w‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.sub_im,
    Complex.one_im, Complex.mul_im, circleMap_zero_re, circleMap_zero_im, polarDenominator,
    radialComponent]
  linear_combination (w.re ^ 2 + w.im ^ 2) * r ^ 2 * (cos_sq_add_sin_sq θ).symm

theorem polarDenominator_pos {w : ℂ} {r : ℝ} (hr : r ^ 2 < 1) (hw : ‖w‖ ≤ 1) (θ : ℝ) :
    0 < polarDenominator w r θ := by
  rw [polarDenominator_eq_norm_sq]
  refine sq_pos_iff.mpr fun h ↦ kernel_denominator_ne_zero_closed_left (w := circleMap 0 r θ) hw
    (by simp [(sq_lt_one_iff_abs_lt_one r).mp hr]) ?_
  simpa [mul_comm] using congrArg star (norm_eq_zero.mp h)

theorem polarKernel_hasDerivAt_r (q : ℝ) (w : ℂ) (r θ : ℝ) (hd : 0 < polarDenominator w r θ) :
    HasDerivAt (fun u ↦ polarKernel q w u θ) (polarKernelR q w r θ) r := by
  have hd0 : HasDerivAt (fun u ↦ polarDenominator w u θ)
      (2 * (‖w‖ ^ 2 * r - radialComponent w θ)) r := by
    convert ((((hasDerivAt_id r).pow 2).const_mul (‖w‖ ^ 2)).sub
      (((hasDerivAt_id r).const_mul 2).mul_const (radialComponent w θ))).add_const 1 using 1
    · rfl
    · simp; ring
  convert hd0.rpow_const (p := q) (Or.inl hd.ne') using 1
  · rfl
  · unfold polarKernelR polarKernel; ring

theorem polarKernelR_hasDerivAt_r (q : ℝ) (w : ℂ) (r θ : ℝ) (hd : 0 < polarDenominator w r θ) :
    HasDerivAt (fun u ↦ polarKernelR q w u θ) (polarKernelRR q w r θ) r := by
  convert ((((hasDerivAt_id r).const_mul (‖w‖ ^ 2)).sub_const (radialComponent w θ)).mul
    (polarKernel_hasDerivAt_r (q - 1) w r θ hd)).const_mul (2 * q) using 1
  · funext; unfold polarKernelR; simp only [Pi.mul_apply, id_eq]; ring
  · unfold polarKernelR polarKernelRR; rw [show q - 1 - 1 = q - 2 by ring]; simp only [id_eq]; ring

theorem polarKernel_hasDerivAt_t (q : ℝ) (w : ℂ) (r θ : ℝ) (hd : 0 < polarDenominator w r θ) :
    HasDerivAt (polarKernel q w r) (polarKernelT q w r θ) θ := by
  have hr : HasDerivAt (radialComponent w) (angularComponent w θ) θ := by
    convert ((hasDerivAt_cos θ).const_mul w.re).add ((hasDerivAt_sin θ).const_mul w.im) using 1
    · rfl
    · unfold angularComponent; ring
  have hd0 : HasDerivAt (polarDenominator w r) (-2 * r * angularComponent w θ) θ := by
    convert (hr.const_mul (-2 * r)).const_add (‖w‖ ^ 2 * r ^ 2 + 1) using 1
    funext; unfold polarDenominator; ring
  convert hd0.rpow_const (p := q) (Or.inl hd.ne') using 1
  · rfl
  · unfold polarKernelT polarKernel; ring

theorem polarKernelT_hasDerivAt_t (q : ℝ) (w : ℂ) (r θ : ℝ) (hd : 0 < polarDenominator w r θ) :
    HasDerivAt (polarKernelT q w r) (polarKernelTT q w r θ) θ := by
  have ha : HasDerivAt (angularComponent w) (-radialComponent w θ) θ := by
    convert ((hasDerivAt_cos θ).const_mul w.im).sub ((hasDerivAt_sin θ).const_mul w.re) using 1
    · rfl
    · unfold radialComponent; ring
  convert (ha.mul (polarKernel_hasDerivAt_t (q - 1) w r θ hd)).const_mul (-2 * q * r) using 1
  · funext; unfold polarKernelT; simp only [Pi.mul_apply]; ring
  · unfold polarKernelT polarKernelTT; rw [show q - 1 - 1 = q - 2 by ring]; ring

theorem polarKernel_op (k : ℝ) (w : ℂ) (r θ : ℝ)
    (hd : 0 < polarDenominator w r θ) (hr : r ≠ 0) (ht : 1 - r ^ 2 ≠ 0) :
    polarOp k r (polarKernel (-k / 2) w r θ) (polarKernelR (-k / 2) w r θ)
      (polarKernelRR (-k / 2) w r θ) (polarKernelTT (-k / 2) w r θ) =
      -(k ^ 2 * (1 - ‖w‖ ^ 2)) / ((1 - r ^ 2) * polarDenominator w r θ) *
        polarKernel (-k / 2) w r θ := by
  have hp1 : polarKernel (-k / 2 - 1) w r θ =
      polarKernel (-k / 2) w r θ / polarDenominator w r θ := rpow_sub_one hd.ne' _
  have hp2 : polarKernel (-k / 2 - 2) w r θ =
      polarKernel (-k / 2) w r θ / polarDenominator w r θ ^ 2 := by
    unfold polarKernel
    rw [show -k / 2 - 2 = (-k / 2 - 1) - 1 by ring, rpow_sub_one hd.ne',
      rpow_sub_one hd.ne', div_div, sq]
  have hB : angularComponent w θ ^ 2 = ‖w‖ ^ 2 - radialComponent w θ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; unfold radialComponent angularComponent
    linear_combination (w.re ^ 2 + w.im ^ 2) * sin_sq_add_cos_sq θ
  unfold polarOp polarKernelRR polarKernelR polarKernelTT
  rw [hp1, hp2, hB]
  field_simp [hr, ht, hd.ne']
  unfold polarDenominator; ring

theorem polarKernel_eq_norm_weightedKernel (α r θ : ℝ) (w : ℂ) :
    polarKernel (-(α + 2) / 2) w r θ = ‖weightedKernel α (circleMap 0 r θ) w‖ := by
  rw [polarKernel, polarDenominator_eq_norm_sq, norm_weightedKernel,
    ← rpow_natCast_mul (norm_nonneg _) 2]
  congr 1; ring

theorem antitoneOn_Ico_of_deriv_nonpos {g g' : ℝ → ℝ} (hg : ContinuousOn g (Ico 0 1))
    (hd : ∀ u ∈ Ioo 0 1, HasDerivAt g (g' u) u) (hn : ∀ u ∈ Ioo 0 1, g' u ≤ 0) :
    AntitoneOn g (Ico 0 1) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico 0 1) hg
    (fun u hu ↦ (hd u (by simpa [interior_Ico] using hu)).hasDerivWithinAt)
    (fun u hu ↦ hn u (by simpa [interior_Ico] using hu))

theorem monotoneOn_Ico_of_deriv_nonneg {g g' : ℝ → ℝ} (hg : ContinuousOn g (Ico 0 1))
    (hd : ∀ u ∈ Ioo 0 1, HasDerivAt g (g' u) u) (hn : ∀ u ∈ Ioo 0 1, 0 ≤ g' u) :
    MonotoneOn g (Ico 0 1) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1) hg
    (fun u hu ↦ (hd u (by simpa [interior_Ico] using hu)).hasDerivWithinAt)
    (fun u hu ↦ hn u (by simpa [interior_Ico] using hu))

theorem continuousOn_radialWeight (p : ℝ) : ContinuousOn (fun u : ℝ ↦ (1 - u ^ 2) ^ p) (Ico 0 1) :=
  (continuousOn_const.sub (continuousOn_id.pow 2)).rpow_const fun u hu ↦
    Or.inl (by nlinarith [hu.1, hu.2] : 1 - u ^ 2 ≠ 0)

abbrev PolarCont (F : ℝ → ℝ → ℝ) : Prop :=
  ContinuousOn (fun p : ℝ × ℝ ↦ F p.1 p.2) (Ico 0 1 ×ˢ univ)

theorem continuous_polar_slice {H : ℝ → ℝ → ℝ} (hH : PolarCont H) {r : ℝ} (hr : r ∈ Ico 0 1) :
    Continuous (H r) :=
  continuousOn_univ.mp <| hH.comp (continuous_const.prodMk continuous_id).continuousOn
    fun θ _ ↦ ⟨hr, mem_univ θ⟩

theorem integrable_mul_of_continuousOn_compact {X : Type*} [NormedAddCommGroup X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} {K : Set X} (hK : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K)
    {f g : X → ℝ} (hf : Integrable f μ) (hg : ContinuousOn g K) :
    Integrable (fun w ↦ g w * f w) μ := by
  have hm : AEStronglyMeasurable g μ := by
    simpa only [Measure.restrict_eq_self_of_ae_mem hμ] using
      hg.aestronglyMeasurable hK.isClosed.measurableSet (μ := μ)
  obtain ⟨M, hM⟩ := hK.bddAbove_image hg.norm
  exact hf.bdd_mul hm (hμ.mono fun w hw ↦ hM (mem_image_of_mem _ hw))

theorem hasDerivAt_integral_mul_of_continuousOn_compact {X : Type*} [NormedAddCommGroup X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} {K : Set X} (hK : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K)
    {S : Set ℝ} (hS : IsCompact S) {x : ℝ} (hSx : S ∈ nhds x) {f : X → ℝ}
    (hf : Integrable f μ) {F F' : ℝ → X → ℝ}
    (hF : ContinuousOn (fun p : ℝ × X ↦ F p.1 p.2) (S ×ˢ K))
    (hF' : ContinuousOn (fun p : ℝ × X ↦ F' p.1 p.2) (S ×ˢ K))
    (hderiv : ∀ w ∈ K, ∀ u ∈ S, HasDerivAt (fun v ↦ F v w) (F' u w) u) :
    HasDerivAt (fun u ↦ ∫ w, F u w * f w ∂μ) (∫ w, F' x w * f w ∂μ) x := by
  have hx : x ∈ S := mem_of_mem_nhds hSx
  have hslice {G : ℝ → X → ℝ} (hG : ContinuousOn (fun p : ℝ × X ↦ G p.1 p.2) (S ×ˢ K))
      {u : ℝ} (hu : u ∈ S) : ContinuousOn (G u) K :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn fun w hw ↦ ⟨hu, hw⟩
  obtain ⟨M, hM⟩ := (hS.prod hK).bddAbove_image hF'.norm
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u w ↦ F u w * f w) (F' := fun u w ↦ F' u w * f w) hSx
    (mem_of_superset hSx fun u hu ↦
      (integrable_mul_of_continuousOn_compact hK hμ hf (hslice hF hu)).aestronglyMeasurable)
    (integrable_mul_of_continuousOn_compact hK hμ hf (hslice hF hx))
    (integrable_mul_of_continuousOn_compact hK hμ hf (hslice hF' hx)).aestronglyMeasurable
    (bound := fun w ↦ M * ‖f w‖)
    (hμ.mono fun w hw u hu ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hM (mem_image_of_mem (fun p : ℝ × X ↦ ‖F' p.1 p.2‖) (mk_mem_prod hu hw))) (norm_nonneg _))
    (hf.norm.const_mul M)
    (hμ.mono fun w hw u hu ↦ (hderiv w hw u hu).mul_const (f w))).2

def angularMean (F : ℝ → ℝ → ℝ) (r : ℝ) : ℝ := (2 * π)⁻¹ * ∫ θ in 0..2 * π, F r θ

theorem continuousOn_angularMean {F : ℝ → ℝ → ℝ} (hF : PolarCont F) :
    ContinuousOn (angularMean F) (Ico 0 1) := by
  have hc : Continuous (fun p : Ico (0 : ℝ) 1 × ℝ ↦ F p.1 p.2) :=
    continuousOn_univ.mp <| hF.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
      fun p _ ↦ ⟨p.1.2, mem_univ _⟩
  rw [continuousOn_iff_continuous_domRestrict]
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    hc 0 (2 * π)).const_mul _

theorem hasDerivAt_angularMean {F Fr : ℝ → ℝ → ℝ} {r : ℝ} (hr : r ∈ Ioo 0 1)
    (hF : PolarCont F) (hFr : PolarCont Fr)
    (hd : ∀ r ∈ Ioo 0 1, ∀ θ, HasDerivAt (fun r ↦ F r θ) (Fr r θ) r) :
    HasDerivAt (angularMean F) (angularMean Fr r) r := by
  let S := Icc (r / 2) ((r + 1) / 2)
  have hsub : S ×ˢ Icc 0 (2 * π) ⊆ Ico 0 1 ×ˢ univ :=
    fun ⟨u, _⟩ ⟨hu, _⟩ ↦ ⟨⟨by dsimp [S] at hu; linarith [hu.1, hr.1],
      by dsimp [S] at hu; linarith [hu.2, hr.2]⟩, mem_univ _⟩
  have hi := hasDerivAt_integral_mul_of_continuousOn_compact
    (μ := volume.restrict (Icc (0 : ℝ) (2 * π))) isCompact_Icc
    (ae_restrict_mem measurableSet_Icc) (show IsCompact S from isCompact_Icc)
    (x := r) (Icc_mem_nhds (by linarith [hr.1]) (by linarith [hr.2]))
    (integrable_const (1 : ℝ)) (hF.mono hsub) (hFr.mono hsub)
    fun θ _ u hu ↦ hd u ⟨by dsimp [S] at hu; linarith [hu.1, hr.1],
      by dsimp [S] at hu; linarith [hu.2, hr.2]⟩ θ
  unfold angularMean
  simpa only [mul_one, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le two_pi_pos.le] using hi.const_mul ((2 * π)⁻¹)

abbrev SrcCont (H : ℂ → ℝ → ℝ → ℝ) : Prop :=
  ContinuousOn (fun p : (ℝ × ℝ) × ℂ ↦ H p.2 p.1.1 p.1.2)
    {p | p.1.1 ^ 2 < 1 ∧ p.2 ∈ Metric.closedBall 0 1}

theorem continuousOn_at_one {H : ℂ → ℝ → ℝ → ℝ} (hH : SrcCont H) : PolarCont (H 1) :=
  hH.comp (continuous_id.prodMk continuous_const).continuousOn
    fun p hp ↦ ⟨by dsimp; nlinarith [hp.1.1, hp.1.2], by simp⟩

theorem continuousOn_polarKernel_source (q : ℝ) : SrcCont (polarKernel q) :=
  ((Continuous.continuousOn (by unfold polarDenominator radialComponent; fun_prop)).rpow_const
    fun p hp ↦ Or.inl (polarDenominator_pos hp.1 (by simpa using hp.2) p.1.2).ne')

theorem continuousOn_polarKernelR_source (q : ℝ) : SrcCont (polarKernelR q) := by
  unfold SrcCont polarKernelR
  exact (Continuous.continuousOn (by unfold radialComponent; fun_prop)).mul
    (continuousOn_polarKernel_source (q - 1))

theorem continuousOn_polarKernelRR_source (q : ℝ) : SrcCont (polarKernelRR q) := by
  unfold SrcCont polarKernelRR
  exact ((Continuous.continuousOn (by fun_prop)).mul (continuousOn_polarKernel_source (q - 1))).add
    ((Continuous.continuousOn (by unfold radialComponent; fun_prop)).mul
      (continuousOn_polarKernel_source (q - 2)))

theorem continuousOn_polarKernelTT_source (q : ℝ) : SrcCont (polarKernelTT q) := by
  unfold SrcCont polarKernelTT
  exact ((Continuous.continuousOn (by unfold radialComponent; fun_prop)).mul
    (continuousOn_polarKernel_source (q - 1))).add
    ((Continuous.continuousOn (by unfold angularComponent; fun_prop)).mul
      (continuousOn_polarKernel_source (q - 2)))

def normalizer (α r : ℝ) : ℝ :=
  circleAverage (fun ζ : ℂ ↦ ‖1 - (r : ℂ) * ζ‖ ^ (-(α + 2))) 0 1

@[simp] theorem normalizer_zero (α : ℝ) : normalizer α 0 = 1 := by
  simp [normalizer, circleAverage_const]

theorem normalizer_nonneg (α r : ℝ) : 0 ≤ normalizer α r :=
  circleAverage_nonneg_of_nonneg fun _ _ ↦ rpow_nonneg (norm_nonneg _) _

theorem normalizer_eq_angularMean (α r : ℝ) :
    normalizer α r = angularMean (polarKernel (-(α + 2) / 2) 1) r := by
  simp only [normalizer, circleAverage_def, angularMean, smul_eq_mul,
    polarKernel_eq_norm_weightedKernel, norm_weightedKernel]
  congr 1; refine intervalIntegral.integral_congr fun θ _ ↦ ?_
  simp [circleMap]

theorem continuousOn_normalizer (α : ℝ) : ContinuousOn (normalizer α) (Ico 0 1) := by
  change ContinuousOn (fun r ↦ normalizer α r) (Ico 0 1)
  simp_rw [normalizer_eq_angularMean]
  exact continuousOn_angularMean (continuousOn_at_one (continuousOn_polarKernel_source _))

def normalizerFirst (α : ℝ) : ℝ → ℝ := angularMean (polarKernelR (-(α + 2) / 2) 1)
def normalizerSecond (α : ℝ) : ℝ → ℝ := angularMean (polarKernelRR (-(α + 2) / 2) 1)

theorem normalizer_c2 (α : ℝ) :
    ContinuousOn (normalizerFirst α) (Ico 0 1) ∧
    ContinuousOn (normalizerSecond α) (Ico 0 1) ∧
    (∀ r ∈ Ioo 0 1, HasDerivAt (normalizer α) (normalizerFirst α r) r) ∧
    (∀ r ∈ Ioo 0 1, HasDerivAt (normalizerFirst α) (normalizerSecond α r) r) ∧
    (∀ r ∈ Ioo 0 1, polarOp (α + 2) r (normalizer α r)
      (normalizerFirst α r) (normalizerSecond α r) 0 = 0) := by
  let q := -(α + 2) / 2
  have hc0 := continuousOn_at_one (continuousOn_polarKernel_source q)
  have hc1 := continuousOn_at_one (continuousOn_polarKernelR_source q)
  have hc2 := continuousOn_at_one (continuousOn_polarKernelRR_source q)
  have hd (s : ℝ) (hs : s ∈ Ioo 0 1) (θ : ℝ) : 0 < polarDenominator 1 s θ :=
    polarDenominator_pos (by nlinarith [hs.1, hs.2]) (by simp) θ
  refine ⟨continuousOn_angularMean hc1, continuousOn_angularMean hc2,
    fun r hr ↦ by
      rw [funext (normalizer_eq_angularMean α)]
      exact hasDerivAt_angularMean hr hc0 hc1 fun s hs θ ↦ polarKernel_hasDerivAt_r q 1 s θ (hd s hs θ),
    fun r hr ↦ hasDerivAt_angularMean hr hc1 hc2 fun s hs θ ↦
      polarKernelR_hasDerivAt_r q 1 s θ (hd s hs θ),
    fun r hr ↦ ?_⟩
  have hrc : r ∈ Ico 0 1 := ⟨hr.1.le, hr.2⟩
  have hi {H : ℝ → ℝ → ℝ} (hH : PolarCont H) : IntegrableOn (H r) (Ioc 0 (2 * π)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).mp
      ((continuous_polar_slice hH hrc).intervalIntegrable _ _)
  have hz : (∫ θ in Ioc 0 (2 * π), polarKernelTT q 1 r θ) = 0 := by
    rw [← intervalIntegral.integral_of_le two_pi_pos.le,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun θ _ ↦ polarKernelT_hasDerivAt_t q 1 r θ (hd r hr θ))
        ((continuous_polar_slice (continuousOn_at_one (continuousOn_polarKernelTT_source q)) hrc).intervalIntegrable _ _)]
    simp [polarKernelT, polarKernel, polarDenominator, radialComponent, angularComponent]
  have hop (θ : ℝ) : polarOp (α + 2) r (polarKernel q 1 r θ) (polarKernelR q 1 r θ)
      (polarKernelRR q 1 r θ) (polarKernelTT q 1 r θ) = 0 := by
    simpa [q] using polarKernel_op (α + 2) 1 r θ (hd r hr θ) hr.1.ne' (by nlinarith [hr.1, hr.2])
  have hint := integral_polarOp (μ := volume.restrict (Ioc 0 (2 * π))) (α + 2) r
    (hi hc0) (hi hc1) (hi hc2) (hi (continuousOn_at_one (continuousOn_polarKernelTT_source q)))
  simp only [hop, integral_zero, hz] at hint
  rw [normalizer_eq_angularMean]
  unfold normalizerFirst normalizerSecond angularMean polarOp at *
  simp only [intervalIntegral.integral_of_le two_pi_pos.le, q] at hint ⊢
  linear_combination -(2 * π)⁻¹ * hint

theorem normalizer_mono (α : ℝ) {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R) (hR : R < 1) : normalizer α r ≤ normalizer α R := by
  obtain ⟨hJr, _, hJd, hJrd, hJode⟩ := normalizer_c2 α
  let k := α + 2
  let Φ (u : ℝ) := u * (1 - u ^ 2) ^ k * normalizerFirst α u
  have hΦ : MonotoneOn Φ (Ico 0 1) :=
    monotoneOn_Ico_of_deriv_nonneg
      ((continuousOn_id.mul (continuousOn_radialWeight k)).mul hJr)
      (fun u hu ↦ by
        have ht : 0 < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
        convert (((hasDerivAt_id u).mul (hasDerivAt_radialWeight k hu)).mul (hJrd u hu)) using 1
        · rfl
        · trans k ^ 2 * u * (1 - u ^ 2) ^ (k - 1) * normalizer α u +
              u * (1 - u ^ 2) ^ k * polarOp k u (normalizer α u)
                (normalizerFirst α u) (normalizerSecond α u) 0
          · rw [hJode u hu, mul_zero, add_zero]
          · simp only [polarOp, Pi.mul_apply, id_eq, k]
            rw [rpow_sub_one ht.ne']; field_simp [hu.1.ne', ht.ne']; ring)
      (fun u hu ↦ mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg k) hu.1.le)
        (rpow_nonneg (by nlinarith [hu.1, hu.2]) _)) (normalizer_nonneg α u))
  exact monotoneOn_Ico_of_deriv_nonneg (continuousOn_normalizer α) hJd
    (fun u hu ↦ by
      have hle := hΦ ⟨le_rfl, zero_lt_one⟩ ⟨hu.1.le, hu.2⟩ hu.1.le
      dsimp [Φ] at hle; rw [zero_mul, zero_mul] at hle
      exact nonneg_of_mul_nonneg_right hle
        (mul_pos hu.1 (rpow_pos_of_pos (by nlinarith [hu.1, hu.2]) _)))
    ⟨hr, hrR.trans_lt hR⟩ ⟨hr.trans hrR, hR⟩ hrR

theorem normalizer_pos (α : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : 0 < normalizer α r :=
  zero_lt_one.trans_le (normalizer_zero α ▸ normalizer_mono α le_rfl hr0 hr1)

theorem eq_on_Ico_of_hasDerivAt_zero {G : ℝ → ℝ} (hGc : ContinuousOn G (Ico 0 1))
    (hGd : ∀ r ∈ Ioo 0 1, HasDerivAt G 0 r) {r : ℝ} (hr : r ∈ Ico 0 1) :
    G r = G 0 :=
  le_antisymm
    (antitoneOn_Ico_of_deriv_nonpos hGc hGd (fun _ _ ↦ le_rfl) ⟨le_rfl, zero_lt_one⟩ hr hr.1)
    (monotoneOn_Ico_of_deriv_nonneg hGc hGd (fun _ _ ↦ le_rfl) ⟨le_rfl, zero_lt_one⟩ hr hr.1)

theorem radialMass_mul_normalizer (α : ℝ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (1 - r ^ 2) ^ (α + 1) * normalizer α r = normalizer (-α - 2) r := by
  obtain ⟨hJr, _, hJd, hJrd, hJode⟩ := normalizer_c2 α
  obtain ⟨hBr, _, hBd, hBrd, hBode⟩ := normalizer_c2 (-α - 2)
  let B := normalizer (-α - 2)
  let W (u : ℝ) := u * (((1 - u ^ 2) * normalizerFirst α u - 2 * (α + 1) * u * normalizer α u) * B u -
    (1 - u ^ 2) * normalizer α u * normalizerFirst (-α - 2) u)
  have hWc : ContinuousOn W (Ico 0 1) :=
    continuousOn_id.mul (((((continuousOn_const.sub (continuousOn_id.pow 2)).mul hJr).sub
      ((continuousOn_id.const_mul (2 * (α + 1))).mul (continuousOn_normalizer α))).mul
      (continuousOn_normalizer (-α - 2))).sub
      (((continuousOn_const.sub (continuousOn_id.pow 2)).mul (continuousOn_normalizer α)).mul hBr))
  have hW0 : ∀ u ∈ Ico 0 1, W u = 0 := fun u hu ↦ by
    simpa [W] using eq_on_Ico_of_hasDerivAt_zero hWc (fun s hs ↦ by
      have hd1 := ((hasDerivAt_id s).pow 2).const_sub 1
      convert (hasDerivAt_id s).mul
        ((((hd1.mul (hJrd s hs)).sub (((hasDerivAt_id s).const_mul (2 * (α + 1))).mul (hJd s hs))).mul
          (hBd s hs)).sub ((hd1.mul (hJd s hs)).mul (hBrd s hs))) using 1
      · rfl
      · trans s * (1 - s ^ 2) * B s * polarOp (α + 2) s (normalizer α s)
              (normalizerFirst α s) (normalizerSecond α s) 0 -
            s * (1 - s ^ 2) * normalizer α s * polarOp (-α - 2 + 2) s (B s)
              (normalizerFirst (-α - 2) s) (normalizerSecond (-α - 2) s) 0
        · rw [hJode s hs, hBode s hs]; ring
        · simp only [polarOp, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, id_eq, B]
          field_simp [hs.1.ne', show 1 - s ^ 2 ≠ 0 by nlinarith [hs.1, hs.2]]; ring) hu
  have hBpos {u : ℝ} (hu : u ∈ Ico 0 1) : 0 < B u := normalizer_pos _ hu.1 hu.2
  have hQc := ((continuousOn_radialWeight (α + 1)).mul (continuousOn_normalizer α)).div
    (continuousOn_normalizer (-α - 2)) fun u hu ↦ (hBpos hu).ne'
  have hQ1 := eq_on_Ico_of_hasDerivAt_zero hQc (fun s hs ↦ by
    have ht : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
    have hBs := (hBpos ⟨hs.1.le, hs.2⟩).ne'
    have hWs := hW0 s ⟨hs.1.le, hs.2⟩
    convert ((hasDerivAt_radialWeight (α + 1) hs).mul (hJd s hs)).div (hBd s hs) hBs using 1
    simp only [Pi.mul_apply, add_sub_cancel_right]
    rw [rpow_add_one ht.ne' α, eq_comm, div_eq_zero_iff]
    left; apply mul_left_cancel₀ hs.1.ne'
    rw [mul_zero]; dsimp only [W, B] at hWs
    linear_combination (1 - s ^ 2) ^ α * hWs) ⟨hr, hr1⟩
  simp only [Pi.div_apply, Pi.mul_apply, zero_pow two_ne_zero, sub_zero, one_rpow, one_mul,
    normalizer_zero, div_one] at hQ1
  exact (div_eq_one_iff_eq (hBpos ⟨hr, hr1⟩).ne').mp hQ1

theorem tendsto_normalizer_neg {α : ℝ} (hα : -1 < α) :
    Tendsto (normalizer (-α - 2)) (𝓝[<] 1) (𝓝 (gammaConstant α)) := by
  have hrep (r : ℝ) : normalizer (-α - 2) r =
      π⁻¹ * ∫ x in 0..π, ((1 - r) ^ 2 + 4 * r * sin x ^ 2) ^ (α / 2) := by
    rw [normalizer_eq_angularMean, angularMean, show -(-α - 2 + 2) / 2 = α / 2 by ring]
    have hd (θ : ℝ) : polarDenominator 1 r θ = (1 - r) ^ 2 + 4 * r * sin (θ / 2) ^ 2 := by
      have h1 := cos_two_mul (θ / 2); rw [show 2 * (θ / 2) = θ by ring] at h1
      simp only [polarDenominator, radialComponent, norm_one, one_pow, one_mul,
        Complex.one_re, Complex.one_im, zero_mul, add_zero]
      linear_combination -2 * r * h1 - 4 * r * sin_sq_add_cos_sq (θ / 2)
    simp_rw [polarKernel, hd]
    rw [intervalIntegral.integral_comp_div
      (fun x ↦ ((1 - r) ^ 2 + 4 * r * sin x ^ 2) ^ (α / 2)) two_ne_zero]
    simp only [zero_div, mul_div_cancel_left₀ π two_ne_zero, smul_eq_mul]; ring
  have hsi : IntervalIntegrable (fun x ↦ sin x ^ α) volume 0 π := by
    by_contra hn
    have h := two_rpow_mul_integral_sin_rpow hα
    rw [intervalIntegral.integral_undef hn, mul_zero] at h
    exact (mul_pos pi_pos (gammaConstant_pos hα)).ne' h.symm
  have hb : ∀ᶠ r : ℝ in 𝓝[<] 1, r ∈ Ioo (1 / 2) 1 := Ioo_mem_nhdsLT (by norm_num)
  have hae : ∀ᵐ x : ℝ, x ∈ uIoc 0 π → 0 < sin x := by
    filter_upwards [show ∀ᵐ x : ℝ, x ≠ π by rw [ae_iff]; simp] with x hx hmem
    rw [uIoc_of_le pi_pos.le] at hmem
    exact sin_pos_of_pos_of_lt_pi hmem.1 (lt_of_le_of_ne hmem.2 hx)
  have hlim : Tendsto (fun r : ℝ ↦ ∫ x in 0..π, ((1 - r) ^ 2 + 4 * r * sin x ^ 2) ^ (α / 2))
      (𝓝[<] 1) (𝓝 (∫ x in 0..π, (2 : ℝ) ^ α * sin x ^ α)) :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun x ↦ 4 ^ (α / 2) + sin x ^ α)
      (hb.mono fun r hr ↦ (Continuous.rpow_const (by fun_prop) fun x ↦ Or.inl
        (add_pos_of_pos_of_nonneg (sq_pos_of_pos (sub_pos.mpr hr.2))
          (mul_nonneg (by linarith [hr.1]) (sq_nonneg _))).ne').aestronglyMeasurable)
      (hb.mono fun r hr ↦ hae.mono fun x hx hmem ↦ by
        have hs := hx hmem
        let d := (1 - r) ^ 2 + 4 * r * sin x ^ 2
        have hd_pos : 0 < d := by dsimp [d]; nlinarith [hr.1, sq_nonneg (1 - r), sq_pos_of_pos hs]
        rw [Real.norm_of_nonneg (rpow_nonneg hd_pos.le _)]
        rcases le_or_gt 0 α with hα0 | hα0
        · have hs2 : sin x ^ 2 ≤ 1 := by nlinarith [sin_le_one x, hs]
          exact (rpow_le_rpow hd_pos.le (by nlinarith [hr.1, hr.2, hs2]) (by linarith)).trans
            (le_add_of_nonneg_right (rpow_nonneg hs.le _))
        · have h1 := rpow_le_rpow_of_nonpos (sq_pos_of_pos hs)
            (show sin x ^ 2 ≤ d by dsimp [d]; nlinarith [hr.1, sq_nonneg (1 - r), sq_nonneg (sin x)])
            (by linarith : α / 2 ≤ 0)
          rw [← rpow_natCast (sin x) 2, ← rpow_mul hs.le,
            show ((2 : ℕ) : ℝ) * (α / 2) = α by ring] at h1
          exact h1.trans (le_add_of_nonneg_left (by positivity)))
      (intervalIntegrable_const.add hsi)
      (hae.mono fun x hx hmem ↦ by
        have hs := hx hmem
        have heq : ((1 - (1 : ℝ)) ^ 2 + 4 * 1 * sin x ^ 2) ^ (α / 2) = (2 : ℝ) ^ α * sin x ^ α := by
          rw [show (1 - (1 : ℝ)) ^ 2 + 4 * 1 * sin x ^ 2 = (2 * sin x) ^ 2 by ring,
            ← rpow_natCast (2 * sin x) 2, ← rpow_mul (by positivity),
            show ((2 : ℕ) : ℝ) * (α / 2) = α by ring, mul_rpow zero_le_two hs.le]
        exact heq ▸ (((by fun_prop : Continuous fun r : ℝ ↦ (1 - r) ^ 2 + 4 * r * sin x ^ 2).continuousAt
          (x := 1)).rpow_const (Or.inl (by positivity))).tendsto.mono_left nhdsWithin_le_nhds)
  have h := hlim.const_mul π⁻¹
  rw [intervalIntegral.integral_const_mul, two_rpow_mul_integral_sin_rpow hα,
    inv_mul_cancel_left₀ pi_pos.ne'] at h
  simpa only [funext hrep] using h

theorem isWeakTypeBound_weightedPositiveProjection {α : ℝ} (hα : -1 < α) :
    IsWeakTypeBound (weightedArea α) (weightedPositiveProjection α)
      (ENNReal.ofReal (gammaConstant α)) := by
  let := weightedArea_isProbabilityMeasure α hα
  have hD := gammaConstant_pos hα
  have hp : 0 < α + 1 := by linarith
  intro f hf t ht
  let μ := weightedArea α
  let WP (z : ℂ) : ℝ := ∫ w, ‖weightedKernel α z w‖ * ‖f w‖ ∂μ
  let U (z : ℂ) : ℝ := WP z / normalizer α ‖z‖
  have hmf := hf.norm.aestronglyMeasurable
  have hWP_meas : Measurable WP := by
    have heq : WP = fun z ↦
        ∫ w, ‖1 - z * star w‖ ^ (-(α + 2)) * hmf.mk (fun w ↦ ‖f w‖) w ∂μ := by
      ext z; simp_rw [WP, norm_weightedKernel]
      exact integral_congr_ae (hmf.ae_eq_mk.mono fun _ hw ↦ congrArg _ hw)
    rw [heq]
    exact ((((Continuous.measurable
      (by fun_prop : Continuous fun p : ℂ × ℂ ↦ ‖1 - p.1 * star p.2‖)).pow_const _).mul
      (hmf.stronglyMeasurable_mk.measurable.comp measurable_snd)).stronglyMeasurable.integral_prod_right'
      (ν := μ)).measurable
  have hU : Measurable U := hWP_meas.div <| by
    unfold normalizer
    simp only [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le two_pi_pos.le]
    exact (measurable_const.mul ((((Continuous.measurable
      (by fun_prop : Continuous fun p : ℝ × ℝ ↦ ‖1 - (p.1 : ℂ) * circleMap 0 1 p.2‖)).pow_const _).stronglyMeasurable).integral_prod_right'
      (ν := volume.restrict (Ioc 0 (2 * π)))).measurable).comp measurable_norm
  have hanti (c : ℝ) : AntitoneOn (fun r ↦ circleAverage (fun z ↦ min (U z) c) 0 r) (Ico 0 1) := by
    let k := α + 2
    let q := -k / 2
    let P (H : ℂ → ℝ → ℝ → ℝ) (r θ : ℝ) : ℝ := ∫ w, H w r θ * ‖f w‖ ∂μ
    refine AntitoneOn.congr (f₁ := angularMean fun r θ ↦
      min (P (polarKernel q) r θ / normalizer α r) c) ?_
      fun u hu ↦ by
        rw [Real.circleAverage_def, angularMean]
        simp only [U, WP, P, norm_circleMap_zero, abs_of_nonneg hu.1, q, k,
          polarKernel_eq_norm_weightedKernel, smul_eq_mul]
    have hμ : ∀ᵐ w ∂μ, w ∈ Metric.closedBall 0 1 :=
      (ae_mem_disk_weightedArea α).mono fun _ hw ↦ Metric.ball_subset_closedBall hw
    have hfn := hf.norm
    have hJ := continuousOn_normalizer α
    have hJpos (r : ℝ) (hr : r ∈ Ico 0 1) : 0 < normalizer α r := normalizer_pos α hr.1 hr.2
    obtain ⟨hJr, hJrr, hJd, hJrd, hJode⟩ := normalizer_c2 α
    have hc_unit {H : ℂ → ℝ → ℝ → ℝ} (hH : SrcCont H) : PolarCont (P H) := by
      refine ContinuousOn.mono (s := {p : ℝ × ℝ | p.1 ^ 2 < 1}) (fun p hp ↦ ?_)
        fun ⟨r, _⟩ ⟨hr, _⟩ ↦ (by nlinarith [hr.1, hr.2] : r ^ 2 < 1)
      obtain ⟨S, hS, hpS, hsub⟩ := exists_compact_subset
        (isOpen_lt (continuous_fst.pow 2) continuous_const) hp
      have hHS : ContinuousOn (fun q : (ℝ × ℝ) × ℂ ↦ H q.2 q.1.1 q.1.2)
          (S ×ˢ Metric.closedBall 0 1) := hH.mono fun q hq ↦ ⟨hsub hq.1, hq.2⟩
      obtain ⟨M, hM⟩ := (hS.prod (isCompact_closedBall 0 1)).bddAbove_image hHS.norm
      refine ((continuousOn_of_dominated (bound := fun w ↦ M * ‖f w‖)
        (fun z hz ↦ (integrable_mul_of_continuousOn_compact (isCompact_closedBall 0 1) hμ hfn
          (hHS.comp (continuous_const.prodMk continuous_id).continuousOn
            fun w hw ↦ ⟨hz, hw⟩)).aestronglyMeasurable)
        (fun z hz ↦ hμ.mono fun w hw ↦ ?_) (hfn.const_mul M)
        (hμ.mono fun w hw ↦ (hHS.comp (continuous_id.prodMk continuous_const).continuousOn
          fun z hz ↦ ⟨hz, hw⟩).mul_const _)).continuousAt
        (mem_interior_iff_mem_nhds.mp hpS)).continuousWithinAt
      rw [norm_mul, norm_norm]
      exact mul_le_mul_of_nonneg_right
        (hM (mem_image_of_mem (fun q : (ℝ × ℝ) × ℂ ↦ ‖H q.2 q.1.1 q.1.2‖) (mk_mem_prod hz hw)))
        (norm_nonneg _)
    have hd_curve {H H' : ℂ → ℝ → ℝ → ℝ} (hH : SrcCont H) (hH' : SrcCont H')
        {γ : ℝ → ℝ × ℝ} (hγ : Continuous γ) (x : ℝ) (hx : (γ x).1 ∈ Ioo 0 1)
        (hd : ∀ w u, 0 < polarDenominator w (γ u).1 (γ u).2 →
          HasDerivAt (fun v ↦ H w (γ v).1 (γ v).2) (H' w (γ u).1 (γ u).2) u) :
        HasDerivAt (fun u ↦ P H (γ u).1 (γ u).2) (P H' (γ x).1 (γ x).2) x := by
      obtain ⟨l, s, _, hSx, htarget⟩ := exists_Icc_mem_subset_of_mem_nhds
        (((continuous_fst.comp hγ).pow 2).continuousAt.eventually
          (gt_mem_nhds (by nlinarith [hx.1, hx.2] : (γ x).1 ^ 2 < 1)))
      have hmap : MapsTo (fun p : ℝ × ℂ ↦ (γ p.1, p.2))
          (Icc l s ×ˢ Metric.closedBall 0 1) {p | p.1.1 ^ 2 < 1 ∧ p.2 ∈ Metric.closedBall 0 1} :=
        fun _ hp ↦ ⟨htarget hp.1, hp.2⟩
      have hc : Continuous (fun p : ℝ × ℂ ↦ (γ p.1, p.2)) := (hγ.comp continuous_fst).prodMk continuous_snd
      exact hasDerivAt_integral_mul_of_continuousOn_compact (isCompact_closedBall 0 1) hμ
        isCompact_Icc hSx hfn (hH.comp hc.continuousOn hmap) (hH'.comp hc.continuousOn hmap)
        fun w hw u hu ↦ hd w u (polarDenominator_pos (htarget hu) (by simpa using hw) _)
    have hK0 := continuousOn_polarKernel_source q
    have hKr := continuousOn_polarKernelR_source q
    have hKrr := continuousOn_polarKernelRR_source q
    have hKtt := continuousOn_polarKernelTT_source q
    have hcT : SrcCont (polarKernelT q) := by
      unfold SrcCont polarKernelT
      exact (Continuous.continuousOn (by unfold angularComponent; fun_prop)).mul
        (continuousOn_polarKernel_source (q - 1))
    have hF := hc_unit hK0
    have hFr := hc_unit hKr
    have hFrr := hc_unit hKrr
    have hFtt (r : ℝ) (hr : r ∈ Ico 0 1) := continuous_polar_slice (hc_unit hKtt) hr
    have hFd (r : ℝ) (hr : r ∈ Ioo 0 1) (θ : ℝ) :=
      hd_curve hK0 hKr (γ := fun u ↦ (u, θ)) (by fun_prop) r hr
        fun w s ↦ polarKernel_hasDerivAt_r q w s θ
    have hFrd (r : ℝ) (hr : r ∈ Ioo 0 1) (θ : ℝ) :=
      hd_curve hKr hKrr (γ := fun u ↦ (u, θ)) (by fun_prop) r hr
        fun w s ↦ polarKernelR_hasDerivAt_r q w s θ
    have hFdt (r : ℝ) (hr : r ∈ Ioo 0 1) (θ : ℝ) :=
      hd_curve hK0 hcT (γ := fun u ↦ (r, u)) (by fun_prop) θ hr
        fun w t ↦ polarKernel_hasDerivAt_t q w r t
    have hFtd (r : ℝ) (hr : r ∈ Ioo 0 1) (θ : ℝ) :=
      hd_curve hcT hKtt (γ := fun u ↦ (r, u)) (by fun_prop) θ hr
        fun w t ↦ polarKernelT_hasDerivAt_t q w r t
    have hpF (u : ℝ) : P (polarKernel q) u (2 * π) = P (polarKernel q) u 0 := by
      simp [P, polarKernel, polarDenominator, radialComponent]
    have hpFt (u : ℝ) : P (polarKernelT q) u (2 * π) = P (polarKernelT q) u 0 := by
      simp [P, polarKernelT, polarKernel, polarDenominator, radialComponent, angularComponent]
    have hFode (u : ℝ) (hu : u ∈ Ioo 0 1) (θ : ℝ) :
        polarOp k u (P (polarKernel q) u θ) (P (polarKernelR q) u θ)
          (P (polarKernelRR q) u θ) (P (polarKernelTT q) u θ) ≤ 0 := by
      have hr2 : u ^ 2 < 1 := by nlinarith [hu.1, hu.2]
      have hint {H : ℂ → ℝ → ℝ → ℝ} (hH : SrcCont H) : Integrable (fun w ↦ H w u θ * ‖f w‖) μ :=
        integrable_mul_of_continuousOn_compact (isCompact_closedBall 0 1) hμ hfn <|
          hH.comp ((continuous_const (y := (u, θ))).prodMk continuous_id).continuousOn
            fun _ hw ↦ ⟨hr2, hw⟩
      dsimp only [P]
      rw [← integral_polarOp k u (hint hK0) (hint hKr) (hint hKrr) (hint hKtt)]
      refine integral_nonpos_of_ae (hμ.mono fun w hw ↦ ?_)
      dsimp only [Pi.zero_apply]
      have hd := polarDenominator_pos hr2 (by simpa using hw) θ
      have ht' : 0 < 1 - u ^ 2 := sub_pos.mpr hr2
      rw [show polarOp k u (polarKernel q w u θ * ‖f w‖) (polarKernelR q w u θ * ‖f w‖)
          (polarKernelRR q w u θ * ‖f w‖) (polarKernelTT q w u θ * ‖f w‖) =
          polarOp k u (polarKernel q w u θ) (polarKernelR q w u θ)
            (polarKernelRR q w u θ) (polarKernelTT q w u θ) * ‖f w‖ by
        unfold polarOp; ring, show q = -k / 2 from rfl, polarKernel_op k w u θ hd hu.1.ne' ht'.ne']
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (sq_nonneg k)
          (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr (by simpa using hw)))))
          (mul_nonneg ht'.le hd.le)) (rpow_nonneg hd.le _)) (norm_nonneg _)
    generalize P (polarKernel q) = F at hF hFd hFdt hpF hFode ⊢
    generalize P (polarKernelR q) = Fr at hFr hFd hFrd hFode
    generalize P (polarKernelRR q) = Frr at hFrr hFrd hFode
    generalize P (polarKernelT q) = Ft at hFdt hFtd hpFt
    generalize P (polarKernelTT q) = Ftt at hFtt hFtd hFode
    generalize normalizer α = J at hJ hJpos hJd hJode ⊢
    generalize normalizerFirst α = Jr at hJr hJd hJrd hJode
    generalize normalizerSecond α = Jrr at hJrr hJrd hJode
    let Q (r θ : ℝ) := F r θ / J r - c
    let D (r θ : ℝ) := Fr r θ * J r - F r θ * Jr r
    let Qr (r θ : ℝ) := D r θ / J r ^ 2
    let ρ (r : ℝ) := r * (1 - r ^ 2) ^ k
    let ρ' (r : ℝ) := (1 - r ^ 2) ^ k - 2 * k * r ^ 2 * (1 - r ^ 2) ^ (k - 1)
    let M (r θ : ℝ) := ρ r * D r θ
    let Mr (r θ : ℝ) := ρ' r * D r θ + ρ r * (Frr r θ * J r - F r θ * Jrr r)
    have lift1 {g : ℝ → ℝ} (hg : ContinuousOn g (Ico 0 1)) : PolarCont (fun r _ ↦ g r) :=
      hg.comp continuous_fst.continuousOn fun _ hp ↦ hp.1
    have hn : ∀ p ∈ Ico (0 : ℝ) 1 ×ˢ (univ : Set ℝ), J p.1 ≠ 0 := fun p hp ↦ (hJpos p.1 hp.1).ne'
    have hQ : PolarCont Q := (hF.div (lift1 hJ) hn).sub continuousOn_const
    have hD := (hFr.mul (lift1 hJ)).sub (hF.mul (lift1 hJr))
    have hQr := hD.div ((lift1 hJ).pow 2) fun p hp ↦ pow_ne_zero 2 (hn p hp)
    have hQd (r : ℝ) (hr : r ∈ Ioo 0 1) (θ : ℝ) : HasDerivAt (fun u ↦ Q u θ) (Qr r θ) r :=
      ((hFd r hr θ).div (hJd r hr) (hJpos r ⟨hr.1.le, hr.2⟩).ne').sub_const c
    have hMd (r : ℝ) (hr : r ∈ Ioo 0 1) (θ : ℝ) : HasDerivAt (fun u ↦ M u θ) (Mr r θ) r := by
      have hρd : HasDerivAt ρ (ρ' r) r := by
        convert (hasDerivAt_id r).mul (hasDerivAt_radialWeight k hr) using 1
        · rfl
        · dsimp [ρ']; ring
      have hDd : HasDerivAt (fun u ↦ D u θ) (Frr r θ * J r - F r θ * Jrr r) r := by
        convert ((hFrd r hr θ).mul (hJd r hr)).sub ((hFd r hr θ).mul (hJrd r hr)) using 1
        dsimp; ring
      exact hρd.mul hDd
    intro r hr R hR hrR
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    let cap (x : ℝ) := c + (x - sqrt (x ^ 2 + ε ^ 2)) / 2
    let d₁ (x : ℝ) := (1 - x / sqrt (x ^ 2 + ε ^ 2)) / 2
    let d₂ (x : ℝ) := -(ε ^ 2) / (2 * sqrt (x ^ 2 + ε ^ 2) ^ 3)
    have hcb (x : ℝ) : min (x + c) c - ε ≤ cap x ∧ cap x ≤ min (x + c) c := by
      have hlo : |x| ≤ sqrt (x ^ 2 + ε ^ 2) :=
        sqrt_sq_eq_abs x ▸ sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))
      have hhi : sqrt (x ^ 2 + ε ^ 2) ≤ |x| + ε :=
        sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_abs x, mul_nonneg (abs_nonneg x) hε.le]⟩
      dsimp [cap]
      rcases le_total x 0 with h | h
      · rw [min_eq_left (by linarith), abs_of_nonpos h] at *; exact ⟨by linarith, by linarith⟩
      · rw [min_eq_right (by linarith), abs_of_nonneg h] at *; exact ⟨by linarith, by linarith⟩
    have hd_cap (x : ℝ) : HasDerivAt cap (d₁ x) x := by
      have hp' : x ^ 2 + ε ^ 2 ≠ 0 := by positivity
      convert (((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 2 |>.add_const (ε ^ 2)).sqrt
        hp')).div_const 2).const_add c using 1 <;> dsimp [cap, d₁]
      ring
    have hd_d1 (x : ℝ) : HasDerivAt d₁ (d₂ x) x := by
      have hp' : 0 < x ^ 2 + ε ^ 2 := by positivity
      have hs := (((hasDerivAt_id x).pow 2 |>.add_const (ε ^ 2)).sqrt hp'.ne')
      convert (((hasDerivAt_id x).div hs (sqrt_pos.mpr hp').ne' |>.const_sub 1).div_const 2)
        using 1 <;> dsimp [d₁, d₂]
      have := sq_sqrt hp'.le; field_simp [(sqrt_pos.mpr hp').ne']; nlinarith
    have hd₁c : Continuous d₁ := continuous_iff_continuousAt.mpr fun x ↦ (hd_d1 x).continuousAt
    have hd₂c : Continuous d₂ := Continuous.div continuous_const (by fun_prop) fun x ↦
      (mul_pos zero_lt_two (pow_pos (sqrt_pos.mpr (by positivity)) _)).ne'
    have hcapc : Continuous cap := continuous_iff_continuousAt.mpr fun x ↦ (hd_cap x).continuousAt
    let G (u θ : ℝ) := cap (Q u θ)
    let Gr (u θ : ℝ) := d₁ (Q u θ) * Qr u θ
    let Ψ (u θ : ℝ) := d₁ (Q u θ) * M u θ
    let Ψr (u θ : ℝ) := d₂ (Q u θ) * Qr u θ * M u θ + d₁ (Q u θ) * Mr u θ
    let Htt (u θ : ℝ) := d₂ (Q u θ) * (Ft u θ / J u) * Ft u θ + d₁ (Q u θ) * Ftt u θ
    have hG : PolarCont G := hcapc.comp_continuousOn hQ
    have hGr : PolarCont Gr := (hd₁c.comp_continuousOn hQ).mul hQr
    have hρc := continuousOn_id.mul (continuousOn_radialWeight k)
    have hρ'c := (continuousOn_radialWeight k).sub
      (((continuousOn_id.pow 2).const_mul (2 * k)).mul (continuousOn_radialWeight (k - 1)))
    have hMc := (lift1 hρc).mul hD
    have hΨ : PolarCont Ψ := (hd₁c.comp_continuousOn hQ).mul hMc
    have hΨr : PolarCont Ψr :=
      (((hd₂c.comp_continuousOn hQ).mul hQr).mul hMc).add
        ((hd₁c.comp_continuousOn hQ).mul (((lift1 hρ'c).mul hD).add
          ((lift1 hρc).mul ((hFrr.mul (lift1 hJ)).sub (hF.mul (lift1 hJrr))))))
    have hΦ : AntitoneOn (angularMean Ψ) (Ico 0 1) :=
      antitoneOn_Ico_of_deriv_nonpos (continuousOn_angularMean hΨ)
        (fun u hu ↦ hasDerivAt_angularMean hu hΨ hΨr fun s hs θ ↦ by
          have hdQ := HasDerivAt.comp s (hd_d1 (Q s θ)) (hQd s hs θ)
          exact hdQ.mul (hMd s hs θ))
        (fun u hu ↦ by
          have huc : u ∈ Ico 0 1 := ⟨hu.1.le, hu.2⟩
          have hir := (continuous_polar_slice hΨr huc).intervalIntegrable (μ := volume) 0 (2 * π)
          have hitt : IntervalIntegrable (Htt u) volume 0 (2 * π) := by
            have hFtc : Continuous (Ft u) := continuous_iff_continuousAt.mpr fun θ ↦ (hFtd u hu θ).continuousAt
            have hQu := continuous_polar_slice hQ huc; have hFttu := hFtt u huc
            exact (by dsimp [Htt]; fun_prop : Continuous (Htt u)).intervalIntegrable 0 (2 * π)
          have hd_Htt (θ : ℝ) : HasDerivAt (fun t ↦ d₁ (F u t / J u - c) * Ft u t) (Htt u θ) θ :=
            (HasDerivAt.comp θ (hd_d1 (Q u θ)) (((hFdt u hu θ).div_const (J u)).sub_const c)).mul
              (hFtd u hu θ)
          have hz : (∫ θ in 0..2 * π, Htt u θ) = 0 := by
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ ↦ hd_Htt θ) hitt,
              hpF u, hpFt u, sub_self]
          let ctt := (1 - u ^ 2) ^ k * J u / u
          have hi := intervalIntegral.integral_mono_on (μ := volume) two_pi_pos.le
            (hir.add (hitt.const_mul ctt)) (intervalIntegrable_const (c := (0 : ℝ)))
            fun θ _ ↦ by
              have hj := hJpos u huc
              have ht' : 0 < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
              have hqflux : Mr u θ + ctt * Ftt u θ ≤ 0 := by
                have hcomb : Mr u θ + ctt * Ftt u θ =
                    u * (1 - u ^ 2) ^ k *
                      (J u * polarOp k u (F u θ) (Fr u θ) (Frr u θ) (Ftt u θ) -
                        F u θ * polarOp k u (J u) (Jr u) (Jrr u) 0) := by
                  dsimp only [Mr, ctt, ρ, ρ', D, polarOp]
                  rw [rpow_sub_one ht'.ne']
                  field_simp [hu.1.ne', ht'.ne']; ring
                rw [hcomb, hJode u hu, mul_zero, sub_zero]
                exact mul_nonpos_of_nonneg_of_nonpos
                  (mul_nonneg hu.1.le (rpow_nonneg ht'.le k))
                  (mul_nonpos_of_nonneg_of_nonpos hj.le (hFode u hu θ))
              have hd₁n : 0 ≤ d₁ (Q u θ) := by
                have hp' : 0 < sqrt (Q u θ ^ 2 + ε ^ 2) := sqrt_pos.mpr (by positivity)
                have hle : Q u θ ≤ sqrt (Q u θ ^ 2 + ε ^ 2) :=
                  (le_abs_self _).trans (sqrt_sq_eq_abs _ ▸ sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε)))
                dsimp [d₁]; linarith [(div_le_one hp').mpr hle]
              have hd₂n : d₂ (Q u θ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
                (neg_nonpos.mpr (sq_nonneg ε)) (by positivity)
              have h1 := mul_nonpos_of_nonneg_of_nonpos hd₁n hqflux
              have hnn : 0 ≤ Qr u θ * M u θ + ctt * ((Ft u θ / J u) * Ft u θ) := by
                have heq_sq : Qr u θ * M u θ + ctt * ((Ft u θ / J u) * Ft u θ) =
                    ρ u * (D u θ / J u) ^ 2 + ((1 - u ^ 2) ^ k / u) * Ft u θ ^ 2 := by
                  dsimp [Qr, M, ctt]; field_simp [hj.ne']
                have := hu.1; have : 0 ≤ (1 - u ^ 2) ^ k := rpow_nonneg ht'.le k
                rw [heq_sq]; dsimp [ρ]; positivity
              have h2 := mul_nonpos_of_nonpos_of_nonneg hd₂n hnn
              dsimp [Ψr, Htt]; linarith
          rw [intervalIntegral.integral_add hir (hitt.const_mul ctt),
            intervalIntegral.integral_const_mul, hz, mul_zero, add_zero,
            intervalIntegral.integral_zero] at hi
          exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr two_pi_pos.le) hi)
    have hm : angularMean G R ≤ angularMean G r :=
      antitoneOn_Ico_of_deriv_nonpos (continuousOn_angularMean hG)
        (fun u hu ↦ hasDerivAt_angularMean hu hG hGr fun s hs θ ↦ (hd_cap _).comp s (hQd s hs θ))
        (fun u hu ↦ by
          have huc : u ∈ Ico 0 1 := ⟨hu.1.le, hu.2⟩
          have hj := hJpos u huc
          have hle := hΦ ⟨le_rfl, zero_lt_one⟩ huc hu.1.le
          have h0 : angularMean Ψ 0 = 0 := by simp [angularMean, Ψ, M, ρ]
          have hrel : angularMean Ψ u = ρ u * J u ^ 2 * angularMean Gr u := by
            unfold angularMean
            have hc : (∫ θ in 0..2 * π, Ψ u θ) =
                (ρ u * J u ^ 2) * ∫ θ in 0..2 * π, Gr u θ := by
              rw [← intervalIntegral.integral_const_mul]
              exact intervalIntegral.integral_congr fun θ _ ↦ by
                dsimp [Ψ, Gr, M, Qr]; field_simp [hj.ne']
            rw [hc]; ring
          rw [h0, hrel] at hle
          exact nonpos_of_mul_nonpos_right hle (mul_pos
            (mul_pos hu.1 (rpow_pos_of_pos (by nlinarith [hu.1, hu.2]) _)) (sq_pos_of_pos hj)))
        hr hR hrR
    have hmc {u : ℝ} (hu : u ∈ Ico 0 1) : Continuous (fun θ ↦ min (F u θ / J u) c) :=
      (((continuous_polar_slice hQ hu).add (continuous_const (y := c))).congr
        fun _ ↦ sub_add_cancel _ _).inf continuous_const
    have hlow := mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_on (μ := volume) two_pi_pos.le
      (((hmc hR).sub continuous_const).intervalIntegrable _ _)
      ((continuous_polar_slice hG hR).intervalIntegrable _ _)
      fun θ _ ↦ by simpa [Q] using (hcb (Q R θ)).1) (inv_nonneg.mpr two_pi_pos.le)
    have hupp := mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_on (μ := volume) two_pi_pos.le
      ((continuous_polar_slice hG hr).intervalIntegrable _ _) ((hmc hr).intervalIntegrable _ _)
      fun θ _ ↦ by simpa [Q] using (hcb (Q r θ)).2) (inv_nonneg.mpr two_pi_pos.le)
    dsimp only [Pi.sub_def] at hlow
    rw [intervalIntegral.integral_sub ((hmc hR).intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_sub, ← mul_assoc,
      inv_mul_cancel₀ two_pi_pos.ne', one_mul] at hlow
    unfold angularMean at hm ⊢
    linarith
  have hUpos (z : ℂ) : 0 ≤ U z := div_nonneg
    (integral_nonneg fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (normalizer_nonneg α ‖z‖)
  let s := t / gammaConstant α
  have hs : 0 < s := div_pos ht hD
  let ρ (y : ℝ) := sqrt (1 - y ^ (α + 1)⁻¹)
  have hρ : Measurable ρ := by dsimp [ρ]; fun_prop
  have hρ_mem (y : ℝ) (hy : 0 < y) : ρ y ∈ Ico 0 1 :=
    ⟨sqrt_nonneg _, (sqrt_lt' zero_lt_one).mpr
      (by simpa using sub_lt_self (1 : ℝ) (rpow_pos_of_pos hy _))⟩
  have hρ_unit {y : ℝ} (hy : y ∈ Ioo 0 1) : ρ y ∈ Ioo 0 1 :=
    ⟨sqrt_pos.mpr (sub_pos.mpr (rpow_lt_one hy.1.le hy.2 (inv_pos.mpr hp))), (hρ_mem y hy.1).2⟩
  let L (y : ℝ) := circleAverage (fun z ↦ if s * y < U z then (1 : ℝ) else 0) 0 (ρ y)
  let G (y : ℝ) := circleAverage (fun z ↦ min (U z) (s * y)) 0 (ρ y)
  let M := ∫ w, ‖f w‖ ∂μ
  have hb_int {H : ℝ → ℂ → ℝ} (hH : Measurable H.uncurry) {B : ℝ}
      (hb : ∀ y ∈ Icc 0 1, ∀ z, ‖H y z‖ ≤ B) :
      (∀ {y}, y ∈ Icc 0 1 → ∀ r, CircleIntegrable (H y) 0 r) ∧
      IntegrableOn (fun y ↦ circleAverage (H y) 0 (ρ y)) (Icc 0 1) := by
    have hci {y : ℝ} (hy : y ∈ Icc 0 1) (r : ℝ) : CircleIntegrable (H y) 0 r := by
      rw [CircleIntegrable, intervalIntegrable_iff_integrableOn_Icc_of_le two_pi_pos.le]
      exact Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
        (hH.comp (measurable_const.prodMk (continuous_circleMap 0 r).measurable)).aestronglyMeasurable
        (.of_forall fun _ ↦ hb y hy _)
    refine ⟨hci, Measure.integrableOn_of_bounded measure_Icc_lt_top.ne ?_
      ((ae_restrict_mem measurableSet_Icc).mono fun y hy ↦ (norm_circleAverage_le_circleAverage_norm ..).trans
        (circleAverage_mono_on_of_le_circle (hci hy _).norm fun _ _ ↦ hb y hy _))⟩
    have hm : Measurable fun p : ℝ × ℝ ↦ H p.1 (circleMap 0 (ρ p.1) p.2) :=
      hH.comp (measurable_fst.prodMk
        (circleMap.continuous.measurable.comp ((hρ.comp measurable_fst).prodMk measurable_snd)))
    simp only [circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le two_pi_pos.le]
    exact (measurable_const.mul (hm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc 0 (2 * π)))).measurable).aestronglyMeasurable
  obtain ⟨hciL, hiL⟩ := hb_int (H := fun y z ↦ if s * y < U z then (1 : ℝ) else 0)
    (measurable_const.ite (measurableSet_lt (measurable_const.mul measurable_fst)
      (hU.comp measurable_snd)) measurable_const)
    (B := 1) fun _ _ _ ↦ by split_ifs <;> norm_num
  obtain ⟨hciC, hiG⟩ := hb_int (H := fun y z ↦ min (U z) (s * y))
    ((hU.comp measurable_snd).inf (measurable_const.mul measurable_fst)) (B := s) fun y hy z ↦ by
      rw [Real.norm_of_nonneg (le_min (hUpos z) (mul_nonneg hs.le hy.1))]
      exact (min_le_right _ _).trans (mul_le_of_le_one_right hs.le hy.2)
  have hI {F : ℝ → ℝ} (hF : IntegrableOn F (Icc 0 1)) {u v : ℝ}
      (hu : u ∈ Icc 0 1 := by constructor <;> linarith)
      (hv : v ∈ Icc 0 1 := by constructor <;> linarith) : IntervalIntegrable F volume u v :=
    (hF.mono_set (uIcc_subset_Icc hu hv)).intervalIntegrable
  have hi : s * (∫ y in 0..1, L y) ≤ M := by
    rw [← intervalIntegral.integral_const_mul]
    have h0 : ContinuousOn (fun u ↦ ∫ y in 0..u, s * L y) (Icc 0 1) :=
      uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1) ▸ intervalIntegral.continuousOn_primitive_interval
        (by rw [uIcc_of_le zero_le_one]; exact hiL.const_mul s)
    have hb : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Ioo 0 1 := Ioo_mem_nhdsGT zero_lt_one
    have ht0 : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝[Icc 0 1] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨tendsto_id.mono_left nhdsWithin_le_nhds,
        hb.mono fun _ hh ↦ ⟨hh.1.le, hh.2.le⟩⟩
    have hlim := ((continuousOn_const (c := ∫ y in 0..1, s * L y)).sub h0
      0 ⟨le_rfl, zero_le_one⟩).tendsto.comp ht0
    simpa using le_of_tendsto hlim (hb.mono fun h ⟨hh0, hh1⟩ ↦ by
      dsimp only [Function.comp_def, Pi.sub_apply, id_eq]
      rw [intervalIntegral.integral_interval_sub_left (hI (hiL.const_mul s)) (hI (hiL.const_mul s))]
      have hshift (y : ℝ) (hy0 : 0 ≤ y) (hyh : y ≤ 1 - h) : h * (s * L (y + h)) ≤ G (y + h) - G y := by
        have hc : s * y ≤ s * (y + h) := mul_le_mul_of_nonneg_left (by linarith) hs.le
        have hy1 : y ∈ Icc 0 1 := ⟨hy0, by linarith⟩
        have hyh1 : y + h ∈ Icc 0 1 := ⟨by linarith, by linarith⟩
        have hi_sm : CircleIntegrable
            (fun z ↦ (s * (y + h) - s * y) • if s * (y + h) < U z then (1 : ℝ) else 0) 0 (ρ (y + h)) :=
          (hciL hyh1 _).const_smul
        have havg := circleAverage_mono hi_sm
          ((hciC hyh1 (ρ (y + h))).sub (hciC hy1 (ρ (y + h)))) fun z _ ↦ by
            dsimp only [Pi.sub_apply]
            by_cases hz : s * (y + h) < U z
            · rw [ite_eq_left hz, smul_eq_mul, mul_one, min_eq_right hz.le, min_eq_right (hc.trans hz.le)]
            · rw [ite_eq_right hz, smul_eq_mul, mul_zero]; exact sub_nonneg.mpr (min_le_min_left _ hc)
        rw [circleAverage_fun_smul, circleAverage_sub (hciC hyh1 _) (hciC hy1 _)] at havg
        have hm : G y ≤ circleAverage (fun z ↦ min (U z) (s * y)) 0 (ρ (y + h)) := by
          rcases eq_or_lt_of_le hy0 with rfl | hpos
          · simp [G, mul_zero, show ∀ z, min (U z) 0 = 0 from fun z ↦ min_eq_right (hUpos z), circleAverage_const]
          · exact hanti (s * y) (hρ_mem (y + h) (by linarith)) (hρ_mem y hpos)
              (sqrt_le_sqrt <| sub_le_sub_left (rpow_le_rpow hy0 (by linarith) (inv_nonneg.mpr hp.le)) 1)
        calc h * (s * L (y + h)) = (s * (y + h) - s * y) • L (y + h) := by simp only [smul_eq_mul]; ring
          _ ≤ _ := havg
          _ ≤ _ := sub_le_sub_left hm _
      have hLc : IntervalIntegrable (fun y ↦ s * L (y + h)) volume 0 (1 - h) :=
        (IntervalIntegrable.comp_add_right_iff).mpr (hI (hiL.const_mul s))
      have hGc : IntervalIntegrable (fun y ↦ G (y + h)) volume 0 (1 - h) :=
        (IntervalIntegrable.comp_add_right_iff).mpr (hI hiG)
      have him := intervalIntegral.integral_mono_on (by linarith : 0 ≤ 1 - h) (hLc.const_mul h)
        (hGc.sub (hI hiG)) fun y hy ↦ hshift y hy.1 hy.2
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hGc (hI hiG),
        intervalIntegral.integral_comp_add_right (fun y ↦ s * L y),
        intervalIntegral.integral_comp_add_right G,
        intervalIntegral.integral_interval_sub_interval_comm' (hI hiG) (hI hiG) (hI hiG),
        zero_add, sub_add_cancel] at him
      have hlo : 0 ≤ ∫ y in 0..h, G y :=
        intervalIntegral.integral_nonneg hh0.le fun y hy ↦
          circleAverage_nonneg_of_nonneg fun z _ ↦ le_min (hUpos z) (mul_nonneg hs.le hy.1)
      have hhi : (∫ y in 1 - h..1, G y) ≤ h * M :=
        (intervalIntegral.integral_mono_on (by linarith) (hI hiG) (intervalIntegrable_const (c := M))
          fun y hy ↦ by
            have h := hanti (s * y) ⟨le_rfl, zero_lt_one⟩
              (hρ_mem y (by linarith [hy.1])) (hρ_mem y (by linarith [hy.1])).1
            simp only [circleAverage_zero] at h
            have h0 : U 0 = M := by simp [U, WP, M, weightedKernel]
            exact h.trans (h0 ▸ min_le_left _ _)).trans_eq (by simp)
      exact (mul_le_mul_iff_of_pos_left hh0).mp (by linarith))
  let S := {z : ℂ | s * (1 - ‖z‖ ^ 2) ^ (α + 1) < U z}
  have hS : MeasurableSet S := measurableSet_lt (by fun_prop) hU
  have heq : (∫ y in 0..1, L y) = μ.real S := by
    let φ (r : ℝ) := (1 - r ^ 2) ^ (α + 1)
    have hφc : Continuous φ := (continuous_const.sub (continuous_pow 2)).rpow_const fun _ ↦ Or.inr hp.le
    have hφa : StrictAntiOn φ (Icc 0 1) := fun r hr u hu h ↦
      rpow_lt_rpow (by nlinarith [hu.1, hu.2]) (by nlinarith [hr.1, hu.1]) hp
    have himg : φ '' Ioo 0 1 = Ioo 0 1 := by
      simpa [φ, zero_rpow hp.ne'] using hφc.continuousOn.image_Ioo_of_strictAntiOn zero_le_one hφa
    have h1 : (∫ y in 0..1, L y) =
        ∫ y in Ioo (0 : ℝ) 1, circleAverage (S.indicator (fun _ ↦ (1 : ℝ))) 0 (ρ y) := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun y hy ↦ circleAverage_congr_sphere fun z hz ↦ ?_
      have hn : ‖z‖ = ρ y := by simpa [abs_of_pos (hρ_unit hy).1] using hz
      have hpow : (1 - ‖z‖ ^ 2) ^ (α + 1) = y := by
        rw [hn]; dsimp [ρ]
        rw [sq_sqrt (sub_nonneg.mpr (rpow_lt_one hy.1.le hy.2 (inv_pos.mpr hp)).le),
          sub_sub_cancel, rpow_inv_rpow hy.1.le hp.ne']
      have hpred : z ∈ S ↔ s * y < U z := by simp [S, hpow]
      by_cases hzS : z ∈ S <;> simp [hzS, hpred.mp, mt hpred.mpr]
    rw [h1, ← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun r hr ↦ (hasDerivAt_radialWeight (α + 1) hr).hasDerivWithinAt)
      (hφa.injOn.mono Ioo_subset_Icc_self),
      show μ.real S = ∫ z, S.indicator (fun _ ↦ (1 : ℝ)) z ∂μ by
        simpa using (integral_indicator_const (μ := μ) (1 : ℝ) hS).symm,
      integral_weightedArea_eq_circleAverage hα ((integrable_const 1).indicator hS)]
    refine setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_
    have h1r : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
    have hpos : 0 < 2 * (α + 1) * r * (1 - r ^ 2) ^ α :=
      mul_pos (mul_pos (mul_pos zero_lt_two hp) hr.1) (rpow_pos_of_pos h1r _)
    simp only [add_sub_cancel_right]
    rw [show -2 * (α + 1) * r * (1 - r ^ 2) ^ α = -(2 * (α + 1) * r * (1 - r ^ 2) ^ α) by ring,
      abs_neg, abs_of_pos hpos, show 2 * (α + 1) * r * (1 - r ^ 2) ^ α =
        2 * r * ((α + 1) * (1 - r ^ 2) ^ α) by ring]
    congr 2
    dsimp [ρ]; rw [rpow_rpow_inv h1r.le hp.ne', sub_sub_cancel, sqrt_sq hr.1.le]
  rw [heq] at hi
  have hm : μ {z | ENNReal.ofReal t < weightedPositiveProjection α f z} ≤ μ S := by
    refine measure_mono_ae ((ae_mem_disk_weightedArea α).mono fun z hz hlev ↦ ?_)
    have hz1 := (mem_disk_iff z).mp hz
    have hWP_eq : weightedPositiveProjection α f z = ENNReal.ofReal (WP z) := by
      rw [ofReal_integral_eq_lintegral_ofReal
        ((integrable_weightedKernel_mul hα hf hz).norm.congr (.of_forall fun _ ↦ norm_mul ..))
        (.of_forall fun _ ↦ by positivity), weightedPositiveProjection]
      exact lintegral_congr fun _ ↦ by rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
    have hF : t < WP z := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mp (hWP_eq ▸ hlev)
    have hrm_le : (1 - ‖z‖ ^ 2) ^ (α + 1) * normalizer α ‖z‖ ≤ gammaConstant α := by
      rw [radialMass_mul_normalizer α (norm_nonneg z) hz1]
      exact ge_of_tendsto (tendsto_normalizer_neg hα)
        (mem_of_superset (Ioo_mem_nhdsLT hz1) fun R hR ↦ normalizer_mono (-α - 2) (norm_nonneg z) hR.1.le hR.2)
    dsimp [S, U]
    rw [lt_div_iff₀ (normalizer_pos α (norm_nonneg z) hz1)]
    calc s * (1 - ‖z‖ ^ 2) ^ (α + 1) * normalizer α ‖z‖
        ≤ s * gammaConstant α := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hrm_le hs.le
      _ = t := div_mul_cancel₀ t hD.ne'
      _ < _ := hF
  have hreal : t * μ.real {z | ENNReal.ofReal t < weightedPositiveProjection α f z} ≤
      gammaConstant α * M := by
    have h1 := (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _) hm) hs.le).trans hi
    have h2 := mul_le_mul_of_nonneg_left h1 hD.le
    rwa [← mul_assoc, mul_div_cancel₀ t hD.ne'] at h2
  have he := ENNReal.ofReal_le_ofReal hreal
  rwa [ENNReal.ofReal_mul ht.le, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_mul hD.le, ofReal_integral_norm_eq_lintegral_enorm hf] at he

theorem weightedPositiveProjection_constant_eq (α : ℝ) (hα : -1 < α) :
    weakTypeConstant (weightedArea α) (weightedPositiveProjection α) =
      ENNReal.ofReal (gammaConstant α) := by
  refine le_antisymm (sInf_le (isWeakTypeBound_weightedPositiveProjection hα)) ?_
  let := weightedArea_isProbabilityMeasure α hα
  refine le_sInf fun C hC ↦ le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    ((tendsto_normalizer_neg hα).congr' (mem_of_superset (Ioo_mem_nhdsLT zero_lt_one)
      fun r hr ↦ (radialMass_mul_normalizer α hr.1.le hr.2).symm))) ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with R hR
  have hnormal : Tendsto (fun t : ℝ ↦ t * normalizer α (t * R)) (𝓝[<] 1) (𝓝 (normalizer α R)) := by
    have htR : Tendsto (fun t : ℝ ↦ t * R) (𝓝[<] 1) (𝓝[Ico 0 1] R) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, mem_of_superset (Ioo_mem_nhdsLT zero_lt_one) fun t ht ↦
        ⟨mul_nonneg ht.1.le hR.1.le, (mul_le_of_le_one_left hR.1.le ht.2.le).trans_lt hR.2⟩⟩
      simpa using (continuousAt_id.mul_const R).tendsto.mono_left
        (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
    simpa using (tendsto_id.mono_left nhdsWithin_le_nhds).mul
      (((continuousOn_normalizer α) R ⟨hR.1.le, hR.2⟩).tendsto.comp htR)
  refine le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (hnormal.const_mul ((1 - R ^ 2) ^ (α + 1)))) ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht
  let ℓ := t * normalizer α (t * R)
  have hJ := normalizer_pos α (mul_nonneg ht.1.le hR.1.le)
    ((mul_le_of_le_one_left hR.1.le ht.2.le).trans_lt hR.2)
  have hℓ : 0 < ℓ := mul_pos ht.1 hJ
  have hℓJ : ℓ < normalizer α (t * R) := mul_lt_of_lt_one_left hJ ht.2
  let s : Set ℂ := {w | t < ‖w‖}
  have hs : MeasurableSet s := (isOpen_lt continuous_const continuous_norm).measurableSet
  let f : ℂ → ℂ := s.indicator 1
  let m := (weightedArea α).real s
  have hspos : 0 < weightedArea α s := by
    rw [weightedArea_norm_gt hα ht.1.le ht.2]
    exact ENNReal.ofReal_pos.mpr (rpow_pos_of_pos (by nlinarith [ht.1, ht.2]) _)
  have hsfinite : weightedArea α s ≠ ∞ := measure_ne_top _ _
  have hm : 0 < m := ENNReal.toReal_pos hspos.ne' hsfinite
  have hsub : weightedArea α {z | R < ‖z‖} ≤
      weightedArea α {z | ENNReal.ofReal (ℓ * m) < weightedPositiveProjection α f z} := by
    refine measure_mono_ae ((ae_mem_disk_weightedArea α).mono fun z hzd (hz : R < ‖z‖) ↦ ?_)
    have hK : Integrable (fun w ↦ ‖weightedKernel α z w‖) (weightedArea α) := by
      simpa only [mul_one] using (integrable_weightedKernel_mul hα (integrable_const (1 : ℂ)) hzd).norm
    have hann : normalizer α (t * R) * m ≤ ∫ w in s, ‖weightedKernel α z w‖ ∂weightedArea α := by
      have hg_int : Integrable (s.indicator fun w ↦ ‖weightedKernel α z w‖ - normalizer α (t * R)) (weightedArea α) :=
        (hK.sub (integrable_const _)).indicator hs
      have hnn : 0 ≤ ∫ w, s.indicator (fun w ↦ ‖weightedKernel α z w‖ - normalizer α (t * R)) w ∂weightedArea α := by
        rw [integral_weightedArea_eq_circleAverage hα hg_int]
        refine setIntegral_nonneg measurableSet_Ioo fun r hr ↦ mul_nonneg
          (mul_nonneg (mul_nonneg zero_le_two hr.1.le)
            (mul_nonneg (by linarith) (rpow_nonneg (by nlinarith [hr.1, hr.2]) _))) ?_
        by_cases htr : t < r
        · have hci' : CircleIntegrable (fun w ↦ ‖weightedKernel α z w‖) 0 r :=
            ((continuousOn_weightedKernel α hzd).norm.mono fun _ hw ↦ (mem_disk_iff _).mpr
              ((mem_sphere_zero_iff_norm.mp hw).trans_lt (by simpa [abs_of_pos hr.1] using hr.2))).circleIntegrable'
          rw [circleAverage_congr_sphere fun w hw ↦ indicator_of_mem (show w ∈ s by
              have : ‖w‖ = r := by simpa [abs_of_pos hr.1] using hw
              dsimp [s]; linarith) _,
            circleAverage_fun_sub hci' (circleIntegrable_const _ _ _), circleAverage_const, sub_nonneg]
          refine (normalizer_mono α (mul_nonneg ht.1.le hR.1.le)
            (mul_le_mul htr.le hz.le hR.1.le hr.1.le)
            ((mul_le_of_le_one_left (norm_nonneg z) hr.2.le).trans_lt ((mem_disk_iff z).mp hzd))).trans_eq ?_
          rw [circleAverage_eq_circleAverage_zero_one]
          simp only [norm_weightedKernel, add_zero, Complex.star_def, map_mul, Complex.conj_ofReal]
          let g (ξ : ℂ) := ‖1 - (z * (r : ℂ)) * ξ‖ ^ (-(α + 2))
          have hinv : circleAverage (fun ζ ↦ g (star ζ)) 0 1 = circleAverage g 0 1 := by
            rw [← circleAverage_zero_one_congr_inv]
            refine circleAverage_congr_sphere fun ζ hζ ↦ congrArg g ?_
            rw [Complex.inv_def, ← Complex.sq_norm, show ‖ζ‖ = 1 by simpa using hζ]; simp
          symm
          change circleAverage (fun ζ : ℂ ↦ ‖1 - z * ((r : ℂ) * (starRingEnd ℂ) ζ)‖ ^ (-(α + 2))) 0 1 = _
          rw [show (fun ζ : ℂ ↦ ‖1 - z * ((r : ℂ) * (starRingEnd ℂ) ζ)‖ ^ (-(α + 2))) =
              fun ζ ↦ g (star ζ) by funext ζ; dsimp [g]; rw [mul_assoc],
            hinv, circleAverage_def, normalizer, circleAverage_eq_integral_add (Complex.arg (z * r))]
          congr 1; refine intervalIntegral.integral_congr fun θ _ ↦ ?_
          dsimp only [g]; congr 2; nth_rw 1 [← Complex.norm_mul_exp_arg_mul_I (z * r)]
          simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.ofReal_add, add_mul,
            Complex.exp_add, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.1.le,
            mul_comm ‖z‖ r, Complex.ofReal_mul]; ring
        · exact le_of_eq (circleAverage_const_on_circle fun w hw ↦ indicator_of_notMem (by
            have : ‖w‖ = r := by simpa [abs_of_pos hr.1] using hw
            simpa [s, this] using htr) _).symm
      rw [integral_indicator hs, integral_sub hK.integrableOn (integrable_const _),
        setIntegral_const, smul_eq_mul, mul_comm m, sub_nonneg] at hnn
      exact hnn
    have hout := (mul_lt_mul_of_pos_right hℓJ hm).trans_le hann
    refine ((ENNReal.ofReal_lt_ofReal_iff ((mul_pos hℓ hm).trans hout)).mpr hout).trans_eq ?_
    rw [ofReal_integral_eq_lintegral_ofReal hK.integrableOn (.of_forall fun _ ↦ norm_nonneg _),
      weightedPositiveProjection, ← lintegral_indicator hs]
    exact lintegral_congr fun w ↦ by by_cases hw : w ∈ s <;> simp [f, hw, ← ofReal_norm]
  have hbound := (mul_le_mul_right hsub (ENNReal.ofReal (ℓ * m))).trans <| by
    simpa [f, enorm_indicator_eq_indicator_enorm, hs] using
      hC f ((integrable_const (1 : ℂ)).indicator hs) (ℓ * m) (mul_pos hℓ hm)
  rw [weightedArea_norm_gt hα hR.1.le hR.2, ENNReal.ofReal_mul hℓ.le,
    show ENNReal.ofReal m = weightedArea α s from ENNReal.ofReal_toReal hsfinite,
    mul_assoc, mul_comm (weightedArea α s), ← mul_assoc] at hbound
  dsimp only [Function.comp_def]
  rw [mul_comm ((1 - R ^ 2) ^ (α + 1)), ENNReal.ofReal_mul hℓ.le]
  exact (ENNReal.mul_le_mul_iff_left hspos.ne' hsfinite).mp hbound

theorem weightedProjection_constant_le (α : ℝ) (hα : -1 < α) :
    weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) ≤
      ENNReal.ofReal (gammaConstant α) :=
  sInf_le fun f hf t ht ↦
    (mul_le_mul_right (measure_mono fun z hz ↦ hz.trans_le
      (show ‖weightedProjection α f z‖ₑ ≤ weightedPositiveProjection α f z by
        simp only [weightedProjection, weightedPositiveProjection, ofReal_norm, ← enorm_mul]
        exact enorm_integral_le_lintegral_enorm _)) _).trans
      (isWeakTypeBound_weightedPositiveProjection hα f hf t ht)

theorem positiveProjection_constant_eq_one : weakTypeConstant diskArea positiveProjection = 1 := by
  simpa [funext weightedPositiveProjection_zero] using
    weightedPositiveProjection_constant_eq 0 (by norm_num)

theorem projection_constant_eq_one :
    weakTypeConstant diskArea (fun f z ↦ ‖projection f z‖ₑ) = 1 :=
  le_antisymm (by simpa using weightedProjection_constant_le 0 (by norm_num))
    (by simpa using one_le_weightedProjection_constant 0 (by norm_num))

end BergmanWeakType
