/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.KernelTransform
public import BergmanWeakType.WeightedSharp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

noncomputable section

open Set MeasureTheory Metric Filter Function
open scoped ComplexConjugate Topology ENNReal

namespace BergmanWeakType

instance area_isFiniteMeasureOnCompacts : IsFiniteMeasureOnCompacts area :=
  IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top

instance area_isOpenPosMeasure : Measure.IsOpenPosMeasure area :=
  Measure.isOpenPosMeasure_smul volume (by positivity)

theorem kernel_denominator_ne_zero_closed_left {ζ w : ℂ} (hζ : ‖ζ‖ ≤ 1) (hw : w ∈ disk) :
    1 - ζ * star w ≠ 0 := fun h ↦ by
  have hnorm : ‖ζ * star w‖ < 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg w) hζ).trans_lt ((mem_disk_iff w).mp hw)
  rw [(sub_eq_zero.mp h).symm, norm_one] at hnorm
  exact lt_irrefl 1 hnorm

/-- The compact-core integrand stays continuous even for boundary output parameters. -/
theorem continuousOn_coreIntegrand {q : ℂ → ℂ} (hq : ContinuousOn q disk)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) {r : ℝ} (hr : r < 1) :
    ContinuousOn (fun w ↦ q w * kernel ζ w) (closedBall 0 r) := by
  have hsub : closedBall (0 : ℂ) r ⊆ disk := fun _ hw ↦ lt_of_le_of_lt hw hr
  exact (hq.mono hsub).mul (((continuousOn_const.sub
    (continuousOn_const.mul continuousOn_id.star)).inv₀
    (fun w hw ↦ kernel_denominator_ne_zero_closed_left hζ (hsub hw))).pow 2)

theorem image_affine_disk {a b : ℂ} (hb : b ≠ 0) :
    (fun w ↦ a + b * w) '' disk = ball a ‖b‖ := by
  ext z
  refine ⟨?_, fun hz ↦ ⟨(z - a) / b, ?_, by field_simp; ring⟩⟩
  · rintro ⟨w, hw, rfl⟩
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_mul]
    simpa using mul_lt_mul_of_pos_left ((mem_disk_iff w).mp hw) (norm_pos_iff.mpr hb)
  · rw [mem_disk_iff, norm_div, div_lt_one (norm_pos_iff.mpr hb)]
    exact mem_ball_iff_norm.mp hz

/-- An integrable input whose output is at least one almost everywhere gives a lower bound by
the ratio of total measure to input mass. -/
theorem measure_univ_div_mass_le_weakTypeConstant_of_witness
    {μ : Measure ℂ} {T : (ℂ → ℂ) → ℂ → ℝ≥0∞} {f : ℂ → ℂ}
    (hf : Integrable f μ) (hout : ∀ᵐ z ∂μ, 1 ≤ T f z) :
    μ Set.univ / (∫⁻ z, ‖f z‖ₑ ∂μ) ≤ weakTypeConstant μ T :=
  le_sInf fun C hC ↦ ENNReal.div_le_of_le_mul <| ENNReal.le_of_forall_lt_one_mul_le fun a ha ↦ by
    by_cases ha0 : a = 0
    · simp [ha0]
    have hatop : a ≠ ⊤ := ne_top_of_lt ha
    have hlevel : {z | a < T f z} =ᵐ[μ] Set.univ :=
      hout.mono fun z hz ↦ propext (iff_true_intro (ha.trans_le hz))
    have hbound := hC f hf a.toReal (ENNReal.toReal_pos ha0 hatop)
    rwa [ENNReal.ofReal_toReal hatop, measure_congr hlevel] at hbound

/-- A nondegenerate complex affine map, as a measurable equivalence. -/
def affineMeasurableEquiv (a b : ℂ) (hb : b ≠ 0) : ℂ ≃ᵐ ℂ where
  toFun w := a + b * w
  invFun z := (z - a) / b
  left_inv w := by field_simp; ring
  right_inv z := by field_simp; ring
  measurable_toFun := by change Measurable (fun w : ℂ ↦ a + b * w); fun_prop
  measurable_invFun := by change Measurable (fun z : ℂ ↦ (z - a) / b); fun_prop

-- Keep the public statement's topology, bornology, and metric instances identical to the
-- independently elaborated Challenge statement, which imports no C*-algebra instances.
attribute [-instance] instCommCStarAlgebraComplex in
/-- Among bounded simply connected domains, positive weak constant one characterizes disks. -/
theorem positive_constant_eq_one_iff_disk (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsSimplyConnected Ω)
    (K : ℂ → ℂ → ℂ) (hK : IsBergmanKernel Ω K) :
    weakTypeConstant (area.restrict Ω) (domainPositiveProjection Ω K) = 1 ↔
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ Ω = Metric.ball c R := by
  have : IsFiniteMeasure (area.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hbounded.measure_lt_top.ne
  have hsec {z : ℂ} (hz : z ∈ Ω) : (∫ w, K z w ∂area.restrict Ω) = 1 := by
    simpa only [mul_one] using
      hK.reproduces (fun _ ↦ 1) (differentiableOn_const 1) (memLp_const 1) z hz
  constructor
  · intro hc
    by_contra hnd
    have hproper : Ω ≠ univ := fun heq ↦ NormedSpace.unbounded_univ ℝ ℂ (heq ▸ hbounded)
    obtain ⟨x₀, hx₀⟩ := hconnected.nonempty
    obtain ⟨ψ, hψ, hψbij, _⟩ := Complex.exists_bijOn_unitBall_map_eq_zero hopen hconnected hproper hx₀
    let φ := invFunOn ψ Ω
    have hψinv : InvOn φ ψ Ω disk := hψbij.invOn_invFunOn
    have hφ : DifferentiableOn ℂ φ disk :=
      differentiableOn_inverse hopen isOpen_ball hψ hψinv (hψinv.1.mapsTo hψbij.surjOn)
    have hbij : BijOn φ disk Ω := hψbij.symm hψinv.symm
    have hinv : InvOn ψ φ disk Ω := hψinv.symm
    have hne (z : ℂ) (hz : z ∈ disk) : deriv φ z ≠ 0 :=
      deriv_ne_zero_of_bijOn isOpen_ball hopen hφ hbij hz
    let r : ℝ := 1 / 2
    have hr : 0 < r := by norm_num
    have hr1 : r < 1 := by norm_num
    have hsub_r : ball (0 : ℂ) r ⊆ disk := ball_subset_ball hr1.le
    let E := φ '' ball (0 : ℂ) r
    have hEopen : IsOpen E := by
      rw [isOpen_iff_mem_nhds]; rintro _ ⟨w, hw, rfl⟩
      exact ((hφ.mono hsub_r).analyticAt (isOpen_ball.mem_nhds hw)).eventually_constant_or_nhds_le_map_nhds.resolve_left
        (not_eventually_constant_of_injOn isOpen_ball (hbij.injOn.mono hsub_r) hw)
        (image_mem_map (isOpen_ball.mem_nhds hw))
    have hE : MeasurableSet E := hEopen.measurableSet
    have hsub : E ⊆ Ω := by rintro _ ⟨w, hw, rfl⟩; exact hbij.mapsTo (hsub_r hw)
    have hEpos : 0 < area E := hEopen.measure_pos area ⟨φ 0, 0, mem_ball_self hr, rfl⟩
    have hφbdd : Bornology.IsBounded (φ '' disk) := hbij.image_eq.symm ▸ hbounded
    have hφnd : ¬∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ φ '' disk = ball c R := by rwa [hbij.image_eq]
    have hq : DifferentiableOn ℂ (deriv φ) disk :=
      (hφ.analyticOnNhd isOpen_ball).deriv.differentiableOn
    have hprod : ContinuousOn (fun p : ℂ × ℂ ↦ deriv φ p.2 * kernel p.1 p.2)
        (closedBall 0 1 ×ˢ closedBall 0 r) :=
      (hq.continuousOn.comp continuous_snd.continuousOn fun p hp ↦ lt_of_le_of_lt hp.2 hr1).mul
        (((continuousOn_const.sub (continuous_fst.continuousOn.mul
          continuous_snd.star.continuousOn)).inv₀ fun p hp ↦
          kernel_denominator_ne_zero_closed_left (by simpa using hp.1) (lt_of_le_of_lt hp.2 hr1)).pow 2)
    have : IsFiniteMeasure (area.restrict (ball (0 : ℂ) r)) :=
      isFiniteMeasure_restrict.mpr ((isBounded_ball (x := (0 : ℂ)) (r := r)).measure_lt_top).ne
    have hμ : ∀ᵐ w ∂area.restrict (ball (0 : ℂ) r), w ∈ closedBall 0 r :=
      (ae_restrict_mem isOpen_ball.measurableSet).mono fun _ hw ↦ ball_subset_closedBall hw
    have hcont_int {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
        [SecondCountableTopologyEither ℂ G] {F : ℂ → ℂ → G}
        (hF : ContinuousOn (fun p : ℂ × ℂ ↦ F p.1 p.2) (closedBall 0 1 ×ˢ closedBall 0 r)) :
        ContinuousOn (fun z ↦ ∫ w in ball 0 r, F z w ∂area) (closedBall 0 1) := by
      obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1 |>.prod
        (isCompact_closedBall (0 : ℂ) r)).bddAbove_image hF.norm
      refine continuousOn_of_dominated (bound := fun _ ↦ M) (fun z hz ↦ ?_)
        (fun z hz ↦ hμ.mono fun w hw ↦ hM (mem_image_of_mem _
          (show (z, w) ∈ closedBall 0 1 ×ˢ closedBall 0 r from ⟨hz, hw⟩)))
        (integrable_const M)
        (hμ.mono fun w hw ↦ hF.comp (continuous_id.prodMk continuous_const).continuousOn
          fun z hz ↦ ⟨hz, hw⟩)
      have hc' : ContinuousOn (F z) (closedBall 0 r) :=
        hF.comp (continuous_const.prodMk continuous_id).continuousOn fun w hw ↦ ⟨hz, hw⟩
      simpa only [Measure.restrict_eq_self_of_ae_mem hμ] using
        hc'.aestronglyMeasurable isClosed_closedBall.measurableSet
          (μ := area.restrict (ball 0 r))
    have hI := hcont_int (F := fun ζ w ↦ deriv φ w * kernel ζ w) hprod
    have hJ := hcont_int (F := fun ζ w ↦ ‖deriv φ w * kernel ζ w‖) hprod.norm
    have hJ_pos (ζ : ℂ) (hζ : ζ ∈ closedBall (0 : ℂ) 1) :
        0 < ∫ w in ball 0 r, ‖deriv φ w * kernel ζ w‖ ∂area := by
      have hζnorm : ‖ζ‖ ≤ 1 := by simpa using hζ
      have hi : IntegrableOn (fun w ↦ deriv φ w * kernel ζ w) (ball 0 r) area :=
        ((continuousOn_coreIntegrand hq.continuousOn hζnorm hr1).integrableOn_compact
          (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
      refine (integral_pos_iff_support_of_nonneg (fun _ ↦ norm_nonneg _) hi.norm).mpr ?_
      have hsupp : ball (0 : ℂ) r ⊆ Function.support (fun w ↦ ‖deriv φ w * kernel ζ w‖) :=
        fun w hw ↦ norm_ne_zero_iff.mpr (mul_ne_zero (hne w (hsub_r hw)) (pow_ne_zero 2
          (inv_ne_zero (kernel_denominator_ne_zero_closed_left hζnorm (hsub_r hw)))))
      exact (measure_ball_pos area (0 : ℂ) hr).trans_le
        (by simpa using measure_mono (μ := area.restrict (ball (0 : ℂ) r)) hsupp)
    have hlt (ζ : ℂ) (hζ : ζ ∈ closedBall (0 : ℂ) 1) :
        ‖∫ w in ball 0 r, deriv φ w * kernel ζ w ∂area‖ <
          ∫ w in ball 0 r, ‖deriv φ w * kernel ζ w‖ ∂area := by
      have hζnorm : ‖ζ‖ ≤ 1 := by simpa using hζ
      have hm_ne {w : ℂ} (hw : w ∈ disk) : 1 - star ζ * w ≠ 0 := by
        simpa using kernel_denominator_ne_zero_closed_left (by simpa using hζnorm)
          (show star w ∈ disk by simpa [mem_disk_iff] using hw)
      refine lt_of_le_of_ne (norm_integral_le_integral_norm (fun w ↦ deriv φ w * kernel ζ w)
        (μ := area.restrict (ball 0 r))) fun heq ↦ hφnd ?_
      have hIne : (∫ w in ball 0 r, deriv φ w * kernel ζ w ∂area) ≠ 0 := by
        have hp := hJ_pos ζ hζ; rw [← heq] at hp; exact norm_pos_iff.mp hp
      have hderiv : ∀ w ∈ disk, deriv φ w * (1 - star ζ * w) ^ 2 = deriv φ 0 := by
        let c := ∫ w in ball 0 r, deriv φ w * kernel ζ w ∂area
        let g : ℂ → ℂ := fun w ↦ deriv φ w * kernel ζ w / c
        let G : ℂ → ℂ := fun w ↦ deriv φ w * (1 - star ζ * w) ^ 2 / c
        have hBcont := continuousOn_coreIntegrand hq.continuousOn hζnorm hr1
        have hBi : IntegrableOn (fun w ↦ deriv φ w * kernel ζ w) (ball 0 r) area :=
          (hBcont.integrableOn_compact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
        have hg : Integrable g (area.restrict (ball 0 r)) := hBi.div_const c
        have hreal : (fun z ↦ (g z).re) =ᵐ[area.restrict (ball 0 r)] (fun z ↦ ‖g z‖) := by
          apply (integral_eq_iff_of_ae_le hg.re hg.norm
            (Eventually.of_forall fun z ↦ Complex.re_le_norm (g z))).mp
          simp only [g, integral_re hg, integral_div, norm_div]
          rw [div_self hIne, ← heq, div_self (norm_ne_zero_iff.mpr hIne)]; rfl
        have hae : (fun z ↦ (g z).im) =ᵐ[area.restrict (ball 0 r)] (fun _ ↦ (0 : ℝ)) :=
          hreal.mono fun z hz ↦ Complex.abs_re_eq_norm.mp
            (by dsimp only at hz; rw [hz, abs_of_nonneg (norm_nonneg _)])
        have hphase : ∀ w ∈ ball (0 : ℂ) r, (g w).im = 0 :=
          Measure.eqOn_open_of_ae_eq hae isOpen_ball
            (Complex.continuous_im.comp_continuousOn ((hBcont.mono ball_subset_closedBall).div_const c))
            continuousOn_const
        have hlin : DifferentiableOn ℂ (fun w : ℂ ↦ 1 - star ζ * w) disk :=
          (differentiableOn_const 1).sub ((differentiableOn_const (star ζ)).mul differentiableOn_id)
        have hGd : DifferentiableOn ℂ G disk := (hq.mul (hlin.pow 2)).div_const c
        have hinner : ∀ w ∈ ball (0 : ℂ) r, (G w).im = 0 := fun w hw ↦ by
          have hd : 1 - ζ * star w ≠ 0 := kernel_denominator_ne_zero_closed_left hζnorm (hsub_r hw)
          have hconj : conj (1 - ζ * star w) = 1 - star ζ * w := by simp
          have hform : G w = g w * (‖1 - ζ * star w‖ ^ 4 : ℝ) := by
            rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← Complex.normSq_eq_norm_sq]
            push_cast
            rw [← Complex.mul_conj, hconj]
            dsimp [G, g, kernel]
            simp only [← starRingEnd_apply] at hd ⊢
            field_simp [hd, hIne]
          rw [hform, Complex.mul_im, Complex.ofReal_im, hphase w hw]; ring
        obtain ⟨d, hd⟩ := (hGd.analyticOnNhd isOpen_ball).mono hsub_r |>.eq_const_of_im_eq_const
          hinner isOpen_ball ⟨⟨0, mem_ball_self hr⟩, (convex_ball 0 r).isPreconnected⟩
        have hall : EqOn G (fun _ ↦ d) disk :=
          (hGd.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
            (convex_ball (0 : ℂ) 1).isPreconnected (by simp [disk])
            ((isOpen_ball.eventually_mem (mem_ball_self hr)).mono fun w hw ↦ hd w hw)
        intro w hw
        have hval : G w = G 0 := (hall hw).trans (hall (by simp [disk])).symm
        dsimp [G] at hval
        change deriv φ w * (1 - conj ζ * w) ^ 2 = deriv φ 0
        simpa only [mul_zero, sub_zero, one_pow, mul_one] using (div_left_inj' hIne).mp hval
      have hφ0 := hne 0 (by simp [disk])
      let H : ℂ → ℂ := fun w ↦ φ 0 + deriv φ 0 * w / (1 - star ζ * w)
      have hH (w : ℂ) (hw : w ∈ disk) : HasDerivAt H (deriv φ w) w := by
        have hn := hm_ne hw
        have heq' : deriv φ w = deriv φ 0 / (1 - star ζ * w) ^ 2 :=
          (eq_div_iff (pow_ne_zero 2 hn)).mpr (hderiv w hw)
        convert (((hasDerivAt_id w).const_mul (deriv φ 0)).div
          ((hasDerivAt_const w 1).sub ((hasDerivAt_id w).const_mul (star ζ))) hn).const_add
            (φ 0) using 1
        · rfl
        · simp only [Pi.sub_apply, id_eq, heq']; ring
      have hd : DifferentiableOn ℂ (φ - H) disk :=
        hφ.sub (fun w hw ↦ (hH w hw).differentiableAt.differentiableWithinAt)
      have hz : EqOn (deriv (φ - H)) 0 disk := fun w hw ↦ by
        simpa using (((hφ w hw).differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt.sub
          (hH w hw)).deriv
      have heq' : φ '' disk = H '' disk := image_congr fun w hw ↦ sub_eq_zero.mp (by
        simpa [H] using isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
          hd hz hw (show (0 : ℂ) ∈ disk by simp [disk]))
      have hζlt : ‖ζ‖ < 1 := lt_of_le_of_ne hζnorm fun h ↦ by
        obtain ⟨M, hMpos, hM⟩ := (heq' ▸ hφbdd).exists_pos_norm_le
        let N : ℝ := (M + ‖φ 0‖ + 1) / ‖deriv φ 0‖
        have hN : 0 < N := by dsimp [N]; have := norm_pos_iff.mpr hφ0; positivity
        let t : ℝ := N / (N + 1)
        have ht : 0 < t := by dsimp [t]; positivity
        have hw : (t : ℂ) * ζ ∈ disk := by
          rw [mem_disk_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, h]
          simpa [t] using (div_lt_one (by positivity)).mpr (by linarith)
        have hζmul : star ζ * ζ = 1 := by
          change conj ζ * ζ = 1
          rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, h]; norm_num
        have hvalue : (t : ℂ) * ζ / (1 - star ζ * ((t : ℂ) * ζ)) = (N : ℂ) * ζ := by
          have hN1 : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : N + 1 ≠ 0)
          rw [show star ζ * ((t : ℂ) * ζ) = t * (star ζ * ζ) by ring, hζmul, mul_one]
          dsimp [t]; push_cast; field_simp [hN1]; ring
        have hbound := hM _ ⟨_, hw, rfl⟩
        dsimp only [H] at hbound
        rw [mul_div_assoc, hvalue] at hbound
        have hnorm := norm_sub_le (φ 0 + deriv φ 0 * ((N : ℂ) * ζ)) (φ 0)
        simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hN, h, mul_one] at hnorm
        have hNmass : ‖deriv φ 0‖ * N = M + ‖φ 0‖ + 1 := by dsimp [N]; field_simp
        linarith
      let d : ℝ := 1 - ‖ζ‖ ^ 2
      have hdpos : 0 < d := by dsimp [d]; nlinarith [norm_nonneg ζ]
      have hdc : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hdpos.ne'
      let Z : Complex.UnitDisc := Complex.UnitDisc.mk ζ hζlt
      let c : ℂ := φ 0 + deriv φ 0 * ζ / (d : ℂ)
      let s : ℂ := deriv φ 0 / (d : ℂ)
      have hs : s ≠ 0 := div_ne_zero hφ0 hdc
      have hform (W : Complex.UnitDisc) :
          H W = c + s * (Complex.UnitDisc.shift (-Z) W : ℂ) := by
        have hn := hm_ne (show (W : ℂ) ∈ disk from (mem_disk_iff _).mpr W.norm_lt_one)
        have hnorm : (‖ζ‖ ^ 2 : ℝ) = star ζ * ζ := by
          change (‖ζ‖ ^ 2 : ℝ) = conj ζ * ζ
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
        change 1 - conj ζ * (W : ℂ) ≠ 0 at hn
        have hn' : 1 - (W : ℂ) * conj ζ ≠ 0 := by simpa only [mul_comm] using hn
        change (‖ζ‖ ^ 2 : ℝ) = conj ζ * ζ at hnorm
        dsimp [H, c, s]
        rw [Complex.UnitDisc.coe_shift]
        simp only [Z, Complex.UnitDisc.coe_neg, Complex.UnitDisc.coe_mk, map_neg, neg_mul,
          ← sub_eq_add_neg]
        field_simp [hn, hn', hdc]
        dsimp [d]; push_cast at hnorm ⊢; rw [hnorm]; field_simp [hn, hn']; ring
      have himage : H '' disk = (fun w ↦ c + s * w) '' disk := by
        ext z; constructor
        · rintro ⟨w, hw, rfl⟩
          let W : Complex.UnitDisc := Complex.UnitDisc.mk w ((mem_disk_iff _).mp hw)
          exact ⟨Complex.UnitDisc.shift (-Z) W,
            (mem_disk_iff _).mpr (Complex.UnitDisc.shift (-Z) W).norm_lt_one, (hform W).symm⟩
        · rintro ⟨w, hw, rfl⟩
          let W : Complex.UnitDisc := Complex.UnitDisc.mk w ((mem_disk_iff _).mp hw)
          let V := (Complex.UnitDisc.shift (-Z)).symm W
          refine ⟨V, (mem_disk_iff _).mpr V.norm_lt_one, ?_⟩
          dsimp only; rw [hform V]; simp [V, W]
      exact ⟨c, ‖s‖, norm_pos_iff.mpr hs, heq'.trans (himage.trans (image_affine_disk hs))⟩
    obtain ⟨a₀, ha₀, hmax⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMaxOn ⟨0, by simp⟩
      (hI.norm.div hJ fun ζ hζ ↦ (hJ_pos ζ hζ).ne')
    let η := 1 - ‖∫ w in ball 0 r, deriv φ w * kernel a₀ w ∂area‖ /
      ∫ w in ball 0 r, ‖deriv φ w * kernel a₀ w‖ ∂area
    have hη : 0 < η := sub_pos.mpr ((div_lt_one (hJ_pos a₀ ha₀)).2 (hlt a₀ ha₀))
    have hη1 : η ≤ 1 := sub_le_self _ (div_nonneg (norm_nonneg _) (hJ_pos a₀ ha₀).le)
    have hjac {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) :
        (‖deriv φ w‖ ^ 2 : ℝ) • K (φ z) (φ w) = (deriv φ w * kernel z w) / deriv φ z := by
      have hqz := hne z hz
      have hqw := hne w hw
      have hqwc : star (deriv φ w) ≠ 0 := star_ne_zero.mpr hqw
      rw [hK.disk_coordinate_formula hopen hφ hψ hbij hinv hz hw,
        Complex.real_smul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
      simp only [starRingEnd_apply]; field_simp [hqz, hqw, hqwc]
    have hgap (u : ℂ) (hu : u ∈ Ω) :
        ‖∫ w in E, K u w ∂area‖ ≤ (1 - η) * ∫ w in E, ‖K u w‖ ∂area := by
      obtain ⟨z, hz, rfl⟩ := hbij.surjOn hu
      have hgap_z : ‖∫ w in ball 0 r, deriv φ w * kernel z w ∂area‖ ≤
          (1 - η) * ∫ w in ball 0 r, ‖deriv φ w * kernel z w‖ ∂area := by
        have hbound := (div_le_iff₀ (hJ_pos z (ball_subset_closedBall hz))).mp
          (hmax (ball_subset_closedBall hz))
        dsimp only [Pi.div_apply] at hbound
        convert hbound using 1; dsimp [η]; ring
      have hI' : (∫ w in E, K (φ z) w ∂area) =
          (∫ w in ball 0 r, deriv φ w * kernel z w ∂area) / deriv φ z := by
        rw [area_integral_image_eq isOpen_ball (hφ.mono hsub_r) (hbij.injOn.mono hsub_r), ← integral_div]
        exact integral_congr_ae ((ae_restrict_mem isOpen_ball.measurableSet).mono fun w hw ↦
          hjac hz (hsub_r hw))
      have hJ' : (∫ w in E, ‖K (φ z) w‖ ∂area) =
          (∫ w in ball 0 r, ‖deriv φ w * kernel z w‖ ∂area) / ‖deriv φ z‖ := by
        rw [area_integral_image_eq isOpen_ball (hφ.mono hsub_r) (hbij.injOn.mono hsub_r), ← integral_div]
        refine integral_congr_ae ((ae_restrict_mem isOpen_ball.measurableSet).mono fun w hw ↦ ?_)
        simpa only [norm_smul, Real.norm_eq_abs, abs_sq, norm_div, smul_eq_mul] using
          congrArg norm (hjac hz (hsub_r hw))
      rw [hI', hJ', norm_div, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right hgap_z (norm_nonneg _)
    let μ := area.restrict Ω
    let f : ℂ → ℂ := fun w ↦ 1 - E.indicator (fun _ ↦ (η : ℂ)) w
    have hfnorm (w : ℂ) : ‖f w‖ = 1 - E.indicator (fun _ ↦ η) w := by
      by_cases hw : w ∈ E
      · simp only [f, indicator_of_mem hw, ← Complex.ofReal_one, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hη1)]
      · simp [f, hw]
    have hf : Integrable f μ :=
      (integrable_const (1 : ℂ)).sub ((integrable_const (η : ℂ)).indicator hE)
    have hEr : 0 < μ.real E := ENNReal.toReal_pos
      (by rw [Measure.restrict_apply hE, inter_eq_left.mpr hsub]; exact hEpos.ne')
      (measure_ne_top _ _)
    have hmass : (∫⁻ z, ‖f z‖ₑ ∂μ) < μ Set.univ := by
      rw [← ofReal_integral_norm_eq_lintegral_enorm hf]
      simp_rw [hfnorm]
      rw [integral_sub (integrable_const 1) ((integrable_const η).indicator hE),
        integral_indicator hE, integral_const, setIntegral_const]
      simp only [smul_eq_mul, mul_one]
      have hμpos : 0 < μ.real univ := hEr.trans_le (measureReal_mono (subset_univ E))
      simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
        (ENNReal.ofReal_lt_ofReal_iff hμpos).mpr (sub_lt_self _ (mul_pos hEr hη))
    have hout : ∀ᵐ a ∂μ, 1 ≤ domainPositiveProjection Ω K f a := by
      filter_upwards [ae_restrict_mem hopen.measurableSet] with a ha
      have hk : Integrable (K a) μ := (hK.squareIntegrable a ha).integrable (by norm_num)
      have hre : μ.restrict E = area.restrict E := by
        rw [Measure.restrict_restrict hE, inter_eq_left.mpr hsub]
      have hg : ‖∫ w in E, K a w ∂μ‖ ≤ (1 - η) * ∫ w in E, ‖K a w‖ ∂μ := by
        simpa only [hre] using hgap a ha
      have hsplit := integral_add_compl hE hk
      have hsplitnorm := integral_add_compl hE hk.norm
      have htriangle := norm_add_le (∫ w in E, K a w ∂μ) (∫ w in Eᶜ, K a w ∂μ)
      rw [hsplit, hsec ha, norm_one] at htriangle
      have hcomp := norm_integral_le_integral_norm (μ := μ.restrict Eᶜ) (K a)
      have heq : (fun w ↦ ‖K a w‖ * ‖f w‖) =
          (fun w ↦ ‖K a w‖ - E.indicator (fun w ↦ η * ‖K a w‖) w) := by
        funext w; rw [hfnorm]; by_cases hw : w ∈ E <;> simp [hw]; ring
      have hi : Integrable (fun w ↦ ‖K a w‖ * ‖f w‖) μ :=
        heq ▸ hk.norm.sub ((hk.norm.const_mul η).indicator hE)
      have hout' : 1 ≤ ∫ w, ‖K a w‖ * ‖f w‖ ∂μ := by
        rw [heq, integral_sub hk.norm ((hk.norm.const_mul η).indicator hE),
          integral_indicator hE, integral_const_mul]
        nlinarith
      rw [show domainPositiveProjection Ω K f a =
          ENNReal.ofReal (∫ w, ‖K a w‖ * ‖f w‖ ∂μ) by
        rw [ofReal_integral_eq_lintegral_ofReal hi
          (Eventually.of_forall fun w ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        simp only [domainPositiveProjection, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, μ]]
      exact_mod_cast ENNReal.ofReal_le_ofReal hout'
    have hlt : 1 < weakTypeConstant μ (domainPositiveProjection Ω K) :=
      ((ENNReal.lt_div_iff_mul_lt (Or.inr ENNReal.one_ne_top) (Or.inr one_ne_zero)).2
        (by simpa only [one_mul] using hmass)).trans_le
        (measure_univ_div_mass_le_weakTypeConstant_of_witness hf hout)
    exact (lt_irrefl (1 : ℝ≥0∞)) (hc ▸ hlt)
  · rintro ⟨a, R, hR, rfl⟩
    let b : ℂ := R
    have hb : b ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    have hnorm : ‖b‖ = R := by simp [b, abs_of_pos hR]
    apply le_antisymm
    · apply sInf_le
      show IsWeakTypeBound (area.restrict (ball a R)) (domainPositiveProjection (ball a R) K) 1
      let e := affineMeasurableEquiv a b hb
      let c := ENNReal.ofReal (R ^ 2)
      have hda (w : ℂ) : HasDerivAt e b w := by
        convert ((hasDerivAt_id w).const_mul b).const_add a using 1
        · rfl
        · simp
      have he : DifferentiableOn ℂ e disk := fun w _ ↦
        (hda w).differentiableAt.differentiableWithinAt
      have himage : e '' disk = ball a R := hnorm ▸ image_affine_disk hb
      have hbij : BijOn e disk (ball a R) := himage ▸ e.injective.injOn.bijOn_image
      have hederiv (w : ℂ) : deriv e w = b := (hda w).deriv
      have hμ : area.restrict (ball a R) = c • Measure.map e diskArea := by
        ext S hS
        rw [Measure.smul_apply, smul_eq_mul, e.map_apply]
        calc
          (area.restrict (ball a R)) S =
              ∫⁻ w in e '' disk, S.indicator (fun _ ↦ (1 : ℝ≥0∞)) w ∂area := by
            rw [himage]
            simpa using (lintegral_indicator_const (μ := area.restrict (ball a R)) hS 1).symm
          _ = ∫⁻ w in disk, c * S.indicator (fun _ ↦ (1 : ℝ≥0∞)) (e w) ∂area := by
            rw [area_lintegral_image_eq (U := disk) isOpen_ball he hbij.injOn]
            exact lintegral_congr fun w ↦ by rw [hederiv, hnorm]
          _ = c * diskArea (e ⁻¹' S) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            congr 1
            change (∫⁻ w, S.indicator (fun _ ↦ (1 : ℝ≥0∞)) (e w) ∂diskArea) = _
            rw [← lintegral_indicator_one (e.measurable hS)]
            exact lintegral_congr fun w ↦ by by_cases hw : e w ∈ S <;> simp [hw]
      have hinv : InvOn e.symm e disk (ball a R) :=
        ⟨fun _ _ ↦ e.symm_apply_apply _, fun _ _ ↦ e.apply_symm_apply _⟩
      have heinv : DifferentiableOn ℂ e.symm (ball a R) :=
        differentiableOn_inverse isOpen_ball isOpen_ball he hinv (hinv.1.mapsTo hbij.surjOn)
      have hproj (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ disk) :
          domainPositiveProjection (ball a R) K f (e z) =
            positiveProjection (fun w ↦ f (a + b * w)) z := by
        change (∫⁻ w, ENNReal.ofReal ‖K (e z) w‖ * ‖f w‖ₑ ∂area.restrict (ball a R)) = _
        rw [hμ, lintegral_smul_measure, e.measurableEmbedding.lintegral_map, smul_eq_mul,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr_ae (ae_mem_disk.mono fun w hw ↦ ?_)
        have hk := hK.disk_coordinate_formula isOpen_ball he heinv hbij hinv hz hw
        rw [hederiv, hederiv] at hk
        have hreal : R ^ 2 * ‖K (e z) (e w)‖ = ‖kernel z w‖ := by
          rw [← hnorm, hk, norm_div, norm_mul, norm_star]; field_simp
        have hcoef : c * ENNReal.ofReal ‖K (e z) (e w)‖ = ENNReal.ofReal ‖kernel z w‖ := by
          simpa only [c, ENNReal.ofReal_mul (sq_nonneg R)] using congrArg ENNReal.ofReal hreal
        dsimp only; rw [← mul_assoc, hcoef]; rfl
      have hc : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hR)
      intro f hf t ht
      have hfmap : Integrable f (Measure.map e diskArea) := by
        rw [hμ] at hf
        exact (integrable_smul_measure hc ENNReal.ofReal_ne_top).mp hf
      have hbound := isWeakTypeBound_positiveProjection_one _
        (e.measurableEmbedding.integrable_map_iff.mp hfmap) t ht
      have hlevel : diskArea (e ⁻¹' {z | ENNReal.ofReal t <
          domainPositiveProjection (ball a R) K f z}) =
          diskArea {z | ENNReal.ofReal t < positiveProjection (fun w ↦ f (a + b * w)) z} :=
        measure_congr (ae_mem_disk.mono fun w hw ↦ by
          simp only [mem_preimage, mem_ofPred_eq]; rw [hproj f hw])
      rw [hμ, Measure.smul_apply, smul_eq_mul, e.map_apply, hlevel,
        lintegral_smul_measure, e.measurableEmbedding.lintegral_map, one_mul]
      simp only [one_mul] at hbound
      rw [smul_eq_mul, ← mul_assoc, mul_comm (ENNReal.ofReal t) c, mul_assoc]
      exact mul_le_mul_right hbound c
    · have hout : ∀ᵐ z ∂area.restrict (ball a R),
          1 ≤ domainPositiveProjection (ball a R) K (fun _ ↦ 1) z :=
        (ae_restrict_mem isOpen_ball.measurableSet).mono fun z hz ↦ by
          have hnorm' := enorm_integral_le_lintegral_enorm (μ := area.restrict (ball a R)) (K z)
          rw [hsec hz] at hnorm'
          simpa [domainPositiveProjection, ← ofReal_norm] using hnorm'
      have huniv : (area.restrict (ball a R)) Set.univ ≠ 0 := by
        simpa using (measure_ball_pos area a hR).ne'
      simpa only [enorm_one, lintegral_const, one_mul,
        ENNReal.div_self huniv (measure_ne_top _ _)] using
        measure_univ_div_mass_le_weakTypeConstant_of_witness (integrable_const (1 : ℂ)) hout

end BergmanWeakType
