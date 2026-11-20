/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.TaylorSingular
public import DOZZ.FourPoint.Fusion.FullTimeSplit
public import DOZZ.FourPoint.TaylorOneRootIdentity
public import DOZZ.FourPoint.TaylorRegionCover
public import DOZZ.FourPoint.TwoRootedDomination
public import DOZZ.FourPoint.BPZ.RootedHessian

/-! # The one- and two-rooted Taylor terms as a Taylor remainder

For `0 < t ≤ 1/4`, the sum `r₁ + r₂ + r₃ + p₁ + p₂ + p₃` of the one-rooted and two-rooted
Taylor terms at `z = t` is the Taylor remainder `∫ u in 0..t, (t - u) * g2 u` of any function
`g2` that on `(0, t]` is the corresponding six-term expression (`bpz_rootedTerms_eq_integral`).

The proof substitutes `u = s t` in the Taylor remainder (`bpz_taylor_remainder_subst_complex`) and
integrates the six-term expression term by term in `s ∈ [0, 1]`. This needs the integrability of
the four weighted time integrands `s ↦ (1 - s) F (s t)`:

* The one-rooted integrands are handled by the local and exterior bounds of the fusion
  estimates (`bpzRR_oneRooted_pure_time_integrable`, `bpzRR_oneRooted_mixed_time_integrable`).
* The two-rooted integrands are dominated by the positive majorant
  `gammaHalfTwoRootedMajorant`. The Taylor fundamental estimate controls the majorant only
  below a small radius `r₀ ≤ 1/4`, which may be smaller than `t`; here the power bound
  `‖w‖ ^ (γ² / 2 - γ α₁)` is proved on the whole punctured quarter disk, from the exterior
  bound, the one-root rooting bound on the half-unit disk, and the explicit planar integral of
  the local kernel (`bpzRR_majorant_bound`). The exponent exceeds `-1`, which is all that
  integrability needs. The measurability of the two-rooted integrands in the moving root is
  proved as in the one-rooted case (`bpzRR_pair_measurable`). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate

namespace DOZZ.Proofs

/-! ### Measurability in the moving root -/

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
include Ω X hX hγ hγ2 hM

/-- The Coulomb expectation of a product of two spatial integrals is measurable in the moving
insertion point. -/
theorem bpzRR_pair_measurable
    (α₁ α₂ α₃ s : ℝ) (H₁ H₂ : ℂ × ℂ → ℂ) (hH₁ : Measurable H₁) (hH₂ : Measurable H₂) :
    Measurable (fun z : ℂ => ∫ ω,
      ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s).toReal : ℂ) *
        (∫ x, H₁ (z, x) ∂M ω) * (∫ x, H₂ (z, x) ∂M ω) ∂P) := by
  letI := hX.1
  exact measurable_integral_ae_parameter (equatorGFF_finiteGMC_aemeasurable P X hX γ hγ hγ2 M hM)
    (((Complex.measurable_ofReal.comp ((measurable_gammaHalf_coulombMass γ α₁ α₂ α₃).pow_const s).ennreal_toReal).mul
      (measurable_integral_finiteMeasure_parameter hH₁)).mul
      (measurable_integral_finiteMeasure_parameter hH₂))

/-- Both two-rooted expectations are measurable in the moving root. -/
theorem bpzRR_twoRooted_measurable (α₁ α₂ α₃ p : ℝ) (mixed : Bool) :
    Measurable (gammaHalfTwoRootedSpatial mixed P M γ α₁ α₂ α₃ p) := by
  have hK := Complex.measurable_ofReal.comp (fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃)
  have hZ := hK.div (measurable_snd.sub measurable_fst)
  unfold gammaHalfTwoRootedSpatial
  cases mixed
  · simpa only [Bool.false_eq_true, ite_false, gammaHalfRootKernelZ, pow_two, mul_assoc, Pi.div_apply, Pi.sub_apply, Function.comp_apply] using
      bpzRR_pair_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ (-p - 2) _ _ hZ hZ
  · simpa only [ite_true, gammaHalfRootKernelZ, gammaHalfRootKernelBar, Pi.div_apply, Pi.sub_apply, Function.comp_apply] using
      bpzRR_pair_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ (-p - 2) _ _ hZ
        (hK.div (continuous_star.measurable.comp (measurable_snd.sub measurable_fst)))

end

/-! ### The power bound for the two-rooted majorant on the quarter disk -/

/-- The local second-derivative kernel has Lebesgue integral on the half-unit disk bounded by the
scaling power `‖w‖ ^ (γ² / 2 - γ α₁)`, by the explicit planar (Riesz) integral. -/
theorem bpzRR_planar_ball_bound (γ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (hlo : γ / 2 < α₁)
    (hα₁ : α₁ < 2 / γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w ≠ 0 →
      ∫⁻ x in Metric.ball (0 : ℂ) (1 / 2),
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ w x / ‖x - w‖ ^ 2) ≤
        ENNReal.ofReal (C * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁)) := by
  have hk : 0 < γ ^ 2 / 2 := by positivity
  have hβ : γ ^ 2 / 2 < γ * α₁ := by
    have h := mul_lt_mul_of_pos_left hlo hγ
    linarith only [h]
  have hβ2 : γ * α₁ < 2 := by
    have h := (lt_div_iff₀ hγ).mp hα₁
    linarith only [h]
  have heq : ∀ w : ℂ, (fun u : ℂ => planarMixedKernel (γ ^ 2 / 2) (γ * α₁) w u) =ᵐ[volume]
      (fun u => ‖u‖ ^ (-(γ * α₁)) * ‖u - w‖ ^ (γ ^ 2 / 2 - 2)) := by
    intro w
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with u hu
    change ‖u - w‖ ^ (γ ^ 2 / 2 - 2) / ‖u‖ ^ (γ * α₁) = _
    rw [div_eq_mul_inv, Real.rpow_neg (norm_nonneg u)]
    ring
  obtain ⟨Cr, hCr⟩ : ∃ Cr : ℝ, ∀ w : ℂ, w ≠ 0 →
      ∫ u : ℂ, planarMixedKernel (γ ^ 2 / 2) (γ * α₁) w u =
        Cr * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁) :=
    ⟨_, fun w hw => (integral_congr_ae (heq w)).trans
      (positive_riesz_convolution_integral _ _ hk hβ hβ2 w hw)⟩
  refine ⟨2 ^ |γ * α₂| * |Cr| + 1, by positivity, ?_⟩
  intro w hw
  have hint := (planar_mixed_integral _ _ hk hβ hβ2 w hw).1
  have hnn : ∀ x, 0 ≤ planarMixedKernel (γ ^ 2 / 2) (γ * α₁) w x := fun x => by
    unfold planarMixedKernel
    positivity
  have hc0 : (0 : ℝ) ≤ 2 ^ |γ * α₂| := by positivity
  have hN : 0 ≤ ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁) := Real.rpow_nonneg (norm_nonneg _) _
  calc
    _ ≤ ∫⁻ x in Metric.ball (0 : ℂ) (1 / 2),
        ENNReal.ofReal (2 ^ |γ * α₂| * planarMixedKernel (γ ^ 2 / 2) (γ * α₁) w x) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball,
        ae_restrict_of_ae (Measure.ae_ne volume (0 : ℂ)),
        ae_restrict_of_ae (Measure.ae_ne volume w)] with x hx hx0 hxw
      exact ENNReal.ofReal_le_ofReal (fusion_localSecondKernel_bound γ α₁ α₂ α₃ w x
        (by simpa only [Metric.mem_ball, dist_zero_right] using hx) hx0 hxw)
    _ ≤ ∫⁻ x, ENNReal.ofReal (2 ^ |γ * α₂| * planarMixedKernel (γ ^ 2 / 2) (γ * α₁) w x) :=
      setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ x, 2 ^ |γ * α₂| * planarMixedKernel (γ ^ 2 / 2) (γ * α₁) w x) :=
      (ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
        (ae_of_all _ fun x => mul_nonneg hc0 (hnn x))).symm
    _ = ENNReal.ofReal (2 ^ |γ * α₂| * (Cr * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁))) := by
      rw [integral_const_mul, hCr w hw]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = (2 ^ |γ * α₂| * Cr) * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁) := by ring
        _ ≤ (2 ^ |γ * α₂| * |Cr|) * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self Cr) hc0) hN
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only) hN

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ p : ℝ)
  (hlo : γ / 2 < α₁)
include Ω X hX hγ hγ2 hM hlo

/-- The positive two-rooted majorant obeys the scaling power `‖w‖ ^ (γ² / 2 - γ α₁)` on the whole
punctured quarter disk, with a constant independent of `w`. The exterior region is bounded, and
the half-unit disk is bounded by the one-root rooting bound and the planar integral. -/
theorem bpzRR_majorant_bound (hα₁ : α₁ < 2 / γ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w ≠ 0 → ‖w‖ ≤ 1 / 4 →
      gammaHalfTwoRootedMajorant P M γ α₁ α₂ α₃ p w ≤
        ENNReal.ofReal (C * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁)) := by
  obtain ⟨Ce, hCe, hext⟩ := twoRooted_exterior_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hp
  obtain ⟨C₀, hC₀, hsp⟩ := twoRooted_annular_spatial_bound P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ p hp
  obtain ⟨C₁, hC₁, hball⟩ := bpzRR_planar_ball_bound γ α₁ α₂ α₃ hγ hlo hα₁
  refine ⟨64 * (Ce + C₀ * C₁), by positivity, ?_⟩
  intro w hw hw4
  have hn  := norm_pos_iff.mpr hw
  have hexp : γ ^ 2 / 2 - γ * α₁ ≤ 0 := by
    have h := mul_lt_mul_of_pos_left hlo hγ
    linarith only [h]
  have hpow : 1 ≤ ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hn (hw4.trans (by norm_num)) hexp
  let Y  := (Ce + C₀ * C₁) * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁)
  have h0 : gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p w
      (Metric.ball (0 : ℂ) (1 / 2))ᶜ ≤ ENNReal.ofReal Y := by
    refine (hext w hw4).trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      Ce ≤ Ce * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁) := le_mul_of_one_le_right hCe.le hpow
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [mul_pos hC₀ hC₁]) (by positivity)
  have h1 : gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p w
      (Metric.ball (0 : ℂ) (1 / 2)) ≤ ENNReal.ofReal Y := by
    refine (hsp w hw4 _ measurableSet_ball (fun x hx => ?_)).trans ?_
    · exact (show ‖x‖ < 1 / 2 by simpa only [Metric.mem_ball, dist_zero_right] using hx).le
    · calc
        _ ≤ ENNReal.ofReal C₀ * ENNReal.ofReal (C₁ * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁)) :=
          mul_le_mul' le_rfl (hball w hw)
        _ = ENNReal.ofReal (C₀ * (C₁ * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁))) :=
          (ENNReal.ofReal_mul hC₀.le).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by
          have hN : 0 ≤ ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁) := by positivity
          calc
            _ = (C₀ * C₁) * ‖w‖ ^ (γ ^ 2 / 2 - γ * α₁) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hCe]) hN)
  let B  := ![(Metric.ball (0 : ℂ) (1 / 2))ᶜ, Metric.ball 0 (1 / 2),
    Metric.ball 0 (1 / 2), Metric.ball 0 (1 / 2)]
  have hB : ∀ i, MeasurableSet (B i) := by
    intro i
    fin_cases i
    · exact measurableSet_ball.compl
    · exact measurableSet_ball
    · exact measurableSet_ball
    · exact measurableSet_ball
  have hcover : ⋃ i, B i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_iUnion]
    by_cases hx : x ∈ Metric.ball (0 : ℂ) (1 / 2)
    · exact ⟨1, hx⟩
    · exact ⟨0, hx⟩
  have hreg : ∀ i, gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p w (B i) ≤
      ENNReal.ofReal Y := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h1
    · exact h1
  calc
    _ ≤ 16 * ∑ i : Fin 4, gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p w (B i) :=
      twoRooted_region_cover P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p w B hB hcover
    _ ≤ 16 * ∑ i : Fin 4, ENNReal.ofReal Y :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => hreg i)
    _ = ENNReal.ofReal (64 * Y) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64), ← mul_assoc]
      norm_num
    _ = _ := by
      congr 1
      ring

/-! ### Integrability of the weighted time integrands -/

section
variable (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ) (hp : 0 ≤ p) (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4)
include hsq hα₁ hp hz hz4

/-- Both two-rooted expectations have integrable weighted time integrands on `[0, 1]`. -/
theorem bpzRR_twoRooted_time_integrable (mixed : Bool) :
    IntegrableOn (fun s : ℝ => ((1 - s : ℝ) : ℂ) *
      gammaHalfTwoRootedSpatial mixed P M γ α₁ α₂ α₃ p ((s : ℂ) * z)) (Icc 0 1) := by
  obtain ⟨C, hC, hI⟩ := bpzRR_majorant_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hlo hα₁ hp
  have he : -1 < γ ^ 2 / 2 - γ * α₁ := by
    linarith only [(fusion_taylor_parameters γ α₁ hγ hlo hsq hα₁).2.2.2.1]
  exact fusion_time_integrable_of_power_bound _
    (bpzRR_twoRooted_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p mixed) C
    (γ ^ 2 / 2 - γ * α₁) (1 / 4) he
    (fun w hw hwr => twoRooted_spatial_norm_le P M γ α₁ α₂ α₃ p w mixed (by positivity) (hI w hw hwr)) z hz hz4

end

end

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ : ℝ)
  (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ)
  (hp : 0 ≤ p) (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4)
include Ω X hX hγ hγ2 hM hlo hsq hα₁ hα₂ hα₃ hp hz hz4

/-- The weighted time integrand of `r₁` is integrable on `[0, 1]`: the local part has the power
bound `‖w‖ ^ (γ² / 2 - γ α₁)` and the exterior part is bounded. -/
theorem bpzRR_oneRooted_pure_time_integrable :
    IntegrableOn (fun s : ℝ => ((1 - s : ℝ) : ℂ) *
      fusionPureSpatial P M γ α₁ α₂ α₃ p univ ((s : ℂ) * z)) (Icc 0 1) volume := by
  exact (fusion_second_time false P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hsq hα₁ hα₂ hα₃ p hp z hz hz4).1

/-- The weighted time integrand of `r₂` is integrable on `[0, 1]`: the local part has the power
bound `‖w‖ ^ (γ² / 2 - γ α₁)` and the exterior part is bounded. -/
theorem bpzRR_oneRooted_mixed_time_integrable :
    IntegrableOn (fun s : ℝ => ((1 - s : ℝ) : ℂ) *
      fusionMixedSpatial P M γ α₁ α₂ α₃ p univ ((s : ℂ) * z)) (Icc 0 1) volume := by
  exact (fusion_second_time true P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hsq hα₁ hα₂ hα₃ p hp z hz hz4).1

end

/-! ### Assembling the remainder -/

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (z : ℂ)
include Ω

/-- The term `r₁` as a weighted time integral of the unrestricted pure spatial expectation. -/
theorem bpzRR_R1_eq :
    gammaHalfRootedR1 P M γ α₁ α₂ α₃ p z =
      ((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) * z ^ 2 *
        ∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) *
          fusionPureSpatial P M γ α₁ α₂ α₃ p univ ((s : ℂ) * z) := by
  simp only [gammaHalfRootedR1, fusionPureSpatial, fusionSecondSpatial, fusionSecondKernel, fusionSecondDenom,
    Bool.false_eq_true, if_false, Measure.restrict_univ,
    ENNReal.rpow_eq_pow]

/-- The term `r₂` as a weighted time integral of the unrestricted mixed spatial expectation. -/
theorem bpzRR_R2_eq :
    gammaHalfRootedR2 P M γ α₁ α₂ α₃ p z =
      ((-2 * p * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) * z * star z *
        ∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) *
          fusionMixedSpatial P M γ α₁ α₂ α₃ p univ ((s : ℂ) * z) := by
  simp only [gammaHalfRootedR2, fusionMixedSpatial, fusionSecondSpatial, fusionSecondKernel, fusionSecondDenom,
    ite_true, Measure.restrict_univ,
    ENNReal.rpow_eq_pow, Complex.ofReal_pow]

end

/-- The Taylor remainder at a real point `t > 0` is `t ^ 2` times the weighted time integral. -/
theorem bpzRR_remainder_eq {t : ℝ} (ht0 : 0 < t) (g2 : ℝ → ℝ) :
    ((∫ u in (0 : ℝ)..t, (t - u) * g2 u : ℝ) : ℂ) =
      ((t ^ 2 : ℝ) : ℂ) * ∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) * (g2 (s * t) : ℂ) := by
  have h := bpz_taylor_remainder_subst_complex (f := fun u => (g2 u : ℂ)) ht0
  rw [← h, ← intervalIntegral.integral_ofReal]
  simp

/-- The one-rooted and two-rooted Taylor terms at a real point `t ∈ (0, 1/4]` add up to the
Taylor remainder `∫ u in 0..t, (t - u) * g2 u` of any function `g2` that on `(0, t]` equals the
six-term expression built from the four rooted expectations and their conjugates. -/
theorem bpz_rootedTerms_eq_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 < α₁)
    (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {p : ℝ}
    (hp : 0 ≤ p) {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 4) {g2 : ℝ → ℝ}
    (hpt : ∀ u : ℝ, 0 < u → u ≤ t → (g2 u : ℂ) = bpzRootedHessian P M γ α₁ α₂ α₃ p (u : ℂ)) :
    gammaHalfOneRootedTerm P M γ α₁ α₂ α₃ p (t : ℂ) +
        gammaHalfTwoRootedTerm P M γ α₁ α₂ α₃ p (t : ℂ) =
      ((∫ u in (0 : ℝ)..t, (t - u) * g2 u : ℝ) : ℂ) := by
  have hz0 := Complex.ofReal_ne_zero.mpr ht0.ne'
  have hz4 : ‖(t : ℂ)‖ ≤ 1 / 4 := by simpa [abs_of_pos ht0] using ht
  have i1 := bpzRR_oneRooted_pure_time_integrable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hsq hα₁
    hα₂ hα₃ p hp (t : ℂ) hz0 hz4
  have i2 := bpzRR_oneRooted_mixed_time_integrable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hsq hα₁
    hα₂ hα₃ p hp (t : ℂ) hz0 hz4
  have i (mixed : Bool) := bpzRR_twoRooted_time_integrable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hlo hsq
    hα₁ hp (t : ℂ) hz0 hz4 mixed
  have e : (∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) * (g2 (s * t) : ℂ)) =
      ∫ s in Icc (0 : ℝ) 1, ((1 - s : ℝ) : ℂ) * bpzRootedHessian P M γ α₁ α₂ α₃ p ((s : ℂ) * t) := by
    apply setIntegral_congr_ae measurableSet_Icc
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with s hs0 hs
    rw [hpt _ (mul_pos (lt_of_le_of_ne hs.1 hs0.symm) ht0) (mul_le_of_le_one_left ht0.le hs.2),
      Complex.ofReal_mul]
  rw [bpzRR_remainder_eq ht0, e]
  simp_rw [bpzRootedHessian, bpzHessianCombination_mul]
  rw [integral_bpzHessianCombination i1 i2 (i false) (i true), bpzHessianCombination_mul]
  simp only [gammaHalfOneRootedTerm, gammaHalfTwoRootedTerm, gammaHalfRootedR3, gammaHalfTwoRootedP3,
    gammaHalfTwoRootedP1, gammaHalfTwoRootedP2, bpzRR_R1_eq, bpzRR_R2_eq, bpzHessianCombination,
    Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow]
  ring

end DOZZ.Proofs
