/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Complex.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.MeanInequalities
public import DOZZ.Complex.Weierstrass

/-!
# Holomorphic Gaussian charge moments
-/

@[expose] public section

open MeasureTheory Filter Topology Set Complex ProbabilityTheory
open scoped Real

namespace DOZZ.Proofs

variable {N : ℕ}


private noncomputable def chargeLinear (l : Fin N → ℝ) (a : ℝ)
    (sL : (Fin N → ℂ) →L[ℂ] ℂ) : (Fin N → ℂ) →L[ℂ] ℂ :=
  (∑ i, (l i : ℂ) • (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ)) - (a : ℂ) • sL

private noncomputable def chargeKernel (s₀ : ℂ) (sL : (Fin N → ℂ) →L[ℂ] ℂ)
    (l : Fin N → ℝ) (A : ℝ) (z : Fin N → ℂ) : ℂ :=
  exp (∑ i, z i * (l i : ℂ)) * (A : ℂ) ^ (-(s₀ + sL z))

/-- The norm of a positive real base to a complex power is its real power. -/
theorem norm_cpow_positive (A : ℝ) (hA : 0 < A) (s : ℂ) :
    ‖(A : ℂ) ^ s‖ = A ^ s.re := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hA.ne'), norm_exp, ← ofReal_log hA.le,
    mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, Real.rpow_def_of_pos hA]


/-- Proof of `DOZZ.differentiableOn_gaussian_charge_moment`: the Gaussian charge moment, allowing
correlation with the positive mass. -/
theorem differentiableOn_gaussian_charge_moment {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set (Fin N → ℂ)) (hU : IsOpen U)
    (L : Ω → Fin N → ℝ) (hL : ProbabilityTheory.HasGaussianLaw L P)
    (A : Ω → ℝ) (hA : AEMeasurable A P) (hpos : ∀ᵐ ω ∂P, 0 < A ω)
    (pstar : ℝ) (_hpstar : 0 < pstar)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => A ω ^ (-q)) P)
    (hmom : ∀ p : ℝ, 0 ≤ p → p < pstar → Integrable (fun ω => A ω ^ p) P)
    (c : (Fin N → ℂ) → ℂ) (hc : DifferentiableOn ℂ c U)
    (s₀ : ℂ) (sL : (Fin N → ℂ) →L[ℂ] ℂ) :
    (∀ z ∈ {z ∈ U | -(s₀ + sL z).re < pstar},
      Integrable (fun ω => Complex.exp (c z + ∑ i, z i * (L ω i : ℂ)) *
        (A ω : ℂ) ^ (-(s₀ + sL z))) P) ∧
    DifferentiableOn ℂ
      (fun z => ∫ ω, Complex.exp (c z + ∑ i, z i * (L ω i : ℂ)) *
        (A ω : ℂ) ^ (-(s₀ + sL z)) ∂P)
      {z ∈ U | -(s₀ + sL z).re < pstar} := by
  have norm_chargeKernel_le (l : Fin N → ℝ) {A : ℝ} (hA : 0 < A) (z : Fin N → ℂ) {K u v : ℝ} (hK : ‖z‖ ≤ K) (hu : u ≤ -(s₀ + sL z).re) (hv : -(s₀ + sL z).re ≤ v) : ‖chargeKernel s₀ sL l A z‖ ≤ Real.exp (K * ∑ i, |l i|) * (A ^ u + A ^ v) := by
    have hexp : ‖exp (∑ i, z i * (l i : ℂ))‖ ≤ Real.exp (K * ∑ i, |l i|) := by
      rw [norm_exp, Finset.mul_sum]
      refine Real.exp_le_exp.2 ?_
      change Complex.reCLM (∑ i, z i * (l i : ℂ)) ≤ _
      rw [map_sum]
      exact Finset.sum_le_sum fun i _ => ((re_le_norm _).trans_eq
        (by rw [norm_mul, norm_real, Real.norm_eq_abs])).trans
        (mul_le_mul_of_nonneg_right ((norm_le_pi_norm z i).trans hK) (abs_nonneg _))
    have hrpow : A ^ (-(s₀ + sL z)).re ≤ A ^ u + A ^ v := by
      rw [neg_re]
      by_cases h1 : 1 ≤ A
      · exact (Real.rpow_le_rpow_of_exponent_le h1 hv).trans (le_add_of_nonneg_left (Real.rpow_pos_of_pos hA u).le)
      · exact (Real.rpow_le_rpow_of_exponent_ge hA (le_of_not_ge h1) hu).trans
          (le_add_of_nonneg_right (Real.rpow_pos_of_pos hA v).le)
    unfold chargeKernel
    rw [norm_mul, norm_cpow_positive A hA]
    exact mul_le_mul hexp hrpow (by positivity) (Real.exp_nonneg _)
  let _ := hL.isGaussian_map
  obtain ⟨Cg, hCg, hint_sq⟩ := IsGaussian.exists_integrable_exp_sq (P.map L)
  have hgauss_sq : Integrable (fun ω => Real.exp (Cg * ‖L ω‖ ^ 2)) P :=
    (integrable_map_measure (by fun_prop) hL.aemeasurable).mp hint_sq
  have hsum_ae : AEMeasurable (fun ω => ∑ i, |L ω i|) P :=
    Finset.aemeasurable_fun_sum Finset.univ fun i _ => by
      have hi : AEMeasurable (fun ω => L ω i) P := (measurable_pi_apply i).comp_aemeasurable hL.aemeasurable
      simpa only [Real.norm_eq_abs] using hi.norm
  have hexp_sum (K : ℝ) (hK : 0 ≤ K) : Integrable (fun ω => Real.exp (K * ∑ i, |L ω i|)) P := by
    have hnorm : Integrable (fun ω => Real.exp ((K * N) * ‖L ω‖)) P :=
      (hgauss_sq.const_mul (Real.exp ((K * N) ^ 2 / (4 * Cg)))).mono'
        ((hL.aemeasurable.norm.const_mul _).exp.aestronglyMeasurable)
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
          refine Real.exp_le_exp.2 ((mul_le_mul_iff_right₀ (by positivity : 0 < 4 * Cg)).1 ?_)
          rw [show (4 * Cg) * ((K * N) ^ 2 / (4 * Cg) + Cg * ‖L ω‖ ^ 2) =
            (K * N) ^ 2 + 4 * Cg ^ 2 * ‖L ω‖ ^ 2 by field_simp]
          nlinarith [sq_nonneg (2 * Cg * ‖L ω‖ - K * N)])
    refine hnorm.mono' ((hsum_ae.const_mul K).exp.aestronglyMeasurable) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have hs : ∑ i, |L ω i| ≤ (N : ℝ) * ‖L ω‖ :=
      (Finset.sum_le_sum fun i _ => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (L ω) i).trans_eq (by simp)
    nlinarith
  have hexp_mass {K t : ℝ} (hK : 0 ≤ K) (ht : t < pstar) :
      Integrable (fun ω => Real.exp (K * ∑ i, |L ω i|) * A ω ^ t) P := by
    have hn := (continuous_id.mul continuous_const).continuousAt.preimage_mem_nhds
      (isOpen_Iio.mem_nhds (show (1 : ℝ) * t ∈ Iio pstar by simpa using ht))
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hn
    let p := 1 + ε / 2
    have hp1 : 1 < p := by dsimp [p]; linarith
    have hpt : p * t < pstar := hb (by
      rw [Metric.mem_ball, Real.dist_eq, show p - 1 = ε / 2 by dsimp [p]; ring, abs_of_pos (half_pos hε)]
      exact half_lt_self hε)
    have hAp : Integrable (fun ω => A ω ^ (p * t)) P := by
      by_cases h0 : 0 ≤ p * t
      · exact hmom _ h0 hpt
      · simpa only [neg_neg] using hinv (-(p * t)) (neg_pos.2 (lt_of_not_ge h0))
    have hpq := Real.HolderConjugate.conjExponent hp1
    have hg := hexp_sum (K * Real.conjExponent p) (mul_nonneg hK hpq.symm.nonneg)
    refine ((hAp.div_const p).add (hg.div_const (Real.conjExponent p))).mono'
      (((hsum_ae.const_mul K).exp.mul (hA.pow_const t)).aestronglyMeasurable) ?_
    filter_upwards [hpos] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hω.le _))]
    have hy := Real.young_inequality_of_nonneg (Real.rpow_nonneg hω.le t) (Real.exp_nonneg (K * ∑ i, |L ω i|)) hpq
    rw [← Real.rpow_mul hω.le, ← Real.exp_mul, mul_comm t p,
      show (K * ∑ i, |L ω i|) * Real.conjExponent p = K * Real.conjExponent p * ∑ i, |L ω i| by ring] at hy
    simpa only [Pi.add_apply, Pi.div_apply, mul_comm (A ω ^ t)] using hy
  have hK_meas (z : Fin N → ℂ) : AEStronglyMeasurable (fun ω => chargeKernel s₀ sL (L ω) (A ω) z) P := by
    have hcoord (i : Fin N) : AEMeasurable (fun ω => (L ω i : ℂ)) P :=
      Complex.continuous_ofReal.measurable.comp_aemeasurable ((measurable_pi_apply i).comp_aemeasurable hL.aemeasurable)
    have he := Complex.continuous_exp.measurable.comp_aemeasurable
      ((Finset.aemeasurable_fun_sum Finset.univ fun i _ => (hcoord i).const_mul (z i)).sub
        ((Complex.continuous_ofReal.measurable.comp_aemeasurable hA.log).const_mul (s₀ + sL z)))
    refine he.aestronglyMeasurable.congr (hpos.mono fun ω hω => ?_)
    change exp ((∑ i, z i * (L ω i : ℂ)) - (s₀ + sL z) * (Real.log (A ω) : ℂ)) =
      chargeKernel s₀ sL (L ω) (A ω) z
    unfold chargeKernel
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 hω.ne'), ← ofReal_log hω.le, ← exp_add]
    congr 1; ring
  have hL_meas : AEStronglyMeasurable (fun ω => chargeLinear (L ω) (Real.log (A ω)) sL) P :=
    (Finset.aestronglyMeasurable_fun_sum Finset.univ fun i _ =>
      ((Complex.continuous_ofReal.measurable.comp_aemeasurable
        ((measurable_pi_apply i).comp_aemeasurable hL.aemeasurable)).aestronglyMeasurable).smul
          aestronglyMeasurable_const).sub
      (((Complex.continuous_ofReal.measurable.comp_aemeasurable hA.log).aestronglyMeasurable).smul
        aestronglyMeasurable_const)
  have hK_int {z : Fin N → ℂ} (hz : -(s₀ + sL z).re < pstar) :
      Integrable (fun ω => chargeKernel s₀ sL (L ω) (A ω) z) P :=
    ((hexp_mass (norm_nonneg z) hz).const_mul 2).mono' (hK_meas z) (hpos.mono fun ω hω => by
      have hb := norm_chargeKernel_le (L ω) hω z le_rfl le_rfl le_rfl
      linarith)
  refine ⟨fun z hz => ((hK_int hz.2).const_mul (exp (c z))).congr
    (Eventually.of_forall fun ω => by
      show exp (c z) * chargeKernel s₀ sL (L ω) (A ω) z =
        exp (c z + ∑ i, z i * (L ω i : ℂ)) * (A ω : ℂ) ^ (-(s₀ + sL z))
      unfold chargeKernel; rw [exp_add, mul_assoc]), ?_⟩
  have hfac : (fun z => ∫ ω, exp (c z + ∑ i, z i * (L ω i : ℂ)) * (A ω : ℂ) ^ (-(s₀ + sL z)) ∂P) =
      fun z => exp (c z) * ∫ ω, chargeKernel s₀ sL (L ω) (A ω) z ∂P := by
    ext z; rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun ω => by
      show exp (c z + ∑ i, z i * (L ω i : ℂ)) * (A ω : ℂ) ^ (-(s₀ + sL z)) =
        exp (c z) * chargeKernel s₀ sL (L ω) (A ω) z
      unfold chargeKernel; rw [exp_add, mul_assoc])
  rw [hfac]
  refine (hc.mono fun _ hz => hz.1).cexp.mul fun a ha => ?_
  let t := -(s₀ + sL a).re
  let δ := (pstar - t) / 2
  have : 0 < δ := half_pos (sub_pos.2 ha.2)
  let u := t - δ
  let v := t + δ
  let K := ‖a‖ + 1
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hv : v < pstar := by dsimp [v, δ]; linarith [ha.2]
  have hu : u < pstar := by dsimp [u, δ]; linarith [ha.2]
  let W := U ∩ (fun z => -(s₀ + sL z).re) ⁻¹' Ioo u v ∩ (fun z => ‖z‖) ⁻¹' Iio K
  have hW : IsOpen W := (hU.inter (isOpen_Ioo.preimage (by fun_prop))).inter (isOpen_Iio.preimage continuous_norm)
  have haW : a ∈ W := ⟨⟨ha.1, by change u < t ∧ t < v; dsimp [u, v, t]; constructor <;> linarith⟩,
    by change ‖a‖ < K; dsimp [K]; linarith⟩
  -- Integrability of envelope `(1 + ‖sL‖) * exp(K ∑ |L|) * (A^u + A^v) * (1 + ∑ |L| + |log A|)`
  have henv_one {r : ℝ} (hr : r < pstar) :
      Integrable (fun ω => Real.exp (K * ∑ i, |L ω i|) * A ω ^ r *
        (1 + ∑ i, |L ω i| + |Real.log (A ω)|)) P := by
    let η := (pstar - r) / 2
    have hη : 0 < η := half_pos (sub_pos.2 hr)
    have h1 := hexp_mass hK0 hr
    have h2 : Integrable (fun ω => Real.exp (K * ∑ i, |L ω i|) * A ω ^ r * (∑ i, |L ω i|)) P :=
      (hexp_mass (by positivity : 0 ≤ K + 1) hr).mono'
        ((((hsum_ae.const_mul K).exp.mul (hA.pow_const r)).mul hsum_ae).aestronglyMeasurable)
        (hpos.mono fun ω hω => by
          change ‖Real.exp (K * ∑ i, |L ω i|) * A ω ^ r * (∑ i, |L ω i|)‖ ≤
            Real.exp ((K + 1) * ∑ i, |L ω i|) * A ω ^ r
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), add_mul K 1, one_mul, Real.exp_add]
          have hs : (∑ i, |L ω i|) ≤ Real.exp (∑ i, |L ω i|) :=
            (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
          nlinarith [mul_nonneg (Real.exp_nonneg (K * ∑ i, |L ω i|)) (Real.rpow_nonneg hω.le r)])
    have h3 : Integrable (fun ω => Real.exp (K * ∑ i, |L ω i|) * A ω ^ r * |Real.log (A ω)|) P :=
      (((hexp_mass hK0 (by dsimp [η]; linarith : r + η < pstar)).add
        (hexp_mass hK0 (by dsimp [η]; linarith : r - η < pstar))).const_mul η⁻¹).mono'
        ((((hsum_ae.const_mul K).exp.mul (hA.pow_const r)).mul
          (by simpa only [Real.norm_eq_abs] using hA.log.norm)).aestronglyMeasurable)
        (hpos.mono fun ω hω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          have hlog : |Real.log (A ω)| ≤ η⁻¹ * (A ω ^ η + A ω ^ (-η)) := by
            have he1 : η * |Real.log (A ω)| ≤ A ω ^ η + A ω ^ (-η) := by
              refine ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)).trans ?_
              rw [Real.rpow_def_of_pos hω, Real.rpow_def_of_pos hω]
              by_cases hl : 0 ≤ Real.log (A ω)
              · rw [abs_of_nonneg hl, mul_comm]; exact le_add_of_nonneg_right (Real.exp_nonneg _)
              · rw [abs_of_neg (lt_of_not_ge hl), show η * -Real.log (A ω) = Real.log (A ω) * -η by ring]
                exact le_add_of_nonneg_left (Real.exp_nonneg _)
            simpa only [← mul_assoc, inv_mul_cancel₀ hη.ne', one_mul] using
              mul_le_mul_of_nonneg_left he1 (inv_nonneg.2 hη.le)
          have hm := mul_le_mul_of_nonneg_left hlog
            (mul_nonneg (Real.exp_nonneg (K * ∑ i, |L ω i|)) (Real.rpow_nonneg hω.le r))
          dsimp only [Pi.add_apply]
          rw [Real.rpow_add hω, sub_eq_add_neg, Real.rpow_add hω]
          linarith)
    exact ((h1.add h2).add h3).congr (Eventually.of_forall fun ω => by simp only [Pi.add_apply]; ring)
  let bound (ω : Ω) := (1 + ‖sL‖) * (Real.exp (K * ∑ i, |L ω i|) * (A ω ^ u + A ω ^ v) *
    (1 + ∑ i, |L ω i| + |Real.log (A ω)|))
  have hb_int : Integrable bound P :=
    (((henv_one hu).add (henv_one hv)).const_mul (1 + ‖sL‖)).congr
      (Eventually.of_forall fun ω => by dsimp only [bound, Pi.add_apply]; ring)
  let F' (z : Fin N → ℂ) (ω : Ω) : (Fin N → ℂ) →L[ℂ] ℂ :=
    chargeKernel s₀ sL (L ω) (A ω) z • chargeLinear (L ω) (Real.log (A ω)) sL
  have hF'_meas : AEStronglyMeasurable (F' a) P := (hK_meas a).smul hL_meas
  have hhd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z ω => chargeKernel s₀ sL (L ω) (A ω) z) (F' := F') (s := W) (hW.mem_nhds haW)
    (eventually_of_mem (hW.mem_nhds haW) fun z _ => hK_meas z) (hK_int ha.2)
    hF'_meas
    (hpos.mono fun ω hω z hz => by
      dsimp only [F', bound]
      rw [norm_smul]
      have hlin_le : ‖chargeLinear (L ω) (Real.log (A ω)) sL‖ ≤
          (1 + ‖sL‖) * (1 + ∑ i, |L ω i| + |Real.log (A ω)|) := by
        have h1 : ‖chargeLinear (L ω) (Real.log (A ω)) sL‖ ≤ (∑ i, |L ω i|) + ‖sL‖ * |Real.log (A ω)| := by
          refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
          · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            rw [norm_smul, norm_real]
            exact (mul_le_of_le_one_right (abs_nonneg _) (norm_coordinate_proj_le_one i))
          · rw [norm_smul, norm_real, Real.norm_eq_abs, mul_comm]
        have : 0 ≤ ∑ i, |L ω i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        nlinarith [norm_nonneg sL, abs_nonneg (Real.log (A ω))]
      have hker := norm_chargeKernel_le (L ω) hω z hz.2.le hz.1.2.1.le hz.1.2.2.le
      exact (mul_le_mul hker hlin_le (norm_nonneg _) (by positivity)).trans_eq (by ring))
    hb_int
    (hpos.mono fun ω hω z _ => by
      have heq : chargeKernel s₀ sL (L ω) (A ω) = fun w =>
          exp (chargeLinear (L ω) (Real.log (A ω)) sL w - s₀ * (Real.log (A ω) : ℂ)) := by
        ext w
        unfold chargeKernel
        rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 hω.ne'), ← ofReal_log hω.le, ← exp_add]
        congr 1
        unfold chargeLinear
        simp only [sub_apply, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
        rw [show (∑ i, (L ω i : ℂ) * w i) = ∑ i, w i * (L ω i : ℂ) from
          Finset.sum_congr rfl fun _ _ => mul_comm _ _]
        ring
      rw [heq]
      convert ((chargeLinear (L ω) (Real.log (A ω)) sL).hasFDerivAt (x := z).sub_const _).cexp using 1
      dsimp only [F']; rw [heq])
  exact hhd.differentiableAt.differentiableWithinAt

end DOZZ.Proofs
