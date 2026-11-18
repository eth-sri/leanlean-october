/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import GaussianFields.LogCorrelated.ABK.KernelPairing

/-!
# GaussianFields.LogCorrelated/ABK/SingularIntegrability
-/

public section

noncomputable section
open Filter MeasureTheory
open scoped ENNReal Topology

namespace GaussianFields

variable {d : Nat}

private lemma abs_rpow_slope_le {α ρ R : ℝ}
    (hα_pos : 0 < α) (hα_le : α ≤ 1 / 2)
    (hρ_pos : 0 < ρ) (hρR : ρ ≤ R) (hR : 1 ≤ R) :
    |(ρ ^ (-α) - 1) / α| ≤ (4 + Real.log R) * (1 + ρ ^ (-(3 / 4 : ℝ))) := by
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hcoef : 0 ≤ 4 + Real.log R := by linarith
  have hsing : 0 ≤ ρ ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hρ_pos.le _
  by_cases hρ1 : ρ ≤ 1
  · let u := ρ⁻¹
    have hu : 0 < u := inv_pos.2 hρ_pos
    have hu1 : 1 ≤ u := (one_le_inv₀ hρ_pos).2 hρ1
    have hnn : 0 ≤ (ρ ^ (-α) - 1) / α := by
      rw [Real.rpow_neg_eq_inv_rpow]; exact div_nonneg (sub_nonneg.2 (Real.one_le_rpow hu1 hα_pos.le)) hα_pos.le
    rw [abs_of_nonneg hnn, Real.rpow_neg_eq_inv_rpow]
    have hexp : u ^ α - 1 ≤ (α * Real.log u) * u ^ α := by
      rw [Real.rpow_def_of_pos hu]
      have h1 : 1 - Real.exp (-(α * Real.log u)) ≤ α * Real.log u := by
        linarith [Real.add_one_le_exp (-(α * Real.log u))]
      calc Real.exp (Real.log u * α) - 1
        _ = Real.exp (Real.log u * α) * (1 - Real.exp (-(α * Real.log u))) := by
            rw [mul_sub, mul_one, ← Real.exp_add, show Real.log u * α + -(α * Real.log u) = 0 by ring, Real.exp_zero]
        _ ≤ Real.exp (Real.log u * α) * (α * Real.log u) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = (α * Real.log u) * Real.exp (Real.log u * α) := mul_comm _ _
    have hdiv : (u ^ α - 1) / α ≤ Real.log u * u ^ α :=
      (div_le_iff₀ hα_pos).2 (hexp.trans_eq (by ring))
    have hlog_u : Real.log u ≤ 4 * u ^ (1 / 4 : ℝ) :=
      (Real.log_le_rpow_div hu.le (by norm_num : (0 : ℝ) < 1 / 4)).trans_eq (by ring)
    have hmain : (u ^ α - 1) / α ≤ 4 * ρ ^ (-(3 / 4 : ℝ)) := by
      calc (u ^ α - 1) / α ≤ Real.log u * u ^ α := hdiv
        _ ≤ (4 * u ^ (1 / 4 : ℝ)) * u ^ (1 / 2 : ℝ) :=
            mul_le_mul hlog_u (Real.rpow_le_rpow_of_exponent_le hu1 hα_le)
              (Real.rpow_nonneg hu.le _) (by positivity)
        _ = 4 * u ^ (3 / 4 : ℝ) := by
            rw [mul_assoc, ← Real.rpow_add hu]; norm_num
        _ = 4 * ρ ^ (-(3 / 4 : ℝ)) := by dsimp [u]; rw [← Real.rpow_neg_eq_inv_rpow]
    exact hmain.trans ((mul_le_mul_of_nonneg_right (by linarith) hsing).trans
      (mul_le_mul_of_nonneg_left (by linarith) hcoef))
  · have hρ1' : 1 ≤ ρ := le_of_not_ge hρ1
    have hnp : (ρ ^ (-α) - 1) / α ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.2 (Real.rpow_le_one_of_one_le_of_nonpos hρ1' (neg_nonpos.2 hα_pos.le))) hα_pos.le
    rw [abs_of_nonpos hnp, show -((ρ ^ (-α) - 1) / α) = (1 - ρ ^ (-α)) / α by ring]
    have hsub : 1 - ρ ^ (-α) ≤ α * Real.log ρ := by
      have := Real.add_one_le_exp (-(α * Real.log ρ))
      rw [Real.rpow_def_of_pos hρ_pos, show Real.log ρ * -α = -(α * Real.log ρ) by ring]; linarith
    calc (1 - ρ ^ (-α)) / α ≤ Real.log ρ := (div_le_iff₀ hα_pos).2 (hsub.trans_eq (mul_comm _ _))
      _ ≤ Real.log R := Real.log_le_log hρ_pos hρR
      _ ≤ 4 + Real.log R := by linarith
      _ ≤ (4 + Real.log R) * (1 + ρ ^ (-(3 / 4 : ℝ))) := le_mul_of_one_le_right hcoef (by linarith)

private def boxInd (R : ℝ) (x : Vec d) : ℝ :=
  ∏ j : Fin d, (Set.Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ)) (x j)

private def boxSing (i : Fin d) (R : ℝ) (x : Vec d) : ℝ :=
  ∏ j : Fin d, if j = i then (Set.Icc (-R) R).indicator (fun t : ℝ => |t| ^ (-(3 / 4 : ℝ))) (x j)
    else (Set.Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ)) (x j)

section
variable (hd : 0 < d) (ψ φ : MeanZeroTestFunction d)
include hd ψ φ

private lemma aestronglyMeasurable_slope_integrand
    {α : ℝ} (hα : α ≠ 0) :
    AEStronglyMeasurable (fun p : Vec d × Vec d => ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2)
      ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) := by
  let s : Set (Vec d × Vec d) := {p | p.1 ≠ p.2}
  have hs : MeasurableSet s := (isClosed_eq continuous_fst continuous_snd).measurableSet.compl
  have hpow : ContinuousOn (fun p : Vec d × Vec d => euclideanNorm (p.1 - p.2) ^ (-α)) s :=
    ((continuous_euclideanNorm (d := d)).comp (continuous_fst.sub continuous_snd)).continuousOn.rpow_const
      fun p hp => Or.inl (abkEuclideanNorm_pos_of_ne_zero (sub_ne_zero.2 hp)).ne'
  have hcont : ContinuousOn (fun p : Vec d × Vec d => ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2) s :=
    (((ψ.continuous.comp continuous_fst).continuousOn).mul ((φ.continuous.comp continuous_snd).continuousOn)).mul
      ((hpow.sub continuousOn_const).div continuousOn_const fun _ _ => hα)
  have hsm := hcont.aestronglyMeasurable (μ := (volume : Measure (Vec d)).prod volume) hs
  have hfull : ∀ᵐ p : Vec d × Vec d ∂(volume : Measure (Vec d)).prod volume, p ∈ s := ae_fst_ne_snd_volume_prod hd
  rwa [Measure.restrict_eq_self_of_ae_mem hfull] at hsm

private lemma exists_slope_majorant_uniform :
    ∃ bound : Vec d × Vec d → ℝ,
      Integrable bound ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) ∧
      ∀ {α : ℝ}, 0 < α → α ≤ 1 / 2 →
        ∀ᵐ p : Vec d × Vec d ∂((volume : Measure (Vec d)).prod (volume : Measure (Vec d))),
          ‖ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2‖ ≤ bound p := by
  let i : Fin d := ⟨0, hd⟩
  obtain ⟨Rψ, _, hψ_supp₀⟩ := exists_support_subset_euclideanClosedBall_meanZeroTestFunction ψ
  obtain ⟨Rφ, _, hφ_supp₀⟩ := exists_support_subset_euclideanClosedBall_meanZeroTestFunction φ
  obtain ⟨Mψ, hMψ_nn, hψ_bd⟩ := exists_abs_meanZeroTestFunction_le ψ
  obtain ⟨Mφ, hMφ_nn, hφ_bd⟩ := exists_abs_meanZeroTestFunction_le φ
  let R := max 1 (max Rψ Rφ)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  have h2R0 : 0 ≤ 2 * R := by positivity
  have hψ_supp : Function.support ψ ⊆ {x | euclideanNorm x ≤ R} :=
    fun _ hx => (hψ_supp₀ hx).trans ((le_max_left Rψ Rφ).trans (le_max_right 1 (max Rψ Rφ)))
  have hφ_supp : Function.support φ ⊆ {x | euclideanNorm x ≤ R} :=
    fun _ hx => (hφ_supp₀ hx).trans ((le_max_right Rψ Rφ).trans (le_max_right 1 (max Rψ Rφ)))
  let C := Mψ * Mφ * (4 + Real.log (2 * R))
  let Bmaj (p : Vec d × Vec d) := boxInd (2 * R) (p.1 - p.2) * boxInd R p.2
  let Smaj (p : Vec d × Vec d) := boxSing i (2 * R) (p.1 - p.2) * boxInd R p.2
  -- 1D integrability
  have hint_1 (S : ℝ) : Integrable ((Set.Icc (-S) S).indicator (fun _ : ℝ => (1 : ℝ))) volume :=
    continuousOn_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hint_s (S : ℝ) (hS : 0 ≤ S) :
      Integrable ((Set.Icc (-S) S).indicator (fun t : ℝ => |t| ^ (-(3 / 4 : ℝ)))) volume := by
    have hp_iv : IntervalIntegrable (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) volume 0 S :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have hp_on : IntegrableOn (fun x : ℝ => |x| ^ (-(3 / 4 : ℝ))) (Set.Icc 0 S) volume :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hS).1 hp_iv).congr_fun
        (fun x hx => by simp [abs_of_nonneg hx.1]) measurableSet_Icc
    have hn_iv : IntervalIntegrable (fun x : ℝ => (-x) ^ (-(3 / 4 : ℝ))) volume (-S) 0 := by
      simpa using ((IntervalIntegrable.iff_comp_neg (f := fun x : ℝ => x ^ (-(3 / 4 : ℝ))) (a := 0) (b := S)).1 hp_iv).symm
    have hn_on : IntegrableOn (fun x : ℝ => |x| ^ (-(3 / 4 : ℝ))) (Set.Icc (-S) 0) volume :=
      ((intervalIntegrable_iff_integrableOn_Icc_of_le (neg_nonpos.2 hS)).1 hn_iv).congr_fun
        (fun x hx => by simp [abs_of_nonpos hx.2]) measurableSet_Icc
    have hu : IntegrableOn (fun x : ℝ => |x| ^ (-(3 / 4 : ℝ))) (Set.Icc (-S) S) volume := by
      rw [← Set.Icc_union_Icc_eq_Icc (neg_nonpos.2 hS) hS]; exact hn_on.union hp_on
    exact hu.integrable_indicator measurableSet_Icc
  have hint_ind (S : ℝ) : Integrable (boxInd (d := d) S) volume :=
    Integrable.fintype_prod fun _ => hint_1 S
  have hint_sing (S : ℝ) (hS : 0 ≤ S) : Integrable (boxSing i S) volume := by
    let f : Fin d → ℝ → ℝ := fun j x =>
      if j = i then (Set.Icc (-S) S).indicator (fun t : ℝ => |t| ^ (-(3 / 4 : ℝ))) x
      else (Set.Icc (-S) S).indicator (fun _ : ℝ => (1 : ℝ)) x
    have hf : ∀ j, Integrable (f j) volume := fun j => by
      by_cases hj : j = i
      · subst hj; simpa [f] using hint_s S hS
      · simpa [f, hj] using hint_1 S
    rw [MeasureTheory.volume_pi]; unfold boxSing
    simpa only [f] using Integrable.fintype_prod hf
  let μ := (volume : Measure (Vec d)).prod (volume : Measure (Vec d))
  have hT : MeasurePreserving (fun p : Vec d × Vec d => (p.1 - p.2, p.2)) μ μ :=
    measurePreserving_sub_prod volume volume
  have hB_int : Integrable Bmaj μ :=
    hT.integrable_comp_of_integrable ((hint_ind (2 * R)).mul_prod (hint_ind R))
  have hS_int : Integrable Smaj μ :=
    hT.integrable_comp_of_integrable ((hint_sing (2 * R) h2R0).mul_prod (hint_ind R))
  have hae_coord : ∀ᵐ p : Vec d × Vec d ∂μ, (p.1 - p.2) i ≠ 0 := by
    have hc : ∀ᵐ v : Vec d ∂volume, v i ≠ 0 := by
      simpa [MeasureTheory.volume_pi] using Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i (0 : ℝ)
    have hm : MeasurableSet {q : Vec d × Vec d | q.1 i ≠ 0} :=
      (isClosed_eq ((continuous_apply i).comp continuous_fst) continuous_const).measurableSet.compl
    have hpr : ∀ᵐ q : Vec d × Vec d ∂μ, q.1 i ≠ 0 := by
      rw [Measure.ae_prod_iff_ae_ae hm]
      exact hc.mono fun _ hv => Eventually.of_forall fun _ => hv
    exact hT.quasiMeasurePreserving.ae hpr
  refine ⟨fun p => C * (Bmaj p + Smaj p), (hB_int.add hS_int).const_mul C, fun {α} hα_pos hα_le => ?_⟩
  filter_upwards [hae_coord] with p hp_c
  have h2R1 : 1 ≤ 2 * R := by linarith
  have hC_nn : 0 ≤ C := mul_nonneg (mul_nonneg hMψ_nn hMφ_nn) (by linarith [Real.log_nonneg h2R1])
  have hInd_nn (S : ℝ) (x : Vec d) : 0 ≤ boxInd S x := Finset.prod_nonneg fun j _ => by
    by_cases hx : x j ∈ Set.Icc (-S) S <;> simp [hx]
  have hSing_nn (S : ℝ) (x : Vec d) : 0 ≤ boxSing i S x := Finset.prod_nonneg fun j _ => by
    by_cases hj : j = i
    · rw [ite_eq_left hj]
      by_cases hx : x j ∈ Set.Icc (-S) S
      · rw [Set.indicator_of_mem hx]; exact Real.rpow_nonneg (abs_nonneg _) _
      · rw [Set.indicator_of_notMem hx]
    · rw [ite_eq_right hj]
      by_cases hx : x j ∈ Set.Icc (-S) S <;> simp [hx]
  have hsum_nn : 0 ≤ Bmaj p + Smaj p :=
    add_nonneg (mul_nonneg (hInd_nn _ _) (hInd_nn _ _)) (mul_nonneg (hSing_nn _ _) (hInd_nn _ _))
  by_cases hψ0 : ψ p.1 = 0
  · simp [hψ0]; exact mul_nonneg hC_nn hsum_nn
  by_cases hφ0 : φ p.2 = 0
  · simp [hφ0]; exact mul_nonneg hC_nn hsum_nn
  have hx_n : euclideanNorm p.1 ≤ R := hψ_supp hψ0
  have hy_n : euclideanNorm p.2 ≤ R := hφ_supp hφ0
  have hρ_le : euclideanNorm (p.1 - p.2) ≤ 2 * R := by
    calc euclideanNorm (p.1 - p.2) = euclideanNorm (p.1 + -p.2) := by rw [sub_eq_add_neg]
      _ ≤ euclideanNorm p.1 + euclideanNorm p.2 :=
          (euclideanNorm_add_le _ _).trans_eq (by rw [euclideanNorm_neg])
      _ ≤ 2 * R := by linarith
  have hy_b (j : Fin d) : p.2 j ∈ Set.Icc (-R) R :=
    abs_le.1 ((abs_apply_le_euclideanNorm p.2 j).trans hy_n)
  have hd_b (j : Fin d) : (p.1 - p.2) j ∈ Set.Icc (-(2 * R)) (2 * R) :=
    abs_le.1 ((abs_apply_le_euclideanNorm (p.1 - p.2) j).trans hρ_le)
  have hInd1 (S : ℝ) (x : Vec d) (hx : ∀ j, x j ∈ Set.Icc (-S) S) : boxInd S x = 1 :=
    Finset.prod_eq_one fun j _ => Set.indicator_of_mem (hx j) _
  have hBeq : Bmaj p = 1 := by dsimp [Bmaj]; rw [hInd1 _ _ hd_b, hInd1 _ _ hy_b, mul_one]
  have hSeq : Smaj p = |(p.1 - p.2) i| ^ (-(3 / 4 : ℝ)) := by
    dsimp [Smaj]; rw [hInd1 _ _ hy_b, mul_one]; unfold boxSing
    rw [Fintype.prod_eq_single i (fun j hji => by rw [ite_eq_right hji, Set.indicator_of_mem (hd_b j)]),
      ite_eq_left rfl, Set.indicator_of_mem (hd_b i)]; rfl
  have hρ_pos := abkEuclideanNorm_pos_of_ne_zero fun (hz : p.1 - p.2 = 0) => hp_c (by rw [hz]; rfl)
  have hsl := abs_rpow_slope_le hα_pos hα_le hρ_pos hρ_le h2R1
  have hsing_le : euclideanNorm (p.1 - p.2) ^ (-(3 / 4 : ℝ)) ≤ |(p.1 - p.2) i| ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (abs_pos.2 hp_c) (abs_apply_le_euclideanNorm (p.1 - p.2) i) (by norm_num)
  have hψn : ‖ψ p.1‖ ≤ Mψ := by simpa [Real.norm_eq_abs] using hψ_bd p.1
  have hφn : ‖φ p.2‖ ≤ Mφ := by simpa [Real.norm_eq_abs] using hφ_bd p.2
  rw [hBeq, hSeq]
  refine norm_mul₃_le.trans ?_
  calc ‖ψ p.1‖ * ‖φ p.2‖ * ‖abkCenteredRieszSlopeKernel α p.1 p.2‖
    _ ≤ (Mψ * Mφ) * ((4 + Real.log (2 * R)) * (1 + euclideanNorm (p.1 - p.2) ^ (-(3 / 4 : ℝ)))) :=
        mul_le_mul (mul_le_mul hψn hφn (norm_nonneg _) hMψ_nn) hsl (norm_nonneg _) (mul_nonneg hMψ_nn hMφ_nn)
    _ = C * (1 + euclideanNorm (p.1 - p.2) ^ (-(3 / 4 : ℝ))) := by dsimp [C]; ring
    _ ≤ C * (1 + |(p.1 - p.2) i| ^ (-(3 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hsing_le) hC_nn

/-- Concrete integrable dominated-convergence majorant for the centered Riesz slope
integrands associated to two ABK test functions. -/
theorem exists_integrable_bound_abkCenteredRieszSlopeKernel_integrand
 :
    ∃ bound : Vec d × Vec d → ℝ,
      Integrable bound ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) ∧
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        ∀ᵐ p : Vec d × Vec d ∂((volume : Measure (Vec d)).prod (volume : Measure (Vec d))),
          ‖ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2‖ ≤ bound p := by
  obtain ⟨bound, hint, hbd⟩ := exists_slope_majorant_uniform hd ψ φ
  exact ⟨bound, hint, Filter.mem_of_superset (Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2))
    fun _ hα => hbd hα.1 hα.2⟩

/-- For each fixed small positive `α`, the centered Riesz slope integrand is integrable. -/
theorem integrable_abkCenteredRieszSlopeKernel_integrand_of_pos_le_half
 {α : ℝ}
    (hα_pos : 0 < α) (hα_le : α ≤ 1 / 2) :
    Integrable
      (fun p : Vec d × Vec d => ψ p.1 * φ p.2 * abkCenteredRieszSlopeKernel α p.1 p.2)
      ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) := by
  obtain ⟨bound, hint, hbd⟩ := exists_slope_majorant_uniform hd ψ φ
  exact hint.mono' (aestronglyMeasurable_slope_integrand hd ψ φ hα_pos.ne') (hbd hα_pos hα_le)

/-- For each fixed small positive `α`, the Riesz kernel integrand is integrable. -/
theorem integrable_abkRieszKernel_integrand_of_pos_le_half
 {α : ℝ}
    (hα_pos : 0 < α) (hα_le : α ≤ 1 / 2) :
    Integrable
      (fun p : Vec d × Vec d => ψ p.1 * φ p.2 * abkRieszKernel α p.1 p.2)
      ((volume : Measure (Vec d)).prod (volume : Measure (Vec d))) := by
  refine (((integrable_abkCenteredRieszSlopeKernel_integrand_of_pos_le_half hd ψ φ hα_pos hα_le).const_mul α).add
    (integrable_abkKernelPairing_const_one ψ φ)).congr (ae_of_all _ fun p => ?_)
  dsimp [abkCenteredRieszSlopeKernel, abkRieszKernel]
  field_simp [hα_pos.ne']; ring


end
/-- The ABK reciprocal normalization times the centered Riesz difference pairing converges to
the logarithmic covariance pairing with the `M₀` prefactor. -/
theorem tendsto_abkMAlphaInv_mul_centeredRieszDifferencePairing
    (hd : 0 < d) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) :
    Tendsto
      (fun α : ℝ => abkMAlphaInv ζ α * abkCenteredRieszDifferencePairing ψ φ α)
      (𝓝[>] (0 : ℝ))
      (𝓝 (abkM0 ζ * abkLogCovariancePairing ψ φ)) := by
  obtain ⟨bound, hint, hbd⟩ := exists_integrable_bound_abkCenteredRieszSlopeKernel_integrand hd ψ φ
  exact tendsto_abkMAlphaInv_mul_centeredRieszDifferencePairing_of_dominated hd ζ ψ φ bound
    (Filter.mem_of_superset self_mem_nhdsWithin fun _ hα =>
      aestronglyMeasurable_slope_integrand hd ψ φ (Set.mem_Ioi.1 hα).ne') hbd hint

end GaussianFields

end
