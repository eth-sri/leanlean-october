/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Complex.Identity
public import Mathlib.MeasureTheory.Integral.TorusIntegral
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Finite-dimensional Weierstrass theorem

Uniform convergence on a closed polydisc passes through the product Cauchy
integral and its joint derivative. Smaller polydiscs provide neighborhoods
on which the resulting derivative convergence is uniform.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Set Complex
open scoped Real

namespace DOZZ.Proofs

variable {N : ℕ}


/-- Coordinate evaluation has operator norm at most one in the finite maximum norm. -/
theorem norm_coordinate_proj_le_one (i : Fin N) :
    ‖(ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    simpa only [ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm z i

private def cderivMap (r : ℝ) (f : (Fin N → ℂ) → ℂ) (z : Fin N → ℂ) :
    (Fin N → ℂ) →L[ℂ] ℂ :=
  ∑ i, Complex.cderiv r (fun w => f (z + w • Pi.single i 1)) 0 • ContinuousLinearMap.proj i




/-- Proof of `DOZZ.differentiableOn_of_tendstoLocallyUniformlyOn_fin`: the locally uniform limit is
jointly holomorphic, with locally uniform convergence of its full complex Fréchet derivative. -/
theorem differentiableOn_of_tendstoLocallyUniformlyOn_fin
    (U : Set (Fin N → ℂ)) (hU : IsOpen U)
    (F : ℕ → (Fin N → ℂ) → ℂ) (f : (Fin N → ℂ) → ℂ)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hlim : TendstoLocallyUniformlyOn F f atTop U) :
    DifferentiableOn ℂ f U ∧
      TendstoLocallyUniformlyOn (fun n => fderiv ℂ (F n)) (fderiv ℂ f) atTop U := by
  have fderiv_eq_cderivMap {g : (Fin N → ℂ) → ℂ} (hg : DifferentiableOn ℂ g U) {z : Fin N → ℂ} {r : ℝ} (hr : 0 < r) (hslice : ∀ i : Fin N, ∀ w ∈ Metric.closedBall (0 : ℂ) r, z + w • Pi.single i 1 ∈ U) : fderiv ℂ g z = cderivMap r g z := by
    have clm_eq_sum_proj (L : (Fin N → ℂ) →L[ℂ] ℂ) : L = ∑ i, L (Pi.single i 1) • (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ) := by
      ext v
      have hv : v = ∑ i, v i • Pi.single i (1 : ℂ) := by
        ext j; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hv, map_sum]
      simp [mul_comm]
    rw [clm_eq_sum_proj (fderiv ℂ g z), cderivMap]
    refine Finset.sum_congr rfl fun i _ => congrArg (· • _) ?_
    have hcont_line : Continuous fun u : ℂ => z + u • Pi.single i (1 : ℂ) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hV : IsOpen {w : ℂ | z + w • Pi.single i 1 ∈ U} := hU.preimage hcont_line
    have hhd (w : ℂ) (hw : z + w • Pi.single i 1 ∈ U) :
        HasDerivAt (fun u => g (z + u • Pi.single i 1))
          (fderiv ℂ g (z + w • Pi.single i 1) (Pi.single i 1)) w := by
      have h1 := (hg.differentiableAt (hU.mem_nhds hw)).hasFDerivAt
      have h2 : HasDerivAt (fun u : ℂ => z + u • Pi.single i 1) (Pi.single i 1) w := by
        simpa using ((hasDerivAt_id w).smul_const (Pi.single i (1 : ℂ))).const_add z
      exact h1.comp_hasDerivAt w h2
    have hc_eq := Complex.cderiv_eq_deriv hV
      (fun w hw => (hhd w hw).differentiableAt.differentiableWithinAt) hr (hslice i)
    simpa using (hc_eq.trans (hhd 0 (hslice i 0 (Metric.mem_closedBall_self hr.le))).deriv).symm
  have norm_pi_single_one_le (i : Fin N) : ‖(Pi.single i 1 : Fin N → ℂ)‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j; by_cases h : j = i <;> simp [h]
  have hf_cont : ContinuousOn f U :=
    hlim.continuousOn (Eventually.of_forall fun n => (hF n).continuousOn).frequently
  have hloc (a : Fin N → ℂ) (ha : a ∈ U) :
      ∃ r > 0, DifferentiableOn ℂ f (Metric.ball a r) ∧
        TendstoUniformlyOn (fun n => fderiv ℂ (F n)) (fderiv ℂ f) atTop (Metric.ball a r) := by
    obtain ⟨ρ, hρ, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds ha)
    have hr : 0 < ρ / 2 := half_pos hρ
    have hslice_mem {z : Fin N → ℂ} (hz : z ∈ Metric.ball a (ρ / 2)) (i : Fin N)
        {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) (ρ / 2)) :
        z + w • Pi.single i 1 ∈ Metric.closedBall a ρ := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      rw [Metric.mem_closedBall, dist_zero_right] at hw
      rw [Metric.mem_closedBall, dist_eq_norm,
        show z + w • Pi.single i 1 - a = (z - a) + w • Pi.single i 1 by abel]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul]
      have : ‖w‖ * ‖(Pi.single i 1 : Fin N → ℂ)‖ ≤ ρ / 2 :=
        (mul_le_of_le_one_right (norm_nonneg _) (norm_pi_single_one_le i)).trans hw
      linarith
    have hunif : TendstoUniformlyOn F f atTop (Metric.closedBall a ρ) :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hlim _ hsub (isCompact_closedBall a ρ)
    have hG_unif : TendstoUniformlyOn (fun n => fderiv ℂ (F n)) (cderivMap (ρ / 2) f)
        atTop (Metric.ball a (ρ / 2)) := by
      rw [Metric.tendstoUniformlyOn_iff] at hunif ⊢
      intro ε hε
      have hδ : 0 < ε * (ρ / 2) / (N + 1) := div_pos (mul_pos hε hr) (by positivity)
      filter_upwards [hunif _ hδ] with n hn z hz
      rw [dist_eq_norm, fderiv_eq_cderivMap (hF n) hr fun i w hw => hsub (hslice_mem hz i hw),
        cderivMap, cderivMap, ← Finset.sum_sub_distrib]
      refine ((norm_sum_le _ _).trans
        (Finset.sum_le_sum (g := fun _ => (ε * (ρ / 2) / (N + 1)) / (ρ / 2)) fun i _ => ?_)).trans_lt ?_
      · rw [show Complex.cderiv (ρ / 2) (fun w => f (z + w • Pi.single i 1)) 0 •
              (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℂ] ℂ) -
            Complex.cderiv (ρ / 2) (fun w => F n (z + w • Pi.single i 1)) 0 • ContinuousLinearMap.proj i =
          (Complex.cderiv (ρ / 2) (fun w => f (z + w • Pi.single i 1)) 0 -
            Complex.cderiv (ρ / 2) (fun w => F n (z + w • Pi.single i 1)) 0) • ContinuousLinearMap.proj i
          from (sub_smul _ _ _).symm, norm_smul]
        have hcont_line : ContinuousOn (fun w : ℂ => z + w • Pi.single i (1 : ℂ))
            (Metric.sphere 0 (ρ / 2)) :=
          (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
        have hmaps : MapsTo (fun w : ℂ => z + w • Pi.single i 1) (Metric.sphere 0 (ρ / 2)) U :=
          fun w hw => hsub (hslice_mem hz i (Metric.sphere_subset_closedBall hw))
        have hlt := Complex.norm_cderiv_sub_lt hr (M := ε * (ρ / 2) / (N + 1)) (z := 0)
          (fun w hw => by simpa [dist_eq_norm] using hn _ (hslice_mem hz i (Metric.sphere_subset_closedBall hw)))
          (hf_cont.comp hcont_line hmaps) ((hF n).continuousOn.comp hcont_line hmaps)
        exact (mul_le_of_le_one_right (norm_nonneg _) (norm_coordinate_proj_le_one i)).trans hlt.le
      · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have : (N : ℝ) * ((ε * (ρ / 2) / (N + 1)) / (ρ / 2)) = (N : ℝ) / (N + 1) * ε := by
          field_simp [hr.ne']
        rw [this]
        exact mul_lt_of_lt_one_left hε ((div_lt_one (by positivity)).2 (lt_add_one _))
    have hball_sub : Metric.ball a (ρ / 2) ⊆ U := fun z hz =>
      hsub (Metric.ball_subset_closedBall (Metric.ball_subset_ball (by linarith) hz))
    have hder_at (z : Fin N → ℂ) (hz : z ∈ Metric.ball a (ρ / 2)) :
        HasFDerivAt f (cderivMap (ρ / 2) f z) z :=
      hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hG_unif
        (fun n x hx => ((hF n).differentiableAt (hU.mem_nhds (hball_sub hx))).hasFDerivAt)
        (fun x hx => hlim.tendsto_at (hball_sub hx)) hz
    exact ⟨ρ / 2, hr, fun z hz => (hder_at z hz).differentiableAt.differentiableWithinAt,
      hG_unif.congr_right fun z hz => (hder_at z hz).fderiv.symm⟩
  refine ⟨fun a ha => ?_, Metric.tendstoLocallyUniformlyOn_iff.2 fun ε hε a ha => ?_⟩
  · obtain ⟨r, hr, hd, _⟩ := hloc a ha
    exact (hd.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt
  · obtain ⟨r, hr, _, hdu⟩ := hloc a ha
    exact ⟨Metric.ball a r, mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)),
      Metric.tendstoUniformlyOn_iff.1 hdu ε hε⟩

end DOZZ.Proofs
