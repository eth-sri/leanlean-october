module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.BasisMatching
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.ConnectionDerivative
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.BasisEndpoint
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.ConnectionLimits
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsDerivatives
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.ConnectionFlux
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsMoments
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Kummer U connection formula

The literal positive integral solution matches the two literal M series, with Gamma coefficients
identified by convergent endpoint limits.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

open Set Filter
open scoped Topology
open MeasureTheory

/- The regular M increment vanishes after division by the fractional power. -/
theorem tendsto_M_fractional_increment_zero (a : ℝ) (b : Pos) :
    Tendsto (fun z : ℝ => (M a b z - 1) / z ^ (1 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
  have hs := (hasDerivAt_M a b 0).tendsto_slope_zero_right
  simp only [zero_add, M_zero, mul_one, smul_eq_mul] at hs
  have hp : Tendsto (fun z : ℝ => z ^ (2 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Real.continuousAt_rpow_const 0 (2 / 3 : ℝ)
      (Or.inr (by norm_num))).tendsto.mono_left nhdsWithin_le_nhds
  have hl := hs.mul hp
  simp only [mul_zero] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have he : z ^ (2 / 3 : ℝ) * z ^ (1 / 3 : ℝ) = z := by
    rw [← Real.rpow_add hz, show (2 / 3 : ℝ) + 1 / 3 = 1 by ring, Real.rpow_one]
  apply (eq_div_iff (ne_of_gt (Real.rpow_pos_of_pos hz (1 / 3 : ℝ)))).mpr
  rw [mul_assoc, he]
  field_simp [ne_of_gt hz]

/- Connection formula for the source's negative first-parameter range. -/
theorem UNr_connection (a : NegThird) (z : ℝ) (hz : 0 < z) :
    UNr a z =
      Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3) * M a.1 b23 z +
      Real.Gamma (-(1 / 3)) / Real.Gamma a.1 * Real.rpow z (1 / 3) *
        M (a.1 + 1 / 3) b43 z := by
  let A : ℝ := Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ z > 0, (UNr a) z = A * M a.1 b23 z + B * secondM a.1 z := by
    let f := (UNr a)
    have hf := (contDiffOn_UNr a)
    have ho := (UNr_ode a)
    have hlim : Tendsto (UNr a) (𝓝[>] 0)
      (𝓝 (Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3))) := by
        have hc : 0 < a.1 + 1 / 3 := by linarith [a.2.1]
        have hp : Tendsto (fun z : ℝ => z ^ (1 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
          simpa using (Real.continuousAt_rpow_const 0 (1 / 3 : ℝ)
            (Or.inr (by norm_num))).tendsto.mono_left nhdsWithin_le_nhds
        have hi := tendsto_connectionIntegral_zero (a.1 + 1 / 3) hc
          (by linarith [a.2.2])
        have hl := (tendsto_const_nhds (x :=
          Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3))).add
          ((hp.mul_const (Real.Gamma (a.1 + 1 / 3))⁻¹).mul hi)
        simp only [zero_mul, add_zero] at hl
        apply hl.congr'
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (UNr_connection_decomposition a z hz).symm

      /- The coefficient of the fractional term at the singular endpoint. -/

    have hdlim : Tendsto (fun z : ℝ => z * deriv (UNr a) z) (𝓝[>] 0) (𝓝 0) := by
      have hc : 0 < a.1 + 1 / 3 := by linarith [a.2.1]
      have hc1 : a.1 + 1 / 3 < 1 / 3 := by linarith [a.2.2]
      have hp : Tendsto (fun z : ℝ => z ^ (1 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
        simpa using (Real.continuousAt_rpow_const 0 (1 / 3 : ℝ)
          (Or.inr (by norm_num))).tendsto.mono_left nhdsWithin_le_nhds
      have hl := (hp.mul_const (Real.Gamma (a.1 + 1 / 3))⁻¹).mul
        (((tendsto_connectionIntegral_zero _ hc hc1).const_mul (1 / 3 : ℝ)).sub
          (tendsto_connectionMoment_zero _ hc hc1))
      simp only [zero_mul] at hl
      apply hl.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      have _h_xinl_0 : z * deriv (UNr a) z = z ^ (1 / 3 : ℝ) * (Real.Gamma (a.1 + 1 / 3))⁻¹ *
      ((1 / 3 : ℝ) * connectionIntegral (a.1 + 1 / 3) z -
        connectionMoment (a.1 + 1 / 3) z) := by
          have hc : 0 < a.1 + 1 / 3 := by linarith [a.2.1]
          have hc1 : a.1 + 1 / 3 < 1 / 3 := by linarith [a.2.2]
          have hui := hasDerivAt_UIr ⟨a.1 + 1 / 3, hc⟩ (4 / 3) z hz
          have hd := hasDerivAt_power_mul (UIr ⟨a.1 + 1 / 3, hc⟩ (4 / 3))
            (1 / 3 : ℝ) z hz hui.differentiableAt.hasDerivAt
          rw [hui.deriv] at hd
          have he : deriv (UNr a) z =
              (1 / 3 : ℝ) * z ^ ((1 / 3 : ℝ) - 1) * UIr ⟨a.1 + 1 / 3, hc⟩ (4 / 3) z +
              z ^ (1 / 3 : ℝ) * (-(Real.Gamma (a.1 + 1 / 3))⁻¹ *
                laplaceIntegral (a.1 + 1 / 3 + 1) (4 / 3 + 1) z) := hd.deriv
          rw [he, UIr_connection_decomposition _ hc1 z hz]
          have hm := laplaceIntegral_connectionMoment _ hc hc1 z hz
          rw [show (4 / 3 : ℝ) + 1 = 7 / 3 by ring] 
          have hp : z * z ^ ((1 / 3 : ℝ) - 1) = z ^ (1 / 3 : ℝ) := by
            conv_lhs => lhs; rw [← Real.rpow_one z]
            rw [← Real.rpow_add hz]
            congr 1
            ring
          have hg := Real.Gamma_add_one (by norm_num : (1 / 3 : ℝ) ≠ 0)
          rw [show (1 / 3 : ℝ) + 1 = 4 / 3 by ring] at hg
          calc
            _ = z ^ (1 / 3 : ℝ) * (Real.Gamma (a.1 + 1 / 3))⁻¹ *
                ((1 / 3 : ℝ) * (z ^ (-(1 / 3 : ℝ)) * Real.Gamma (1 / 3) +
                  connectionIntegral (a.1 + 1 / 3) z) -
                  z * laplaceIntegral (a.1 + 1 / 3 + 1) (7 / 3) z) := by
                    rw [← hp]
                    ring
            _ = _ := by rw [hm, hg]; ring

        /- The scaled first derivative tends to zero at the singular endpoint. -/
      exact _h_xinl_0.symm

    have hm : ContDiffOn ℝ (⊤ : ℕ∞) (M a.1 b23) (Ioi 0) :=
      ((analyticOnNhd_M a.1 b23).contDiffOn uniqueDiffOn_univ).mono (subset_univ _)
    have hm0 : Tendsto (M a.1 b23) (𝓝[>] 0) (𝓝 1) := by
      simpa using (hasDerivAt_M a.1 b23 0).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    have hwf (z : ℝ) (hz : 0 < z) :=
      weightedWronskian_secondM_eq a.1 f A hf ho hlim hdlim z hz
    have hwm (z : ℝ) (hz : 0 < z) := weightedWronskian_secondM_eq a.1 (M a.1 b23) 1 hm
      (by intro z _; simpa only [b23] using M_ode a.1 b23 z) hm0
        (tendsto_M_scaled_deriv_zero _ _) z hz
    let q : ℝ → ℝ := fun z => (f z - A * M a.1 b23 z) / secondM a.1 z
    have hd (z : ℝ) (hz : z ∈ Ioi (0 : ℝ)) : HasDerivAt q 0 z := by
      have hdf := (hf.differentiableOn (by simp)).differentiableAt
        (isOpen_Ioi.mem_nhds hz)
      have hdm := (hasDerivAt_M a.1 b23 z).differentiableAt
      have hdg := ((contDiffOn_secondM a.1).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioi.mem_nhds hz)
      have h := (hdf.hasDerivAt.sub (hdm.hasDerivAt.const_mul A)).div hdg.hasDerivAt
        (ne_of_gt (secondM_pos a z hz))
      convert h using 1
      · have hw : deriv f z * secondM a.1 z - f z * deriv (secondM a.1) z =
            A * (deriv (M a.1 b23) z * secondM a.1 z -
              M a.1 b23 z * deriv (secondM a.1) z) := by
          have he := hwf z hz
          have hm' := hwm z hz
          dsimp only [weightedWronskian] at he hm'
          have hp : Real.exp (-z) * z ^ (2 / 3 : ℝ) ≠ 0 := ne_of_gt
            (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hz _))
          apply (mul_left_cancel₀ hp)
          linear_combination he - A * hm'
        dsimp only [Pi.sub_apply]
        symm
        rw [div_eq_zero_iff]
        left
        linear_combination hw
    obtain ⟨B, hB⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero
      (convex_Ioi (0 : ℝ)).isPreconnected
      (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hd z hz).deriv)
    refine ⟨B, fun z hz => ?_⟩
    have h := hB z hz
    dsimp [q] at h
    have he := (div_eq_iff (ne_of_gt (secondM_pos a z hz))).mp h
    linarith only [he]
  have hm : Tendsto (M (a.1 + 1 / 3) b43) (𝓝[>] 0) (𝓝 1) := by
    simpa using (hasDerivAt_M (a.1 + 1 / 3) b43 0).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hl := ((tendsto_M_fractional_increment_zero a.1 b23).const_mul A).add
    (hm.const_mul B)
  simp only [mul_zero, mul_one, zero_add] at hl
  have he : Tendsto (fun w : ℝ => (UNr a w - A) / w ^ (1 / 3 : ℝ))
      (𝓝[>] 0) (𝓝 B) := by
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [hB w hw, secondM]
    have hp := ne_of_gt (Real.rpow_pos_of_pos hw (1 / 3 : ℝ))
    field_simp [hp]
    ring
  have _h_xinl_0 : Tendsto (fun z : ℝ => (UNr a z - Real.Gamma (1 / 3) / Real.Gamma (a.1 + 1 / 3)) / z ^ (1 / 3 : ℝ)) (𝓝[>] 0) (𝓝 (Real.Gamma (-(1 / 3 : ℝ)) / Real.Gamma a.1)) := by
    have hc : 0 < a.1 + 1 / 3 := by linarith [a.2.1]
    have hi := (tendsto_connectionIntegral_zero (a.1 + 1 / 3) hc
      (by linarith [a.2.2])).const_mul (Real.Gamma (a.1 + 1 / 3))⁻¹
    have _h_inl_13 : (∫ t in Ioi (0 : ℝ), connectionKernel (a.1 + 1 / 3) t) =
        Real.Gamma (a.1 + 1 / 3) * Real.Gamma (-(1 / 3 : ℝ)) / Real.Gamma a.1 := by
        have hc : 0 < a.1 + 1 / 3 := by linarith [a.2.1]
        have hc1 : a.1 + 1 / 3 < 1 / 3 := by linarith [a.2.2]
        rw [integral_connectionKernel_beta _ hc hc1]
        have ha := ne_of_lt a.2.2
        have hga : Real.Gamma a.1 ≠ 0 := by
          have hg := Real.Gamma_pos_of_pos (show 0 < a.1 + 1 by linarith [a.2.1])
          rw [Real.Gamma_add_one ha] at hg
          exact right_ne_zero_of_mul (ne_of_gt hg)
        have hg := Real.Gamma_add_one (by norm_num : -(1 / 3 : ℝ) ≠ 0)
        rw [show -(1 / 3 : ℝ) + 1 = 2 / 3 by ring] at hg
        rw [show a.1 + 1 / 3 + 2 / 3 = a.1 + 1 by ring, Real.Gamma_add_one ha, hg]
        field_simp
        ring


    rw [_h_inl_13] at hi
    have hg := ne_of_gt (Real.Gamma_pos_of_pos hc)
    have he : (Real.Gamma (a.1 + 1 / 3))⁻¹ *
        (Real.Gamma (a.1 + 1 / 3) * Real.Gamma (-(1 / 3 : ℝ)) / Real.Gamma a.1) =
          Real.Gamma (-(1 / 3 : ℝ)) / Real.Gamma a.1 := by
      rw [← mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hg, one_mul]
    rw [he] at hi
    apply hi.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [UNr_connection_decomposition a z hz]
    have hp := ne_of_gt (Real.rpow_pos_of_pos hz (1 / 3 : ℝ))
    field_simp [hp]
    ring
  rw [hB z hz, (tendsto_nhds_unique he _h_xinl_0), secondM, Real.rpow_eq_pow]
  dsimp only [A]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
