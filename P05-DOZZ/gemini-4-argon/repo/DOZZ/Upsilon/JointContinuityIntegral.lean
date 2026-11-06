/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.Upsilon.Continuation
import DOZZ.Upsilon.FullShifts
import DOZZ.Upsilon.Uniqueness
import DOZZ.Upsilon.ZeroStructure
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Joint parameter and argument continuity of the entire Upsilon family
-/

@[expose] public section

open Complex Filter MeasureTheory Set Topology

namespace DOZZ.Proofs

private noncomputable def jointToComplex (p : (ℝ × ℂ) × ℝ) : (ℂ × ℂ) × ℂ :=
  (((p.1.1 : ℂ), p.1.2), (p.2 : ℂ))

private noncomputable def jointComplexNumerator (q : (ℂ × ℂ) × ℂ) : ℂ :=
  let w := q.1.1 / 4 + q.1.1⁻¹ - q.1.2
  w ^ 2 * Complex.exp (-q.2) *
      (Complex.sinh (q.2 * q.1.1 / 4) * Complex.sinh (q.2 / q.1.1)) -
    Complex.sinh (w * (q.2 / 2)) ^ 2

private noncomputable def jointCanceledNumerator (p : (ℝ × ℂ) × ℝ) : ℂ :=
  jointComplexNumerator (jointToComplex p)



private noncomputable def jointThirdDerivative (q : (ℝ × ℂ) × ℝ) : ℂ :=
  iteratedFDeriv ℝ 3 jointCanceledNumerator q (fun _ : Fin 3 => ((0 : ℝ × ℂ), (1 : ℝ)))





private noncomputable def jointNumeratorAt (γ : ℝ) (z : ℂ) : ℝ → ℂ :=
  fun t => jointCanceledNumerator ((γ, z), t)

private noncomputable def jointNumeratorComplexAt (γ : ℝ) (z : ℂ) : ℂ → ℂ :=
  fun t => jointComplexNumerator (((γ : ℂ), z), t)


private theorem deriv_real_restrict (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    deriv (fun t : ℝ => F (t : ℂ)) = fun t : ℝ => deriv F (t : ℂ) := by
  funext t
  exact (hF t).hasDerivAt.comp_ofReal.deriv


private noncomputable def jointNumeratorComplexAtDerivative (γ : ℝ) (z t : ℂ) : ℂ :=
  let w := (γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z
  w ^ 2 * Complex.exp (-t) *
      ((γ : ℂ) / 4 * Complex.cosh (t * (γ : ℂ) / 4) *
          Complex.sinh (t / (γ : ℂ)) +
        (γ : ℂ)⁻¹ * Complex.sinh (t * (γ : ℂ) / 4) *
          Complex.cosh (t / (γ : ℂ)) -
        Complex.sinh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ))) -
    w * Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))










private noncomputable def jointTailLower (γ₀ : ℝ) : ℝ :=
  ((1 - Real.exp (-2 * (γ₀ / 2 / 4))) / 2) *
    ((1 - Real.exp (-2 * (1 / (γ₀ + 1)))) / 2)




private noncomputable def jointStripMargin (γ₀ : ℝ) (z₀ : ℂ) : ℝ :=
  min (z₀.re / 4) ((Q γ₀ - z₀.re) / 4)

private noncomputable def jointWBound (γ₀ : ℝ) (z₀ : ℂ) : ℝ :=
  (γ₀ + 1) / 4 + 2 / γ₀ + ‖z₀‖ + 1

private noncomputable def jointMajorant (γ₀ : ℝ) (z₀ : ℂ) (C t : ℝ) : ℝ :=
  (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t) +
    (jointTailLower γ₀)⁻¹ * Real.exp (-jointStripMargin γ₀ z₀ * t)



theorem upsilonLog_continuousAt_joint {γ₀ : ℝ} {z₀ : ℂ}
    (hγ₀ : 0 < γ₀) (hz₀ : 0 < z₀.re) (hzQ₀ : z₀.re < Q γ₀) :
    ContinuousAt (Function.uncurry upsilonLog) (γ₀, z₀) := by
  have jointTailLower_pos : 0 < jointTailLower γ₀ := by
    unfold jointTailLower
    exact mul_pos (div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [(show 0 < γ₀ / 2 / 4 by positivity)]))) (by norm_num))
      (div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [(show 0 < 1 / (γ₀ + 1) by positivity)]))) (by norm_num))
  have jointNumeratorComplexAt_deriv_eq γ z : deriv (jointNumeratorComplexAt γ z) = jointNumeratorComplexAtDerivative γ z := by
    funext t
    change deriv (fun t : ℂ =>
      ((γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z) ^ 2 * Complex.exp (-t) *
          (Complex.sinh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ))) -
        Complex.sinh (((γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z) * (t / 2)) ^ 2) t = _
    simp (disch := fun_prop) [jointNumeratorComplexAtDerivative, deriv_csinh,
      deriv_cexp]
    ring_nf
  have jointNumeratorComplexAt_contDiff {γ} (hγ : γ ≠ 0) z : ContDiff ℂ 3 (jointNumeratorComplexAt γ z) := by
    change ContDiff ℂ 3 (fun t : ℂ =>
      ((γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z) ^ 2 * Complex.exp (-t) *
          (Complex.sinh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ))) -
        Complex.sinh (((γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z) * (t / 2)) ^ 2)
    fun_prop (disch := assumption)
  have jointCanceledNumerator_contDiffOn : ContDiffOn ℝ 3 jointCanceledNumerator {p | 0 < p.1.1} := by
    have jointComplexNumerator_contDiffAt {q : (ℂ × ℂ) × ℂ} (hq : q.1.1 ≠ 0) : ContDiffAt ℂ 3 jointComplexNumerator q := by
      unfold jointComplexNumerator
      fun_prop
    intro p hp
    change ContDiffWithinAt ℝ 3 jointCanceledNumerator {p | 0 < p.1.1} p
    exact (show ContDiffAt ℝ 3 jointCanceledNumerator p by change ContDiffAt ℝ 3 (jointComplexNumerator ∘ jointToComplex) p; exact ContDiffAt.comp p ((jointComplexNumerator_contDiffAt (by apply Complex.ofReal_ne_zero.mpr; exact (ne_of_gt hp))).restrict_scalars ℝ) (by change ContDiffAt ℝ 3 (fun x : (ℝ × ℂ) × ℝ => (((x.1.1 : ℂ), x.1.2), (x.2 : ℂ))) p; exact ((ContDiffAt.comp p Complex.ofRealCLM.contDiff.contDiffAt (by fun_prop)).prodMk (by fun_prop)).prodMk (ContDiffAt.comp p Complex.ofRealCLM.contDiff.contDiffAt (by fun_prop)))).contDiffWithinAt
  have jointCanceledNumerator_contDiffAt {q : (ℝ × ℂ) × ℝ} (hq : 0 < q.1.1) : ContDiffAt ℝ 3 jointCanceledNumerator q := jointCanceledNumerator_contDiffOn.contDiffAt ((isOpen_lt continuous_const (by fun_prop)).mem_nhds hq)
  have jointIntegrand_norm_le_majorant {C} (hC : 0 ≤ C) (hTaylor : ∀ γ z t, γ ∈ Set.Icc (γ₀ / 2) (γ₀ + 1) → ‖z - z₀‖ ≤ 1 → t ∈ Set.Icc 0 1 → ‖jointNumeratorAt γ z t‖ ≤ C * t ^ 3) {γ : ℝ} {z : ℂ} (hγ : γ ∈ Set.Icc (γ₀ / 2) (γ₀ + 1)) (hz : ‖z - z₀‖ ≤ 1) (hleft : jointStripMargin γ₀ z₀ < z.re) (hright : jointStripMargin γ₀ z₀ < Q γ - z.re) {t} (ht : 0 < t) : ‖upsilonLogIntegrand γ z t‖ ≤ jointMajorant γ₀ z₀ C t := by
    have Q_le_jointUpper : Q γ ≤ (γ₀ + 1) / 2 + 4 / γ₀ := by
      have hinv : 1 / γ ≤ 2 / γ₀ := by
        calc
          1 / γ ≤ 1 / (γ₀ / 2) := (one_div_le_one_div_of_le (by positivity : 0 < γ₀ / 2) hγ.1)
          _ = 2 / γ₀ := by field_simp [hγ₀.ne']
      have hinv2 : 2 / γ ≤ 4 / γ₀ := by
        calc
          2 / γ = 2 * (1 / γ) := by ring
          _ ≤ 2 * (2 / γ₀) := mul_le_mul_of_nonneg_left hinv (by norm_num)
          _ = 4 / γ₀ := by ring
      unfold Q
      calc
        2 / γ + γ / 2 = γ / 2 + 2 / γ := by ring
        _ ≤ (γ₀ + 1) / 2 + 4 / γ₀ := by
          exact add_le_add (div_le_div_of_nonneg_right hγ.2 (by norm_num)) hinv2
    have jointTailLower_le : jointTailLower γ₀ ≤ tailConst γ := by
      have h₁ : 0 ≤ (1 - Real.exp (-2 * (γ₀ / 2 / 4))) / 2 := by
        have : Real.exp (-2 * (γ₀ / 2 / 4)) < 1 := Real.exp_lt_one_iff.mpr (by linarith only [(show 0 < γ₀ / 2 / 4 by positivity)])
        positivity
      have h₂ : 0 ≤ (1 - Real.exp (-2 * (1 / (γ₀ + 1)))) / 2 := by
        have : Real.exp (-2 * (1 / (γ₀ + 1))) < 1 := Real.exp_lt_one_iff.mpr (by linarith only [(show 0 < 1 / (γ₀ + 1) by positivity)])
        positivity
      have h₁' : (1 - Real.exp (-2 * (γ₀ / 2 / 4))) / 2 ≤
          (1 - Real.exp (-2 * (γ / 4))) / 2 := by
        linarith only [(Real.exp_le_exp.mpr (by linarith only [hγ.1]) : Real.exp (-2 * (γ / 4)) ≤ Real.exp (-2 * (γ₀ / 2 / 4)))]
      unfold jointTailLower tailConst
      exact mul_le_mul h₁' (by linarith only [(Real.exp_le_exp.mpr (by linarith only [(one_div_le_one_div_of_le (lt_of_lt_of_le (by positivity) hγ.1) hγ.2)]) : Real.exp (-2 * (1 / γ)) ≤ Real.exp (-2 * (1 / (γ₀ + 1))))]) h₂ (le_trans h₁ h₁')
    have upsilonLogIntegrand_norm_le_jointTaylor {γ : ℝ} (hγ : 0 < γ) z {C} {t} (hC : 0 ≤ C) (hN : ‖jointNumeratorAt γ z t‖ ≤ C * t ^ 3) (ht : 0 < t) : ‖upsilonLogIntegrand γ z t‖ ≤ 4 * C := by
      have upsilonLogIntegrand_eq_jointNumerator_div : upsilonLogIntegrand γ z t = jointNumeratorAt γ z t / ((realDenom γ t : ℂ) * (t : ℂ)) := by
        have jointNumeratorAt_eq_source z t : jointNumeratorAt γ z t = (Q γ / 2 - z) ^ 2 * Real.exp (-t) * (Real.sinh (t * γ / 4) * Real.sinh (t / γ) : ℂ) - Complex.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2 := by
          have jointW_eq_source : (γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z = (Q γ / 2 : ℝ) - z := by
            have hqR : Q γ / 2 = γ / 4 + γ⁻¹ := by
              unfold Q
              field_simp [hγ.ne']
              ring
            rw [(show (γ : ℂ) / 4 + (γ : ℂ)⁻¹ = (Q γ / 2 : ℝ) by exact_mod_cast hqR.symm)]
          simp only [jointNumeratorAt, jointCanceledNumerator, jointToComplex,
            jointComplexNumerator]
          rw [jointW_eq_source]
          simp only [Complex.ofReal_exp, Complex.ofReal_sinh, Complex.ofReal_neg,
            Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
        rw [upsilonLogIntegrand, jointNumeratorAt_eq_source]
        have htC := Complex.ofReal_ne_zero.mpr ht.ne'
        have hS₁ : (Real.sinh (t * γ / 4) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.2 (by positivity)).ne'
        have hS₂ := Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.2 (div_pos ht hγ)).ne'
        rw [(show (realDenom γ t : ℂ) = (Real.sinh (t * γ / 4) : ℂ) * (Real.sinh (t / γ) : ℂ) by simp [realDenom])]
        field_simp [(Complex.ofReal_ne_zero.mpr (realDenom_pos hγ ht).ne'), htC, hS₁, hS₂]
      have hDen := realDenom_pos hγ ht
      have hDt : t ^ 3 / 4 ≤ realDenom γ t * t := by
        calc
          t ^ 3 / 4 = (t ^ 2 / 4) * t := by ring
          _ ≤ realDenom γ t * t := mul_le_mul_of_nonneg_right (realDenom_ge_quadratic hγ ht) (le_of_lt ht)
      have hDtPos := mul_pos hDen ht
      rw [upsilonLogIntegrand_eq_jointNumerator_div, norm_div, (show ‖(realDenom γ t : ℂ) * (t : ℂ)‖ = realDenom γ t * t by rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hDen, abs_of_pos ht])]
      calc
        ‖jointNumeratorAt γ z t‖ / (realDenom γ t * t) ≤
            (C * t ^ 3) / (realDenom γ t * t) :=
          div_le_div_of_nonneg_right hN (le_of_lt hDtPos)
        _ ≤ 4 * C := (div_le_iff₀ hDtPos).2 <| by
          calc
            C * t ^ 3 = 4 * C * (t ^ 3 / 4) := by ring
            _ ≤ 4 * C * (realDenom γ t * t) :=
              mul_le_mul_of_nonneg_left hDt (by positivity)
    have hγpos : 0 < γ := lt_of_lt_of_le (by positivity) hγ.1
    have : 0 < jointStripMargin γ₀ z₀ := by
      unfold jointStripMargin
      exact lt_min (by positivity) (by linarith)
    by_cases ht1 : t ≤ 1
    · have hN := hTaylor γ z t hγ hz ⟨le_of_lt ht, ht1⟩
      have hExp : 1 ≤ Real.exp (1 - t) := by
        calc
          1 = Real.exp 0 := by simp
          _ ≤ Real.exp (1 - t) := Real.exp_le_exp.mpr (by linarith)
      have hsmallBound : 4 * C ≤ (4 * C * Real.exp 1) * Real.exp (-t) := by
        calc
          4 * C = 4 * C * 1 := by ring
          _ ≤ 4 * C * Real.exp (1 - t) := mul_le_mul_of_nonneg_left hExp (by positivity)
          _ = (4 * C * Real.exp 1) * Real.exp (-t) := by rw [(show Real.exp (1 - t) = Real.exp 1 * Real.exp (-t) by rw [← Real.exp_add]; congr 1)]; ring
      have hsum : (4 * C * Real.exp 1) * Real.exp (-t) ≤
          jointMajorant γ₀ z₀ C t := by
        unfold jointMajorant
        calc
          (4 * C * Real.exp 1) * Real.exp (-t) ≤
              (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t) := (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg _) : 4 * C * Real.exp 1 ≤ 4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) (Real.exp_nonneg (-t)))
          _ ≤ (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t) +
              (jointTailLower γ₀)⁻¹ * Real.exp (-jointStripMargin γ₀ z₀ * t) :=
                le_add_of_nonneg_right (mul_nonneg (le_of_lt (inv_pos.mpr (jointTailLower_pos))) (Real.exp_nonneg _))
      exact (upsilonLogIntegrand_norm_le_jointTaylor hγpos z hC hN ht).trans (hsmallBound.trans hsum)
    · have ht1' : 1 ≤ t := le_of_not_ge ht1
      have hW : ‖(Q γ / 2 : ℂ) - z‖ ≤ jointWBound γ₀ z₀ := by
        have hzNorm : ‖z‖ ≤ ‖z₀‖ + 1 := by
          calc
            ‖z‖ = ‖(z - z₀) + z₀‖ := by congr 1; abel
            _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
            _ ≤ ‖z₀‖ + 1 := by linarith [hz]
        have : 0 < Q γ := by unfold Q; positivity
        have hQhalf' : Q γ / 2 ≤ (γ₀ + 1) / 4 + 2 / γ₀ := by
          calc
            Q γ / 2 ≤ ((γ₀ + 1) / 2 + 4 / γ₀) / 2 := (div_le_div_of_nonneg_right (Q_le_jointUpper) (by norm_num))
            _ = (γ₀ + 1) / 4 + 2 / γ₀ := by ring
        calc
          ‖(Q γ / 2 : ℂ) - z‖ ≤ ‖(Q γ / 2 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
          _ = Q γ / 2 + ‖z‖ := by rw [(show ‖(Q γ / 2 : ℂ)‖ = Q γ / 2 by rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; norm_num)]
          _ ≤ (γ₀ + 1) / 4 + 2 / γ₀ + ‖z₀‖ + 1 := by
            calc
              _ ≤ ((γ₀ + 1) / 4 + 2 / γ₀) + (‖z₀‖ + 1) :=
                add_le_add hQhalf' hzNorm
              _ = (γ₀ + 1) / 4 + 2 / γ₀ + ‖z₀‖ + 1 := by ring
          _ = jointWBound γ₀ z₀ := rfl
      have hκpos := jointTailLower_pos
      let η := jointStripMargin γ₀ z₀
      have : |Q γ / 2 - z.re| < Q γ / 2 - η := by
        rw [abs_lt]
        constructor <;> linarith [hleft, hright]
      calc
        ‖upsilonLogIntegrand γ z t‖ ≤
            ‖(Q γ / 2 : ℂ) - z‖ ^ 2 * Real.exp (-t) +
              (tailConst γ)⁻¹ *
                Real.exp (-(Q γ / 2 - |Q γ / 2 - z.re|) * t) := (upsilonLogIntegrand_norm_le_tail hγpos z (show 0 < z.re by linarith) (by linarith) ht1')
        _ ≤ jointMajorant γ₀ z₀ C t := by
          unfold jointMajorant
          calc
            _ ≤ jointWBound γ₀ z₀ ^ 2 * Real.exp (-t) +
                (jointTailLower γ₀)⁻¹ * Real.exp (-jointStripMargin γ₀ z₀ * t) :=
                  add_le_add (mul_le_mul_of_nonneg_right (by simpa [pow_two] using (mul_le_mul hW hW (norm_nonneg _) (by unfold jointWBound; positivity))) (Real.exp_nonneg _)) (mul_le_mul ((inv_le_inv₀ (tailConst_pos hγpos) hκpos).2 (jointTailLower_le)) (by apply Real.exp_le_exp.mpr; linarith only [mul_le_mul_of_nonneg_right (show jointStripMargin γ₀ z₀ ≤ Q γ / 2 - |Q γ / 2 - z.re| by linarith) ht.le]) (Real.exp_nonneg _) (le_of_lt (inv_pos.mpr hκpos)))
            _ ≤ (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t) +
                (jointTailLower γ₀)⁻¹ * Real.exp (-jointStripMargin γ₀ z₀ * t) := by
                  exact add_le_add (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (Real.exp_nonneg (-t))) le_rfl
  have jointMajorant_integrable {C} (hC : 0 ≤ C) : Integrable (jointMajorant γ₀ z₀ C) (volume.restrict (Set.Ioi 0)) := by
    change Integrable (fun t : ℝ =>
        (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t) +
          (jointTailLower γ₀)⁻¹ * Real.exp (-jointStripMargin γ₀ z₀ * t))
      (volume.restrict (Set.Ioi 0))
    exact (show Integrable (fun t => (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t)) (volume.restrict (Set.Ioi 0)) by simpa [mul_comm] using (exp_neg_integrableOn_Ioi 0 (b := 1) (by norm_num)).const_mul (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2)).add (by simpa [mul_comm] using (exp_neg_integrableOn_Ioi 0 (b := jointStripMargin γ₀ z₀) (by unfold jointStripMargin; exact lt_min (by positivity) (by linarith))).const_mul ((jointTailLower γ₀)⁻¹))
  have exists_jointNumerator_taylor_bound {γ₀ : ℝ} {z₀} (hγ₀ : 0 < γ₀) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : ℝ) (z : ℂ) (t : ℝ), γ ∈ Set.Icc (γ₀ / 2) (γ₀ + 1) → ‖z - z₀‖ ≤ 1 → t ∈ Set.Icc 0 1 → ‖jointNumeratorAt γ z t‖ ≤ C * t ^ 3 := by
    have jointNumerator_taylorWithinEval_zero (γ : ℝ) (z : ℂ) (hγ : 0 < γ) (t : ℝ) : taylorWithinEval (jointNumeratorAt γ z) 2 (Set.Icc 0 1) 0 t = 0 := by
      have jointNumeratorComplexAt_iteratedDeriv_two_zero {γ : ℝ} (hγ : γ ≠ 0) z : iteratedDeriv 2 (jointNumeratorComplexAt γ z) 0 = 0 := by
        rw [iteratedDeriv_succ]
        rw [show iteratedDeriv 1 (jointNumeratorComplexAt γ z) =
            deriv (jointNumeratorComplexAt γ z) by simp]
        rw [jointNumeratorComplexAt_deriv_eq]
        change deriv (fun t : ℂ =>
          ((γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z) ^ 2 * Complex.exp (-t) *
              ((γ : ℂ) / 4 * Complex.cosh (t * (γ : ℂ) / 4) *
                  Complex.sinh (t / (γ : ℂ)) +
                (γ : ℂ)⁻¹ * Complex.sinh (t * (γ : ℂ) / 4) *
                  Complex.cosh (t / (γ : ℂ)) -
                Complex.sinh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ))) -
            ((γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z) *
              Complex.sinh (((γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z) * (t / 2)) *
              Complex.cosh (((γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z) * (t / 2))) 0 = 0
        simp (disch := fun_prop) [deriv_csinh, deriv_ccosh, deriv_cexp]
        field_simp [(Complex.ofReal_ne_zero.mpr hγ)]
        ring
      have jointNumeratorComplexAt_deriv_zero {γ : ℝ} z : deriv (jointNumeratorComplexAt γ z) 0 = 0 := by
        rw [jointNumeratorComplexAt_deriv_eq]
        simp [jointNumeratorComplexAtDerivative]
      have jointNumeratorAt_eq_complex_restrict (γ : ℝ) z : jointNumeratorAt γ z = fun t : ℝ => jointNumeratorComplexAt γ z t := by
        funext t
        simp [jointNumeratorAt, jointNumeratorComplexAt, jointCanceledNumerator,
          jointToComplex, jointComplexNumerator]
      let f := jointNumeratorAt γ z
      have hf0 : f 0 = 0 := by
        simp [f, jointNumeratorAt, jointCanceledNumerator,
          jointComplexNumerator, jointToComplex]
      have hF : Differentiable ℂ (jointNumeratorComplexAt γ z) := (jointNumeratorComplexAt_contDiff (γ := γ) hγ.ne' z).differentiable
          (by norm_num)
      have hfderiv0 : deriv f 0 = 0 := by
        change deriv (jointNumeratorAt γ z) 0 = 0
        rw [jointNumeratorAt_eq_complex_restrict, deriv_real_restrict _ hF]
        exact jointNumeratorComplexAt_deriv_zero (γ := γ) z
      have hftwo : iteratedDeriv 2 f 0 = 0 := by
        change iteratedDeriv 2 (fun t : ℝ => jointNumeratorComplexAt γ z (t : ℂ)) 0 = 0
        rw [iteratedDeriv_succ]
        rw [show iteratedDeriv 1 (fun t : ℝ => jointNumeratorComplexAt γ z (t : ℂ)) =
            deriv (fun t : ℝ => jointNumeratorComplexAt γ z (t : ℂ)) by simp]
        rw [deriv_real_restrict _ hF]
        have hF' : Differentiable ℂ (deriv (jointNumeratorComplexAt γ z)) := by
          have hC2 : ContDiff ℂ 2 (jointNumeratorComplexAt γ z) :=
            (jointNumeratorComplexAt_contDiff (γ := γ) hγ.ne' z).of_le (by norm_num)
          simpa [iteratedDeriv_succ] using hC2.differentiable_iteratedDeriv' 1
        have hsecond := (hF' (0 : ℂ)).hasDerivAt.comp_ofReal.deriv
        calc
          deriv (fun t : ℝ => deriv (jointNumeratorComplexAt γ z) (t : ℂ)) 0 =
              deriv (deriv (jointNumeratorComplexAt γ z)) 0 := hsecond
          _ = iteratedDeriv 2 (jointNumeratorComplexAt γ z) 0 := by
            rw [iteratedDeriv_succ]
            simp
          _ = 0 := jointNumeratorComplexAt_iteratedDeriv_two_zero (γ := γ)
            hγ.ne' z
      have hfAt : ContDiffAt ℝ 3 f 0 := by
        have hAt := jointCanceledNumerator_contDiffAt (q := ((γ, z), (0 : ℝ))) hγ
        have hline : ContDiffAt ℝ 3 (fun s : ℝ => ((γ, z), s)) 0 := by fun_prop
        have hcomp := ContDiffAt.comp 0 hAt hline
        change ContDiffAt ℝ 3 (fun s : ℝ => jointCanceledNumerator ((γ, z), s)) 0 at hcomp
        change ContDiffAt ℝ 3 (fun s : ℝ => jointCanceledNumerator ((γ, z), s)) 0
        exact hcomp
      have h0 : iteratedDerivWithin 0 f (Set.Icc 0 1) 0 = 0 := by
        simp [hf0]
      have h1 : iteratedDerivWithin 1 f (Set.Icc 0 1) 0 = 0 := by
        rw [iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
          (hfAt.of_le (by norm_num)) (by simp)]
        simpa [iteratedDeriv_succ] using hfderiv0
      have h2 : iteratedDerivWithin 2 f (Set.Icc 0 1) 0 = 0 := by
        rw [iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
          (hfAt.of_le (by norm_num)) (by simp)]
        exact hftwo
      rw [taylor_within_apply]
      simp [f, Finset.sum_range_succ, h0, h1, h2]
    have exists_jointThirdDerivative_bound {γ₀ : ℝ} {z₀} (hγ₀ : 0 < γ₀) : ∃ M : ℝ, ∀ (γ : ℝ) (z : ℂ) (t : ℝ), γ ∈ Set.Icc (γ₀ / 2) (γ₀ + 1) → ‖z - z₀‖ ≤ 1 → t ∈ Set.Icc 0 1 → ‖iteratedDeriv 3 (fun s : ℝ => jointCanceledNumerator ((γ, z), s)) t‖ ≤ M := by
      have jointThirdDerivative_continuousOn : ContinuousOn jointThirdDerivative {p : (ℝ × ℂ) × ℝ | 0 < p.1.1} := by
        change ContinuousOn
          (fun q => iteratedFDeriv ℝ 3 jointCanceledNumerator q
            (fun _ : Fin 3 => ((0 : ℝ × ℂ), (1 : ℝ))))
          {p : (ℝ × ℂ) × ℝ | 0 < p.1.1}
        exact (show Continuous (fun f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => (ℝ × ℂ) × ℝ) ℂ => f (fun _ : Fin 3 => ((0 : ℝ × ℂ), (1 : ℝ)))) by fun_prop).comp_continuousOn (ContinuousOn.continuousOn_iteratedFDeriv jointCanceledNumerator_contDiffOn (isOpen_lt continuous_const (by fun_prop)) (by norm_num))
      have jointThirdDerivative_eq_iteratedDeriv (q : (ℝ × ℂ) × ℝ) (hq : 0 < q.1.1) : jointThirdDerivative q = iteratedDeriv 3 (fun t : ℝ => jointCanceledNumerator (q.1, t)) q.2 := by
        let line : ℝ → (ℝ × ℂ) × ℝ := fun t => (q.1, t)
        let v := ((0 : ℝ × ℂ), (1 : ℝ))
        have hlineD : deriv line = fun _ => v := by
          funext t
          exact ((hasDerivAt_const t q.1).prodMk (hasDerivAt_id t)).deriv
        have hline3 : iteratedDeriv 3 line q.2 = 0 := by
          rw [iteratedDeriv_succ]
          rw [show iteratedDeriv 2 line = fun _ => 0 by
            funext t
            rw [iteratedDeriv_succ, show iteratedDeriv 1 line = deriv line by simp, hlineD]
            simp]
          simp
        have hcomp := iteratedDeriv_vcomp_three
          (hg := (by simpa [line] using jointCanceledNumerator_contDiffAt hq))
          (hf := (by fun_prop : ContDiffAt ℝ 3 line q.2))
        rw [(show iteratedDeriv 2 line q.2 = 0 by rw [iteratedDeriv_succ, show iteratedDeriv 1 line = deriv line by simp, hlineD]; simp), hline3] at hcomp
        simp only [line, hlineD] at hcomp
        rw [(show iteratedFDeriv ℝ 2 jointCanceledNumerator q ![0, v] = 0 by apply ContinuousMultilinearMap.map_coord_zero _ 0; simp), (show iteratedFDeriv ℝ 2 jointCanceledNumerator q ![v, 0] = 0 by apply ContinuousMultilinearMap.map_coord_zero _ 1; simp)] at hcomp
        simp at hcomp
        simpa [jointThirdDerivative, line, v, Function.comp_def] using hcomp.symm
      let K : Set ((ℝ × ℂ) × ℝ) :=
        (Set.Icc (γ₀ / 2) (γ₀ + 1) ×ˢ Metric.closedBall z₀ 1) ×ˢ Set.Icc 0 1
      have hKpos : K ⊆ {p : (ℝ × ℂ) × ℝ | 0 < p.1.1} := by
        intro p hp
        rcases hp with ⟨⟨hγ, hz⟩, ht⟩
        exact lt_of_lt_of_le (by positivity) hγ.1
      obtain ⟨M, hM⟩ := (show IsCompact K by dsimp [K]; exact (isCompact_Icc.prod (isCompact_closedBall z₀ 1)).prod isCompact_Icc).exists_bound_of_continuousOn
        (jointThirdDerivative_continuousOn.mono hKpos)
      refine ⟨M, ?_⟩
      intro γ z t hγ hz ht
      have hM' := hM ((γ, z), t) (by dsimp [K]; exact ⟨⟨hγ, Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hz)⟩, ht⟩)
      rw [jointThirdDerivative_eq_iteratedDeriv ((γ, z), t)
        (lt_of_lt_of_le (by positivity) hγ.1)] at hM'
      simpa using hM'
    obtain ⟨M, hM⟩ := exists_jointThirdDerivative_bound (γ₀ := γ₀) (z₀ := z₀) hγ₀
    have hMnonneg : 0 ≤ M := (norm_nonneg _).trans (hM γ₀ z₀ 0 (by constructor <;> linarith [hγ₀]) (by norm_num) (by norm_num))
    refine ⟨M, hMnonneg, ?_⟩
    intro γ z t hγ hz ht
    have hγpos : 0 < γ := lt_of_lt_of_le (by positivity) hγ.1
    let f := jointNumeratorAt γ z
    have hfCont : ContDiffOn ℝ 3 f (Set.Icc 0 1) := by
      intro y hy
      have hcomp := ContDiffAt.comp y (jointCanceledNumerator_contDiffAt (q := ((γ, z), y)) hγpos) (by fun_prop)
      change ContDiffAt ℝ 3 f y at hcomp
      exact hcomp.contDiffWithinAt
    have hderiv : ∀ y ∈ Set.Icc 0 1,
        ‖iteratedDerivWithin 3 f (Set.Icc 0 1) y‖ ≤ M := by
      intro y hy
      have hcomp := ContDiffAt.comp y (jointCanceledNumerator_contDiffAt (q := ((γ, z), y)) hγpos) (by fun_prop)
      change ContDiffAt ℝ 3 f y at hcomp
      rw [(iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) hcomp hy)]
      exact hM γ z y hγ hz hy
    have hTaylor := taylor_mean_remainder_bound (f := f) (a := 0) (b := 1)
      (C := M) (x := t) (n := 2) (by norm_num) hfCont ht hderiv
    rw [jointNumerator_taylorWithinEval_zero γ z hγpos t] at hTaylor
    norm_num at hTaylor
    exact hTaylor.trans (by linarith only [(mul_nonneg hMnonneg (pow_nonneg ht.1 _) : 0 ≤ M * t ^ 3)])
  let gap := Q γ₀ - z₀.re
  have : 0 < gap := by dsimp [gap]; linarith
  have := hγ₀.ne'
  have hQcont : ContinuousAt (fun γ : ℝ => Q γ) γ₀ := by
    fun_prop (disch := assumption) [Q]
  obtain ⟨δQ, hδQ, hQδ⟩ := Metric.continuousAt_iff.mp hQcont
    (gap / 8) (by positivity)
  let ρz := min (z₀.re / 4) (min (gap / 8) 1)
  have hρz : 0 < ρz := by
    unfold ρz
    exact lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  let ε := min (δQ / 2) (min (γ₀ / 2) ρz)
  have hεδQ : ε ≤ δQ / 2 := by unfold ε; exact min_le_left _ _
  have hεγ : ε ≤ γ₀ / 2 := by
    unfold ε
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hερ : ε ≤ ρz := by
    unfold ε
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hρz₀ : ρz ≤ z₀.re / 4 := by unfold ρz; exact min_le_left _ _
  have hρgap : ρz ≤ gap / 8 := by
    unfold ρz
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hρone : ρz ≤ 1 := by
    unfold ρz
    exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨C, hC, hTaylor⟩ :=
    exists_jointNumerator_taylor_bound (γ₀ := γ₀) (z₀ := z₀) hγ₀
  let B := jointMajorant γ₀ z₀ C
  have hBint := jointMajorant_integrable hC
  let F : ℝ × ℂ → ℝ → ℂ := fun p t => upsilonLogIntegrand p.1 p.2 t
  have hMeas : ∀ᶠ p : ℝ × ℂ in 𝓝 (γ₀, z₀),
      AEStronglyMeasurable (F p) (volume.restrict (Set.Ioi 0)) := by
    filter_upwards with p
    exact (upsilonLogIntegrand_aestronglyMeasurable p.1 p.2).restrict
  have hBound : ∀ᶠ p : ℝ × ℂ in 𝓝 (γ₀, z₀),
      ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), ‖F p t‖ ≤ B t := by
    filter_upwards [(Metric.ball_mem_nhds _ (by unfold ε; exact lt_min (by positivity) (lt_min (by positivity) hρz)) : ∀ᶠ p : ℝ × ℂ in 𝓝 (γ₀, z₀), dist p (γ₀, z₀) < ε)] with p hp
    have hpdist : max (dist p.1 γ₀) (dist p.2 z₀) < ε := by
      simpa [Prod.dist_eq] using hp
    have hγdist := (max_lt_iff.mp hpdist).1
    have hγabs : |p.1 - γ₀| < ε := by
      simpa [Real.dist_eq] using hγdist
    have hγmem : p.1 ∈ Set.Icc (γ₀ / 2) (γ₀ + 1) := by
      constructor
      · have hlow := (abs_lt.mp hγabs).1
        linarith [hεγ]
      · have hupp := (abs_lt.mp hγabs).2
        linarith [(le_trans hερ hρone)]
    have hznorm : ‖p.2 - z₀‖ < ρz := by
      exact lt_of_lt_of_le (by simpa [dist_eq_norm] using ((max_lt_iff.mp hpdist).2)) hερ
    have hzreclose : |p.2.re - z₀.re| < ρz := by
      simpa using lt_of_le_of_lt (Complex.abs_re_le_norm (p.2 - z₀)) hznorm
    have hleft : jointStripMargin γ₀ z₀ < p.2.re := by
      have h := (abs_lt.mp hzreclose).1
      have : jointStripMargin γ₀ z₀ ≤ z₀.re / 4 := by
        unfold jointStripMargin
        exact min_le_left _ _
      have hr := hρz₀
      linarith
    have hright : jointStripMargin γ₀ z₀ < Q p.1 - p.2.re := by
      have : Q γ₀ - gap / 8 < Q p.1 := by
        have h := (abs_lt.mp (show |Q p.1 - Q γ₀| < gap / 8 by simpa [Real.dist_eq] using hQδ (by exact lt_of_lt_of_le hγdist (le_trans hεδQ (show δQ / 2 < δQ by linarith [hδQ]).le)))).1
        dsimp [gap] at h ⊢
        linarith
      have : p.2.re < z₀.re + ρz := by
        have h := (abs_lt.mp hzreclose).2
        linarith
      have : jointStripMargin γ₀ z₀ ≤ gap / 4 := by
        unfold jointStripMargin
        dsimp [gap]
        exact min_le_right _ _
      linarith [hρgap]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact jointIntegrand_norm_le_majorant hC hTaylor hγmem (hznorm.le.trans hρone : ‖p.2 - z₀‖ ≤ 1)
      hleft hright ht
  have hCont : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
      ContinuousAt (fun p => F p t) (γ₀, z₀) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := ht
    have htC := Complex.ofReal_ne_zero.mpr htpos.ne'
    have hsin₁ : Real.sinh (t * γ₀ / 4) ≠ 0 :=
      (Real.sinh_pos_iff.2 (by positivity)).ne'
    have hsin₂ := (Real.sinh_pos_iff.2 (div_pos htpos hγ₀)).ne'
    let w : ℝ × ℂ → ℂ := fun p => Q p.1 / 2 - p.2
    let D : ℝ × ℂ → ℂ := fun p =>
      (Real.sinh (t * p.1 / 4) : ℂ) * (Real.sinh (t / p.1) : ℂ)
    have hD : ContinuousAt D (γ₀, z₀) := by
      dsimp [D]
      fun_prop
    have hA : ContinuousAt (fun p => w p ^ 2 * Real.exp (-t))
        (γ₀, z₀) := by
      fun_prop
    have hS : ContinuousAt (fun p =>
        Complex.sinh (w p * (t / 2)) ^ 2) (γ₀, z₀) := by
      fun_prop
    have hres : ContinuousAt (fun p =>
        (w p ^ 2 * Real.exp (-t) - Complex.sinh (w p * (t / 2)) ^ 2 / D p) /
          (t : ℂ)) (γ₀, z₀) := (hA.sub (hS.div hD (by dsimp [D]; exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hsin₁) (Complex.ofReal_ne_zero.mpr hsin₂)))).div continuousAt_const htC
    change ContinuousAt (fun p : ℝ × ℂ => F p t) (γ₀, z₀)
    simpa [F, upsilonLogIntegrand, w, D] using hres
  change ContinuousAt (fun p : ℝ × ℂ => ∫ t in Set.Ioi (0 : ℝ), F p t) (γ₀, z₀)
  exact continuousAt_of_dominated hMeas hBound hBint hCont


end DOZZ.Proofs

end
