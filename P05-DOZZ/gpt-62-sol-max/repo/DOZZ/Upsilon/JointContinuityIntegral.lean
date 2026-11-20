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
public import DOZZ.Upsilon.IntegralBounds

/-!
# Joint parameter and argument continuity of the entire Upsilon family
-/

@[expose] public section

open Complex Filter MeasureTheory Set Topology

namespace DOZZ.Proofs

private noncomputable def jointToComplex (p : (ℝ × ℂ) × ℝ) : (ℂ × ℂ) × ℂ :=
  (((p.1.1 : ℂ), p.1.2), (p.2 : ℂ))

private noncomputable def jointComplexNumerator (q : (ℂ × ℂ) × ℂ) : ℂ :=
  upsilonNumerator q.1.1 (q.1.1 / 4 + q.1.1⁻¹ - q.1.2) q.2

private noncomputable def jointCanceledNumerator (p : (ℝ × ℂ) × ℝ) : ℂ :=
  jointComplexNumerator (jointToComplex p)

private theorem jointCanceledNumerator_contDiffAt {p : (ℝ × ℂ) × ℝ}
    (hp : 0 < p.1.1) : ContDiffAt ℝ 3 jointCanceledNumerator p := by
  have hp0 : (jointToComplex p).1.1 ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have h : ContDiffAt ℂ 3 jointComplexNumerator (jointToComplex p) := by
    fun_prop (disch := assumption) [jointComplexNumerator, upsilonNumerator]
  have hmap : ContDiff ℝ 3 jointToComplex :=
    ((Complex.ofRealCLM.contDiff.comp (contDiff_fst.comp contDiff_fst)).prodMk
      (contDiff_snd.comp contDiff_fst)).prodMk (Complex.ofRealCLM.contDiff.comp contDiff_snd)
  exact (h.restrict_scalars ℝ).comp p hmap.contDiffAt

private theorem jointCanceledNumerator_eq (γ : ℝ) (z : ℂ) (t : ℝ) :
    jointCanceledNumerator ((γ,z),t) = upsilonCanceledNumerator γ z t := by
  have h : (Q γ : ℂ) / 2 = (γ : ℂ) / 4 + (γ : ℂ)⁻¹ := by
    unfold Q
    push_cast
    ring
  simp [jointCanceledNumerator, jointComplexNumerator, jointToComplex, upsilonCanceledNumerator, h]

private theorem exists_jointNumerator_taylor_bound {γ₀ : ℝ} {z₀ : ℂ} (hγ₀ : 0 < γ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : ℝ) (z : ℂ) (t : ℝ),
      γ ∈ Icc (γ₀ / 2) (γ₀ + 1) → ‖z - z₀‖ ≤ 1 → t ∈ Icc 0 1 →
      ‖upsilonCanceledNumerator γ z t‖ ≤ C * t ^ 3 := by
  let K := Icc (γ₀ / 2) (γ₀ + 1) ×ˢ Metric.closedBall z₀ 1
  have hpos (p : ℝ × ℂ) (hp : p ∈ K) : 0 < p.1 := (by positivity : 0 < γ₀ / 2).trans_le hp.1.1
  obtain ⟨C,hC,hb⟩ := exists_uniform_cubic_bound (K := K) (F := jointCanceledNumerator)
    (isCompact_Icc.prod (isCompact_closedBall _ _))
    (fun p hp => jointCanceledNumerator_contDiffAt (hpos p.1 hp.1)) (by
      rintro ⟨g,z⟩ hp j hj
      simp_rw [jointCanceledNumerator_eq]
      exact upsilonCanceledNumerator_jet (hpos (g,z) hp) z j hj)
  refine ⟨C,hC,fun γ z t hγ hz ht => ?_⟩
  rw [← jointCanceledNumerator_eq]
  exact hb (γ,z) ⟨hγ, by simpa [Metric.mem_closedBall, dist_eq_norm]⟩ t ht

private noncomputable def jointTailLower (γ₀ : ℝ) : ℝ :=
  ((1 - Real.exp (-2 * (γ₀ / 2 / 4))) / 2) *
    ((1 - Real.exp (-2 * (1 / (γ₀ + 1)))) / 2)

private theorem jointTailLower_pos {γ₀ : ℝ} (hγ₀ : 0 < γ₀) :
    0 < jointTailLower γ₀ := by
  have ha : 0 < γ₀ / 2 / 4 := by positivity
  have hb : 0 < 1 / (γ₀ + 1) := by positivity
  have h₁ : -2 * (γ₀ / 2 / 4) < 0 := by linarith only [ha]
  have h₂ : -2 * (1 / (γ₀ + 1)) < 0 := by linarith only [hb]
  have he₁  := Real.exp_lt_one_iff.mpr h₁
  have he₂  := Real.exp_lt_one_iff.mpr h₂
  unfold jointTailLower
  exact mul_pos (div_pos (sub_pos.mpr he₁) (by norm_num))
    (div_pos (sub_pos.mpr he₂) (by norm_num))

section
variable {γ₀ γ : ℝ} (hγ₀ : 0 < γ₀) (hγ : γ ∈ Set.Icc (γ₀ / 2) (γ₀ + 1))
include hγ₀ hγ

private theorem jointTailLower_le :
    jointTailLower γ₀ ≤ tailConst γ := by
  have hγpos  := lt_of_lt_of_le (by positivity) hγ.1
  have hinv  :=
    one_div_le_one_div_of_le hγpos hγ.2
  have he₁ : Real.exp (-2 * (γ / 4)) ≤ Real.exp (-2 * (γ₀ / 2 / 4)) :=
    Real.exp_le_exp.mpr (by linarith only [hγ.1])
  have he₂ : Real.exp (-2 * (1 / γ)) ≤ Real.exp (-2 * (1 / (γ₀ + 1))) :=
    Real.exp_le_exp.mpr (by linarith only [hinv])
  have hbase1 : -2 * (γ₀ / 2 / 4) < 0 := by
    have : 0 < γ₀ / 2 / 4 := by positivity
    linarith only [this]
  have hbase2 : -2 * (1 / (γ₀ + 1)) < 0 := by
    have : 0 < 1 / (γ₀ + 1) := by positivity
    linarith only [this]
  have h₁ : 0 ≤ (1 - Real.exp (-2 * (γ₀ / 2 / 4))) / 2 := by
    have he  := Real.exp_lt_one_iff.mpr hbase1
    positivity
  have h₂ : 0 ≤ (1 - Real.exp (-2 * (1 / (γ₀ + 1)))) / 2 := by
    have he  := Real.exp_lt_one_iff.mpr hbase2
    positivity
  have h₁' : (1 - Real.exp (-2 * (γ₀ / 2 / 4))) / 2 ≤
      (1 - Real.exp (-2 * (γ / 4))) / 2 := by
    linarith only [he₁]
  have h₂' : (1 - Real.exp (-2 * (1 / (γ₀ + 1)))) / 2 ≤
      (1 - Real.exp (-2 * (1 / γ))) / 2 := by
    linarith only [he₂]
  have h₁actual  :=
    le_trans h₁ h₁'
  unfold jointTailLower tailConst
  exact mul_le_mul h₁' h₂' h₂ h₁actual

private theorem Q_le_jointUpper :
    Q γ ≤ (γ₀ + 1) / 2 + 4 / γ₀ := by
  have hinv₁  :=
    one_div_le_one_div_of_le (by positivity : 0 < γ₀ / 2) hγ.1
  have hinv : 1 / γ ≤ 2 / γ₀ := by
    linarith
  have hinv2 : 2 / γ ≤ 4 / γ₀ := by
    grind
  have hγhalf : γ / 2 ≤ (γ₀ + 1) / 2 :=
    div_le_div_of_nonneg_right hγ.2 (by norm_num)
  unfold Q
  grind

end

private noncomputable def jointStripMargin (γ₀ : ℝ) (z₀ : ℂ) : ℝ :=
  min (z₀.re / 4) ((Q γ₀ - z₀.re) / 4)

private noncomputable def jointWBound (γ₀ : ℝ) (z₀ : ℂ) : ℝ :=
  (γ₀ + 1) / 4 + 2 / γ₀ + ‖z₀‖ + 1

private noncomputable def jointMajorant (γ₀ : ℝ) (z₀ : ℂ) (C : ℝ) (t : ℝ) : ℝ :=
  (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t) +
    (jointTailLower γ₀)⁻¹ * Real.exp (-jointStripMargin γ₀ z₀ * t)

private theorem jointMajorant_integrable {γ₀ : ℝ} {z₀ : ℂ} {C : ℝ}
    (hγ₀ : 0 < γ₀) (hz₀ : 0 < z₀.re) (hzQ₀ : z₀.re < Q γ₀) (hC : 0 ≤ C) :
    Integrable (jointMajorant γ₀ z₀ C) (volume.restrict (Set.Ioi 0)) := by
  have hη : 0 < jointStripMargin γ₀ z₀ := by
    unfold jointStripMargin
    positivity
  have hmajor₁ : Integrable (fun t : ℝ =>
      (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t))
      (volume.restrict (Set.Ioi 0)) := by
    simpa [mul_comm] using
      (exp_neg_integrableOn_Ioi 0 (b := 1) (by norm_num)).const_mul
        (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2)
  have hmajor₂ : Integrable (fun t : ℝ =>
      (jointTailLower γ₀)⁻¹ * Real.exp (-jointStripMargin γ₀ z₀ * t))
      (volume.restrict (Set.Ioi 0)) := by
    simpa [mul_comm] using
      (exp_neg_integrableOn_Ioi 0 (b := jointStripMargin γ₀ z₀) hη).const_mul
        ((jointTailLower γ₀)⁻¹)
  change Integrable (fun t : ℝ =>
      (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t) +
        (jointTailLower γ₀)⁻¹ * Real.exp (-jointStripMargin γ₀ z₀ * t))
    (volume.restrict (Set.Ioi 0))
  exact hmajor₁.add hmajor₂

section
variable {γ₀ : ℝ} {z₀ : ℂ} (hγ₀ : 0 < γ₀) (hz₀ : 0 < z₀.re) (hzQ₀ : z₀.re < Q γ₀)
include hγ₀ hz₀ hzQ₀

private theorem jointIntegrand_norm_le_majorant
    {C : ℝ} (hC : 0 ≤ C)
    (hTaylor : ∀ γ z t, γ ∈ Set.Icc (γ₀ / 2) (γ₀ + 1) →
      ‖z - z₀‖ ≤ 1 → t ∈ Set.Icc 0 1 →
      ‖upsilonCanceledNumerator γ z t‖ ≤ C * t ^ 3)
    {γ : ℝ} {z : ℂ} (hγ : γ ∈ Set.Icc (γ₀ / 2) (γ₀ + 1))
    (hz : ‖z - z₀‖ ≤ 1)
    (hleft : jointStripMargin γ₀ z₀ < z.re)
    (hright : jointStripMargin γ₀ z₀ < Q γ - z.re)
    {t : ℝ} (ht : 0 < t) :
    ‖upsilonLogIntegrand γ z t‖ ≤ jointMajorant γ₀ z₀ C t := by
  have hγpos : 0 < γ := lt_of_lt_of_le (by positivity) hγ.1
  have hη : 0 < jointStripMargin γ₀ z₀ := by
    unfold jointStripMargin
    exact lt_min (by positivity) (by linarith)
  have hzpos : 0 < z.re := by linarith
  have hzQ : z.re < Q γ := by linarith
  by_cases ht1 : t ≤ 1
  · have hN := hTaylor γ z t hγ hz ⟨le_of_lt ht, ht1⟩
    have hsmall := upsilonLogIntegrand_norm_le_of_taylor hγpos z ht hC hN
    have hExp : 1 ≤ Real.exp (1 - t) := by
      calc
        1 = Real.exp 0 := by simp
        _ ≤ Real.exp (1 - t) := Real.exp_le_exp.mpr (by linarith)
    have hExpEq : Real.exp (1 - t) = Real.exp 1 * Real.exp (-t) := by
      rw [← Real.exp_add]
      congr 1
    have hsmallBound : 4 * C ≤ (4 * C * Real.exp 1) * Real.exp (-t) := by
      calc
        4 * C = 4 * C * 1 := by ring
        _ ≤ 4 * C * Real.exp (1 - t) := mul_le_mul_of_nonneg_left hExp (by positivity)
        _ = (4 * C * Real.exp 1) * Real.exp (-t) := by rw [hExpEq]; ring
    have hcoeff : 0 ≤ 4 * C * Real.exp 1 := by positivity
    have hsum : (4 * C * Real.exp 1) * Real.exp (-t) ≤
        jointMajorant γ₀ z₀ C t := by
      unfold jointMajorant
      have hExtra : 4 * C * Real.exp 1 ≤
          4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg _)
      have hmain := mul_le_mul_of_nonneg_right hExtra (Real.exp_nonneg (-t))
      have htail : 0 ≤ (jointTailLower γ₀)⁻¹ *
          Real.exp (-jointStripMargin γ₀ z₀ * t) := by
        exact mul_nonneg (le_of_lt (inv_pos.mpr (jointTailLower_pos hγ₀)))
          (Real.exp_nonneg _)
      calc
        (4 * C * Real.exp 1) * Real.exp (-t) ≤
            (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t) := hmain
        _ ≤ (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t) +
            (jointTailLower γ₀)⁻¹ * Real.exp (-jointStripMargin γ₀ z₀ * t) :=
              le_add_of_nonneg_right htail
    exact hsmall.trans (hsmallBound.trans hsum)
  · have ht1' : 1 ≤ t := le_of_not_ge ht1
    have hQmax := Q_le_jointUpper hγ₀ hγ
    have hW : ‖(Q γ / 2 : ℂ) - z‖ ≤ jointWBound γ₀ z₀ := by
      have hzNorm : ‖z‖ ≤ ‖z₀‖ + 1 := by
        calc
          ‖z‖ = ‖(z - z₀) + z₀‖ := by congr 1; abel
          _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
          _ ≤ ‖z₀‖ + 1 := by linarith [hz]
      have hQpos : 0 < Q γ := by unfold Q; positivity
      have hQhalf : Q γ / 2 ≤ ((γ₀ + 1) / 2 + 4 / γ₀) / 2 :=
        div_le_div_of_nonneg_right hQmax (by norm_num)
      have hQhalf' : Q γ / 2 ≤ (γ₀ + 1) / 4 + 2 / γ₀ := by
        calc
          Q γ / 2 ≤ ((γ₀ + 1) / 2 + 4 / γ₀) / 2 := hQhalf
          _ = (γ₀ + 1) / 4 + 2 / γ₀ := by ring
      have hnormQ : ‖(Q γ / 2 : ℂ)‖ = Q γ / 2 := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
        norm_num
      calc
        ‖(Q γ / 2 : ℂ) - z‖ ≤ ‖(Q γ / 2 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
        _ = Q γ / 2 + ‖z‖ := by rw [hnormQ]
        _ ≤ (γ₀ + 1) / 4 + 2 / γ₀ + ‖z₀‖ + 1 := by
          calc
            _ ≤ ((γ₀ + 1) / 4 + 2 / γ₀) + (‖z₀‖ + 1) :=
              add_le_add hQhalf' hzNorm
            _ = (γ₀ + 1) / 4 + 2 / γ₀ + ‖z₀‖ + 1 := by ring
        _ = jointWBound γ₀ z₀ := rfl
    have hw2 : ‖(Q γ / 2 : ℂ) - z‖ ^ 2 ≤ jointWBound γ₀ z₀ ^ 2 := by
      have hWnonneg : 0 ≤ jointWBound γ₀ z₀ := by
        unfold jointWBound
        positivity
      have hmul := mul_le_mul hW hW (norm_nonneg _) hWnonneg
      simpa [pow_two] using hmul
    have hκpos : 0 < jointTailLower γ₀ := jointTailLower_pos hγ₀
    have hκle : jointTailLower γ₀ ≤ tailConst γ := jointTailLower_le hγ₀ hγ
    have htailpos : 0 < tailConst γ := tailConst_pos hγpos
    have hinv : (tailConst γ)⁻¹ ≤ (jointTailLower γ₀)⁻¹ :=
      (inv_le_inv₀ htailpos hκpos).2 hκle
    let η := jointStripMargin γ₀ z₀
    have hleftη  := hleft
    have hrightη  := hright
    have habsη : |Q γ / 2 - z.re| < Q γ / 2 - η := by
      rw [abs_lt]
      constructor <;> linarith [hleftη, hrightη]
    have habs : |Q γ / 2 - z.re| < Q γ / 2 - jointStripMargin γ₀ z₀ := by
      assumption
    have hδ : jointStripMargin γ₀ z₀ ≤ Q γ / 2 - |Q γ / 2 - z.re| := by
      linarith
    have hExp : Real.exp (-(Q γ / 2 - |Q γ / 2 - z.re|) * t) ≤
        Real.exp (-jointStripMargin γ₀ z₀ * t) := by
      apply Real.exp_le_exp.mpr
      linarith only [mul_le_mul_of_nonneg_right hδ ht.le]
    have htail := upsilonLogIntegrand_norm_le_tail hγpos z hzpos hzQ ht1'
    have hfirst : ‖(Q γ / 2 : ℂ) - z‖ ^ 2 * Real.exp (-t) ≤
        jointWBound γ₀ z₀ ^ 2 * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hw2 (Real.exp_nonneg _)
    have hsecond := mul_le_mul hinv hExp (Real.exp_nonneg _)
        (le_of_lt (inv_pos.mpr hκpos))
    calc
      ‖upsilonLogIntegrand γ z t‖ ≤
          ‖(Q γ / 2 : ℂ) - z‖ ^ 2 * Real.exp (-t) +
            (tailConst γ)⁻¹ *
              Real.exp (-(Q γ / 2 - |Q γ / 2 - z.re|) * t) := htail
      _ ≤ jointMajorant γ₀ z₀ C t := by
        unfold jointMajorant
        have hcoeff : jointWBound γ₀ z₀ ^ 2 ≤
            4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2 :=
          le_add_of_nonneg_left (by positivity)
        have hcoeff' := mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg (-t))
        calc
          _ ≤ jointWBound γ₀ z₀ ^ 2 * Real.exp (-t) +
              (jointTailLower γ₀)⁻¹ * Real.exp (-jointStripMargin γ₀ z₀ * t) :=
                add_le_add hfirst hsecond
          _ ≤ (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t) +
              (jointTailLower γ₀)⁻¹ * Real.exp (-jointStripMargin γ₀ z₀ * t) := by
                exact add_le_add hcoeff' le_rfl

theorem upsilonLog_continuousAt_joint :
    ContinuousAt (Function.uncurry upsilonLog) (γ₀, z₀) := by
  let gap := Q γ₀ - z₀.re
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hγ₀ne : γ₀ ≠ 0 := hγ₀.ne'
  have hQcont : ContinuousAt (fun γ : ℝ => Q γ) γ₀ := by
    fun_prop (disch := assumption) [Q]
  obtain ⟨δQ, hδQ, hQδ⟩ := Metric.continuousAt_iff.mp hQcont
    (gap / 8) (by positivity)
  let ρz := min (z₀.re / 4) (min (gap / 8) 1)
  have hρz : 0 < ρz := by
    unfold ρz
    exact lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  let ε := min (δQ / 2) (min (γ₀ / 2) ρz)
  have hε : 0 < ε := by
    unfold ε
    exact lt_min (by positivity) (lt_min (by positivity) hρz)
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
  let B : ℝ → ℝ := jointMajorant γ₀ z₀ C
  have hBint : Integrable B (volume.restrict (Set.Ioi 0)) := jointMajorant_integrable hγ₀ hz₀ hzQ₀ hC
  have hNear : ∀ᶠ p : ℝ × ℂ in 𝓝 (γ₀, z₀), dist p (γ₀, z₀) < ε :=
    Metric.ball_mem_nhds _ hε
  let F : ℝ × ℂ → ℝ → ℂ := fun p t => upsilonLogIntegrand p.1 p.2 t
  have hMeas : ∀ᶠ p : ℝ × ℂ in 𝓝 (γ₀, z₀),
      AEStronglyMeasurable (F p) (volume.restrict (Set.Ioi 0)) := by
    filter_upwards with p
    exact (upsilonLogIntegrand_aestronglyMeasurable p.1 p.2).restrict
  have hBound : ∀ᶠ p : ℝ × ℂ in 𝓝 (γ₀, z₀),
      ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), ‖F p t‖ ≤ B t := by
    filter_upwards [hNear] with p hp
    have hpdist : max (dist p.1 γ₀) (dist p.2 z₀) < ε := by
      simpa [Prod.dist_eq] using hp
    have hγdist : dist p.1 γ₀ < ε := (max_lt_iff.mp hpdist).1
    have hγabs : |p.1 - γ₀| < ε := by
      simpa [Real.dist_eq] using hγdist
    have hγmem : p.1 ∈ Set.Icc (γ₀ / 2) (γ₀ + 1) := by
      constructor
      · have hlow := (abs_lt.mp hγabs).1
        linarith [hεγ]
      · have hupp := (abs_lt.mp hγabs).2
        have hε1  := le_trans hερ hρone
        linarith [hε1]
    have hγQdist : dist p.1 γ₀ < δQ := by
      have hhalf : δQ / 2 < δQ := by linarith [hδQ]
      exact lt_of_lt_of_le hγdist (le_trans hεδQ hhalf.le)
    have hQclose : |Q p.1 - Q γ₀| < gap / 8 := by
      simpa [Real.dist_eq] using hQδ hγQdist
    have hzdist : dist p.2 z₀ < ε := (max_lt_iff.mp hpdist).2
    have hznorm : ‖p.2 - z₀‖ < ρz := by
      have hznorm' : ‖p.2 - z₀‖ < ε := by
        simpa [dist_eq_norm] using hzdist
      exact lt_of_lt_of_le hznorm' hερ
    have hzball : ‖p.2 - z₀‖ ≤ 1 := hznorm.le.trans hρone
    have hzreclose : |p.2.re - z₀.re| < ρz := by
      have hRe := Complex.abs_re_le_norm (p.2 - z₀)
      simpa using lt_of_le_of_lt hRe hznorm
    have hleft : jointStripMargin γ₀ z₀ < p.2.re := by
      have h := (abs_lt.mp hzreclose).1
      have hη : jointStripMargin γ₀ z₀ ≤ z₀.re / 4 := by
        unfold jointStripMargin
        exact min_le_left _ _
      have hr := hρz₀
      linarith
    have hright : jointStripMargin γ₀ z₀ < Q p.1 - p.2.re := by
      have hqLower : Q γ₀ - gap / 8 < Q p.1 := by
        have h := (abs_lt.mp hQclose).1
        dsimp [gap] at h ⊢
        linarith
      have hzUpper : p.2.re < z₀.re + ρz := by
        have h := (abs_lt.mp hzreclose).2
        linarith
      have hη : jointStripMargin γ₀ z₀ ≤ gap / 4 := by
        unfold jointStripMargin
        dsimp [gap]
        exact min_le_right _ _
      linarith [hρgap]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact jointIntegrand_norm_le_majorant hγ₀ hz₀ hzQ₀ hC hTaylor hγmem hzball
      hleft hright ht
  have hCont : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
      ContinuousAt (fun p : ℝ × ℂ => F p t) (γ₀, z₀) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := ht
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htpos.ne'
    have hsin₁ : Real.sinh (t * γ₀ / 4) ≠ 0 :=
      (Real.sinh_pos_iff.2 (by positivity)).ne'
    have hsin₂  :=
      (Real.sinh_pos_iff.2 (div_pos htpos hγ₀)).ne'
    let w : ℝ × ℂ → ℂ := fun p => Q p.1 / 2 - p.2
    let D : ℝ × ℂ → ℂ := fun p =>
      (Real.sinh (t * p.1 / 4) : ℂ) * (Real.sinh (t / p.1) : ℂ)
    have hw : ContinuousAt w (γ₀, z₀) := by
      dsimp [w]
      fun_prop (disch := assumption) [Q]
    have hD : ContinuousAt D (γ₀, z₀) := by
      dsimp [D]
      fun_prop
    have hDne : D (γ₀, z₀) ≠ 0 := by
      dsimp [D]
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hsin₁)
        (Complex.ofReal_ne_zero.mpr hsin₂)
    have hA : ContinuousAt (fun p : ℝ × ℂ => w p ^ 2 * Real.exp (-t))
        (γ₀, z₀) := by
      fun_prop
    have hS : ContinuousAt (fun p : ℝ × ℂ =>
        Complex.sinh (w p * (t / 2)) ^ 2) (γ₀, z₀) := by
      fun_prop
    have hNum := hA.sub (hS.div hD hDne)
    have hres := hNum.div continuousAt_const htC
    simpa
  change ContinuousAt (fun p : ℝ × ℂ => ∫ t in Set.Ioi (0 : ℝ), F p t) (γ₀, z₀)
  exact continuousAt_of_dominated hMeas hBound hBint hCont

end


end DOZZ.Proofs

end
