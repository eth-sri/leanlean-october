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

noncomputable section
open Complex Filter MeasureTheory Set Topology

namespace DOZZ.Proofs

private def jointComplexNumerator (q : (ℂ × ℂ) × ℂ) : ℂ :=
  let w := q.1.1 / 4 + q.1.1⁻¹ - q.1.2
  w ^ 2 * Complex.exp (-q.2) * (Complex.sinh (q.2 * q.1.1 / 4) * Complex.sinh (q.2 / q.1.1)) -
    Complex.sinh (w * (q.2 / 2)) ^ 2

private def jointCanceledNumerator (p : (ℝ × ℂ) × ℝ) : ℂ :=
  jointComplexNumerator (((p.1.1 : ℂ), p.1.2), (p.2 : ℂ))

private lemma jointCanceledNumerator_contDiffOn :
    ContDiffOn ℝ 3 jointCanceledNumerator {p | 0 < p.1.1} := fun p hp => by
  have hq : (((p.1.1 : ℂ), p.1.2), (p.2 : ℂ)).1.1 ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hp)
  have hc : ContDiffAt ℂ 3 jointComplexNumerator (((p.1.1 : ℂ), p.1.2), (p.2 : ℂ)) := by
    unfold jointComplexNumerator; fun_prop
  have hm : ContDiffAt ℝ 3 (fun x : (ℝ × ℂ) × ℝ => (((x.1.1 : ℂ), x.1.2), (x.2 : ℂ))) p :=
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp p (by fun_prop)).prodMk (by fun_prop)).prodMk
      (Complex.ofRealCLM.contDiff.contDiffAt.comp p (by fun_prop))
  exact (ContDiffAt.comp p (hc.restrict_scalars ℝ) hm).contDiffWithinAt


section
variable {γ₀ : ℝ} {z₀ : ℂ} (hγ₀ : 0 < γ₀)
include z₀ hγ₀

private lemma exists_jointNumerator_taylor_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : ℝ) (z : ℂ) (t : ℝ),
      γ ∈ Set.Icc (γ₀ / 2) (γ₀ + 1) → ‖z - z₀‖ ≤ 1 → t ∈ Set.Icc 0 1 →
      ‖jointCanceledNumerator ((γ, z), t)‖ ≤ C * t ^ 3 := by
  have jointCanceledNumerator_contDiffAt {q : (ℝ × ℂ) × ℝ} (hq : 0 < q.1.1) := 
    jointCanceledNumerator_contDiffOn.contDiffAt
      ((isOpen_lt continuous_const (by fun_prop : Continuous fun p : (ℝ × ℂ) × ℝ => p.1.1)).mem_nhds hq)
  let v : (ℝ × ℂ) × ℝ := ((0 : ℝ × ℂ), (1 : ℝ))
  let D3 (q : (ℝ × ℂ) × ℝ) : ℂ := iteratedFDeriv ℝ 3 jointCanceledNumerator q (fun _ : Fin 3 => v)
  have hopen : IsOpen {p : (ℝ × ℂ) × ℝ | 0 < p.1.1} :=
    isOpen_lt continuous_const (by fun_prop : Continuous fun p : (ℝ × ℂ) × ℝ => p.1.1)
  have hD3_cont : ContinuousOn D3 {p : (ℝ × ℂ) × ℝ | 0 < p.1.1} :=
    (by fun_prop : Continuous fun f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => (ℝ × ℂ) × ℝ) ℂ =>
      f (fun _ => v)).comp_continuousOn
      (ContinuousOn.continuousOn_iteratedFDeriv jointCanceledNumerator_contDiffOn hopen (by norm_num))
  have hD3_eq (q : (ℝ × ℂ) × ℝ) (hq : 0 < q.1.1) :
      D3 q = iteratedDeriv 3 (fun t : ℝ => jointCanceledNumerator (q.1, t)) q.2 := by
    let line : ℝ → (ℝ × ℂ) × ℝ := fun t => (q.1, t)
    have hlineD : deriv line = fun _ => v :=
      funext fun t => ((hasDerivAt_const t q.1).prodMk (hasDerivAt_id t)).deriv
    have hline2 : iteratedDeriv 2 line = fun _ => 0 := by
      funext t; rw [iteratedDeriv_succ, show iteratedDeriv 1 line = deriv line by simp, hlineD]; simp
    have hline3 : iteratedDeriv 3 line q.2 = 0 := by rw [iteratedDeriv_succ, hline2]; simp
    have hcomp := iteratedDeriv_vcomp_three
      (hg := (by simpa [line] using jointCanceledNumerator_contDiffAt hq : ContDiffAt ℝ 3 jointCanceledNumerator (line q.2)))
      (hf := (by fun_prop : ContDiffAt ℝ 3 line q.2))
    rw [congrFun hline2 q.2, hline3] at hcomp
    simp only [line, hlineD] at hcomp
    rw [ContinuousMultilinearMap.map_coord_zero _ (0 : Fin 2) (by simp),
      ContinuousMultilinearMap.map_coord_zero _ (1 : Fin 2) (by simp)] at hcomp
    simpa [D3, line, v, Function.comp_def] using hcomp.symm
  let K : Set ((ℝ × ℂ) × ℝ) := (Icc (γ₀ / 2) (γ₀ + 1) ×ˢ Metric.closedBall z₀ 1) ×ˢ Icc 0 1
  have hK : IsCompact K := (isCompact_Icc.prod (isCompact_closedBall z₀ 1)).prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (hD3_cont.mono fun p hp => lt_of_lt_of_le (half_pos hγ₀) hp.1.1.1)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans
    (hM ((γ₀, z₀), 0) ⟨⟨⟨by linarith, by linarith⟩, Metric.mem_closedBall_self zero_le_one⟩, by norm_num⟩)
  refine ⟨M, hM0, fun γ z t hγ hz ht => ?_⟩
  have hγpos := lt_of_lt_of_le (half_pos hγ₀) hγ.1
  let f : ℝ → ℂ := fun s => jointCanceledNumerator ((γ, z), s)
  have hfAt (y : ℝ) : ContDiffAt ℝ 3 f y :=
    (jointCanceledNumerator_contDiffAt (q := ((γ, z), y)) hγpos).comp y (by fun_prop)
  have hderiv (y : ℝ) (hy : y ∈ Icc 0 1) : ‖iteratedDerivWithin 3 f (Icc 0 1) y‖ ≤ M := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) (hfAt y) hy,
      ← hD3_eq ((γ, z), y) hγpos]
    exact hM ((γ, z), y) ⟨⟨hγ, Metric.mem_closedBall.2 (by simpa [dist_eq_norm] using hz)⟩, hy⟩
  let g : ℂ → ℂ := fun ζ => jointComplexNumerator (((γ : ℂ), z), ζ)
  have hgC3 : ContDiff ℂ 3 g := by
    change ContDiff ℂ 3 fun ζ : ℂ =>
      ((γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z) ^ 2 * Complex.exp (-ζ) *
        (Complex.sinh (ζ * (γ : ℂ) / 4) * Complex.sinh (ζ / (γ : ℂ))) -
      Complex.sinh (((γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z) * (ζ / 2)) ^ 2
    fun_prop
  let g' : ℂ → ℂ := fun ζ =>
    let w := (γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z
    w ^ 2 * Complex.exp (-ζ) *
        ((γ : ℂ) / 4 * Complex.cosh (ζ * (γ : ℂ) / 4) * Complex.sinh (ζ / (γ : ℂ)) +
          (γ : ℂ)⁻¹ * Complex.sinh (ζ * (γ : ℂ) / 4) * Complex.cosh (ζ / (γ : ℂ)) -
          Complex.sinh (ζ * (γ : ℂ) / 4) * Complex.sinh (ζ / (γ : ℂ))) -
      w * Complex.sinh (w * (ζ / 2)) * Complex.cosh (w * (ζ / 2))
  have hg_deriv : deriv g = g' := by
    ext ζ
    change deriv (fun ζ : ℂ =>
      ((γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z) ^ 2 * Complex.exp (-ζ) *
        (Complex.sinh (ζ * (γ : ℂ) / 4) * Complex.sinh (ζ / (γ : ℂ))) -
      Complex.sinh (((γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z) * (ζ / 2)) ^ 2) ζ = _
    simp (disch := fun_prop) [g', deriv_csinh, deriv_cexp]; ring_nf
  have hdr (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
      deriv (fun s : ℝ => F (s : ℂ)) = fun s : ℝ => deriv F (s : ℂ) :=
    funext fun s => (hF s).hasDerivAt.comp_ofReal.deriv
  have hgDiff : Differentiable ℂ g := hgC3.differentiable (by norm_num)
  have hg'Diff : Differentiable ℂ (deriv g) := by
    simpa [iteratedDeriv_succ] using (hgC3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).differentiable_iteratedDeriv' 1
  have hf0 : iteratedDerivWithin 0 f (Icc 0 1) 0 = 0 := by
    simp [f, jointCanceledNumerator, jointComplexNumerator]
  have hf1 : iteratedDerivWithin 1 f (Icc 0 1) 0 = 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) ((hfAt 0).of_le (by norm_num)) (by simp)]
    change iteratedDeriv 1 (fun s : ℝ => g (s : ℂ)) 0 = 0
    rw [iteratedDeriv_succ, iteratedDeriv_zero, hdr g hgDiff, hg_deriv]
    simp [g']
  have hf2 : iteratedDerivWithin 2 f (Icc 0 1) 0 = 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) ((hfAt 0).of_le (by norm_num)) (by simp)]
    change iteratedDeriv 2 (fun s : ℝ => g (s : ℂ)) 0 = 0
    rw [iteratedDeriv_succ, show iteratedDeriv 1 (fun s : ℝ => g (s : ℂ)) = deriv (fun s : ℝ => g (s : ℂ)) by simp,
      hdr g hgDiff, hdr (deriv g) hg'Diff]
    dsimp only
    rw [Complex.ofReal_zero, hg_deriv]
    dsimp only [g']
    simp (disch := fun_prop) [deriv_csinh, deriv_ccosh, deriv_cexp]
    field_simp [Complex.ofReal_ne_zero.2 hγpos.ne']; ring
  have hTay := taylor_mean_remainder_bound (f := f) (a := 0) (b := 1) (C := M) (x := t) (n := 2)
    zero_le_one (fun y _ => (hfAt y).contDiffWithinAt) ht hderiv
  have ht0 : taylorWithinEval f 2 (Icc 0 1) 0 t = 0 := by
    rw [taylor_within_apply]; simp [Finset.sum_range_succ, hf0, hf1, hf2]
  rw [ht0] at hTay; norm_num at hTay
  exact hTay.trans (by nlinarith [mul_nonneg hM0 (pow_nonneg ht.1 3)])

theorem upsilonLog_continuousAt_joint (hz₀ : 0 < z₀.re) (hzQ₀ : z₀.re < Q γ₀) :
    ContinuousAt (Function.uncurry upsilonLog) (γ₀, z₀) := by
  let gap := Q γ₀ - z₀.re
  have hγ₀ne := hγ₀.ne'
  have hQcont : ContinuousAt (fun γ : ℝ => Q γ) γ₀ := by fun_prop (disch := assumption) [Q]
  obtain ⟨δQ, hδQ, hQδ⟩ := Metric.continuousAt_iff.mp hQcont (gap / 8) (by dsimp [gap]; linarith)
  let ρz := min (z₀.re / 4) (min (gap / 8) 1)
  have hρz : 0 < ρz := lt_min (by positivity) (lt_min (by dsimp [gap]; linarith) zero_lt_one)
  let ε := min (δQ / 2) (min (γ₀ / 2) ρz)
  have hε : 0 < ε := lt_min (half_pos hδQ) (lt_min (half_pos hγ₀) hρz)
  obtain ⟨C, hC, hTaylor⟩ := exists_jointNumerator_taylor_bound (γ₀ := γ₀) (z₀ := z₀) hγ₀
  let η := min (z₀.re / 4) (gap / 4)
  have hη : 0 < η := lt_min (by positivity) (by dsimp [gap]; linarith)
  let κ := ((1 - Real.exp (-2 * (γ₀ / 2 / 4))) / 2) * ((1 - Real.exp (-2 * (1 / (γ₀ + 1)))) / 2)
  have hκ : 0 < κ := by
    have h1 : Real.exp (-2 * (γ₀ / 2 / 4)) < 1 :=
      Real.exp_lt_one_iff.2 (by linarith [show 0 < γ₀ / 2 / 4 by positivity])
    have h2 : Real.exp (-2 * (1 / (γ₀ + 1))) < 1 :=
      Real.exp_lt_one_iff.2 (by linarith [show 0 < 1 / (γ₀ + 1) by positivity])
    dsimp [κ]; positivity
  let W₀ := (γ₀ + 1) / 4 + 2 / γ₀ + ‖z₀‖ + 1
  let B (t : ℝ) : ℝ := (4 * C * Real.exp 1 + W₀ ^ 2) * Real.exp (-t) + κ⁻¹ * Real.exp (-η * t)
  have hBint : Integrable B (volume.restrict (Ioi 0)) := by
    have i1 : Integrable (fun t : ℝ => (4 * C * Real.exp 1 + W₀ ^ 2) * Real.exp (-t)) (volume.restrict (Ioi 0)) := by
      simpa [mul_comm] using (exp_neg_integrableOn_Ioi 0 (b := 1) zero_lt_one).const_mul (4 * C * Real.exp 1 + W₀ ^ 2)
    have i2 : Integrable (fun t : ℝ => κ⁻¹ * Real.exp (-η * t)) (volume.restrict (Ioi 0)) := by
      simpa [mul_comm] using (exp_neg_integrableOn_Ioi 0 (b := η) hη).const_mul κ⁻¹
    exact i1.add i2
  let F : ℝ × ℂ → ℝ → ℂ := fun p t => upsilonLogIntegrand p.1 p.2 t
  refine continuousAt_of_dominated
    (Eventually.of_forall fun p => (upsilonLogIntegrand_aestronglyMeasurable p.1 p.2).restrict)
    ?_ hBint ?_
  · filter_upwards [Metric.ball_mem_nhds (γ₀, z₀) hε] with p hp
    have hp' : max (dist p.1 γ₀) (dist p.2 z₀) < ε := by simpa [Prod.dist_eq] using hp
    have hγabs : |p.1 - γ₀| < ε := by simpa [Real.dist_eq] using (max_lt_iff.1 hp').1
    have hερ : ε ≤ ρz := (min_le_right _ _).trans (min_le_right _ _)
    have hρ1 : ρz ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
    have hγmem : p.1 ∈ Icc (γ₀ / 2) (γ₀ + 1) :=
      ⟨by linarith [(abs_lt.1 hγabs).1, (min_le_right (δQ / 2) _).trans (min_le_left (γ₀ / 2) ρz)],
       by linarith [(abs_lt.1 hγabs).2, hερ, hρ1]⟩
    have hγpos : 0 < p.1 := lt_of_lt_of_le (half_pos hγ₀) hγmem.1
    have hQclose : |Q p.1 - Q γ₀| < gap / 8 := by
      simpa [Real.dist_eq] using hQδ ((max_lt_iff.1 hp').1.trans_le ((min_le_left _ _).trans (half_lt_self hδQ).le))
    have hznorm : ‖p.2 - z₀‖ < ρz :=
      (by simpa [dist_eq_norm] using (max_lt_iff.1 hp').2 : ‖p.2 - z₀‖ < ε).trans_le hερ
    have hzre : |p.2.re - z₀.re| < ρz := (Complex.abs_re_le_norm (p.2 - z₀)).trans_lt hznorm
    have hleft : η < p.2.re := by
      linarith [(abs_lt.1 hzre).1, min_le_left (z₀.re / 4) (gap / 4), min_le_left (z₀.re / 4) (min (gap / 8) 1)]
    have hright : η < Q p.1 - p.2.re := by
      have : ρz ≤ gap / 8 := (min_le_right _ _).trans (min_le_left _ _)
      have : η ≤ gap / 4 := min_le_right _ _
      dsimp [gap] at *; linarith [(abs_lt.1 hQclose).1, (abs_lt.1 hzre).2]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    by_cases ht1 : t ≤ 1
    · have hN := hTaylor p.1 p.2 t hγmem (hznorm.le.trans hρ1) ⟨ht.le, ht1⟩
      have hDen := realDenom_pos hγpos ht
      have hDt : t ^ 3 / 4 ≤ realDenom p.1 t * t := by
        linarith [mul_le_mul_of_nonneg_right (realDenom_ge_quadratic hγpos ht) ht.le]
      have hId : upsilonLogIntegrand p.1 p.2 t =
          jointCanceledNumerator ((p.1, p.2), t) / ((realDenom p.1 t : ℂ) * (t : ℂ)) := by
        have hqR : (p.1 : ℂ) / 4 + (p.1 : ℂ)⁻¹ = (Q p.1 / 2 : ℝ) := by
          exact_mod_cast (show p.1 / 4 + p.1⁻¹ = Q p.1 / 2 by unfold Q; field_simp [hγpos.ne']; ring)
        have hnum : jointCanceledNumerator ((p.1, p.2), t) =
            (Q p.1 / 2 - p.2) ^ 2 * Real.exp (-t) *
              (Real.sinh (t * p.1 / 4) * Real.sinh (t / p.1) : ℂ) -
            Complex.sinh ((Q p.1 / 2 - p.2) * (t / 2)) ^ 2 := by
          simp only [jointCanceledNumerator, jointComplexNumerator]; rw [hqR]
          simp only [Complex.ofReal_exp, Complex.ofReal_sinh, Complex.ofReal_neg,
            Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
        rw [upsilonLogIntegrand, hnum, realDenom, Complex.ofReal_mul]
        have hs1 : (Real.sinh (t * p.1 / 4) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.2 (Real.sinh_pos_iff.2 (by positivity)).ne'
        have hs2 : (Real.sinh (t / p.1) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.2 (Real.sinh_pos_iff.2 (div_pos ht hγpos)).ne'
        field_simp [Complex.ofReal_ne_zero.2 ht.ne', hs1, hs2]
      have h4C : ‖F p t‖ ≤ 4 * C := by
        dsimp [F]
        rw [hId, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hDen.le, Real.norm_of_nonneg ht.le]
        exact (div_le_div_of_nonneg_right hN (mul_pos hDen ht).le).trans
          ((div_le_iff₀ (mul_pos hDen ht)).2 (by nlinarith))
      have he : 1 ≤ Real.exp 1 * Real.exp (-t) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
      refine h4C.trans ?_
      dsimp [B]
      have : 0 ≤ κ⁻¹ * Real.exp (-η * t) := by positivity
      have : 0 ≤ W₀ ^ 2 * Real.exp (-t) := by positivity
      nlinarith
    · have ht1' : 1 ≤ t := le_of_not_ge ht1
      have hinv : 1 / p.1 ≤ 2 / γ₀ :=
        (one_div_le_one_div_of_le (half_pos hγ₀) hγmem.1).trans_eq (by field_simp [hγ₀ne])
      have hQhalf : Q p.1 / 2 ≤ (γ₀ + 1) / 4 + 2 / γ₀ := by
        unfold Q; linarith [hγmem.2, hinv, show 2 / p.1 = 2 * (1 / p.1) by ring]
      have hQpos : 0 ≤ Q p.1 / 2 := by unfold Q; positivity
      have hW : ‖(Q p.1 / 2 : ℂ) - p.2‖ ≤ W₀ := by
        have hzn : ‖p.2‖ ≤ ‖z₀‖ + 1 := by
          linarith [norm_sub_rev p.2 z₀, norm_sub_norm_le p.2 z₀, hznorm.le, hρ1]
        have hQn : ‖(Q p.1 / 2 : ℂ)‖ = Q p.1 / 2 := by
          rw [ ← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.norm_real, Real.norm_of_nonneg hQpos]
        dsimp [W₀]; linarith [norm_sub_le (Q p.1 / 2 : ℂ) p.2, hQn, hQhalf, hzn]
      have hw2 : ‖(Q p.1 / 2 : ℂ) - p.2‖ ^ 2 ≤ W₀ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hW 2
      have hκle : κ ≤ tailConst p.1 := by
        have he1 : Real.exp (-2 * (p.1 / 4)) ≤ Real.exp (-2 * (γ₀ / 2 / 4)) :=
          Real.exp_le_exp.2 (by linarith [hγmem.1])
        have he2 : Real.exp (-2 * (1 / p.1)) ≤ Real.exp (-2 * (1 / (γ₀ + 1))) :=
          Real.exp_le_exp.2 (by linarith [one_div_le_one_div_of_le hγpos hγmem.2])
        have hp1 : 0 ≤ (1 - Real.exp (-2 * (γ₀ / 2 / 4))) / 2 :=
          div_nonneg (sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith))) zero_le_two
        have hp2 : 0 ≤ (1 - Real.exp (-2 * (1 / (γ₀ + 1)))) / 2 :=
          div_nonneg (sub_nonneg.2 (Real.exp_le_one_iff.2
            (by linarith [show 0 < 1 / (γ₀ + 1) by positivity]))) zero_le_two
        dsimp [κ]; unfold tailConst
        exact mul_le_mul (by linarith) (by linarith) hp2 (by linarith)
      have habs : |Q p.1 / 2 - p.2.re| ≤ Q p.1 / 2 - η :=
        abs_le.2 ⟨by linarith, by linarith⟩
      have hExp : Real.exp (-(Q p.1 / 2 - |Q p.1 / 2 - p.2.re|) * t) ≤ Real.exp (-η * t) :=
        Real.exp_le_exp.2 (by nlinarith)
      refine (upsilonLogIntegrand_norm_le_tail hγpos p.2 (by linarith) (by linarith) ht1').trans ?_
      dsimp [B]
      have h2 := mul_le_mul ((inv_le_inv₀ (tailConst_pos hγpos) hκ).2 hκle) hExp
        (Real.exp_nonneg _) (inv_pos.2 hκ).le
      have h1 := mul_le_mul_of_nonneg_right hw2 (Real.exp_nonneg (-t))
      have hC0 : 0 ≤ 4 * C * Real.exp 1 * Real.exp (-t) := by positivity
      linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    let w : ℝ × ℂ → ℂ := fun p => Q p.1 / 2 - p.2
    let D : ℝ × ℂ → ℂ := fun p => (Real.sinh (t * p.1 / 4) : ℂ) * (Real.sinh (t / p.1) : ℂ)
    have hw : ContinuousAt w (γ₀, z₀) := by dsimp [w]; fun_prop (disch := assumption) [Q]
    have hD : ContinuousAt D (γ₀, z₀) := by dsimp [D]; fun_prop
    have hDne : D (γ₀, z₀) ≠ 0 := mul_ne_zero
      (Complex.ofReal_ne_zero.2 (Real.sinh_pos_iff.2 (by positivity)).ne')
      (Complex.ofReal_ne_zero.2 (Real.sinh_pos_iff.2 (div_pos ht hγ₀)).ne')
    have hA : ContinuousAt (fun p : ℝ × ℂ => w p ^ 2 * Real.exp (-t)) (γ₀, z₀) := by fun_prop
    have hS : ContinuousAt (fun p : ℝ × ℂ => Complex.sinh (w p * (t / 2)) ^ 2) (γ₀, z₀) := by fun_prop
    have hres : ContinuousAt (fun p : ℝ × ℂ =>
        (w p ^ 2 * Real.exp (-t) - Complex.sinh (w p * (t / 2)) ^ 2 / D p) / (t : ℂ)) (γ₀, z₀) :=
      (hA.sub (hS.div hD hDne)).div continuousAt_const (Complex.ofReal_ne_zero.2 ht.ne')
    simpa [F, upsilonLogIntegrand, w, D] using hres


end
end DOZZ.Proofs

end
