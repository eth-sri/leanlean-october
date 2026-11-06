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

private theorem jointComplexNumerator_contDiffAt {q : (ℂ × ℂ) × ℂ}
    (hq : q.1.1 ≠ 0) : ContDiffAt ℂ 3 jointComplexNumerator q := by
  unfold jointComplexNumerator
  fun_prop

private theorem jointCanceledNumerator_contDiffOn :
    ContDiffOn ℝ 3 jointCanceledNumerator {p | 0 < p.1.1} := by
  intro p hp
  have hp0 : p.1.1 ≠ 0 := ne_of_gt hp
  have hγproj : ContDiffAt ℝ 3 (fun x => x.1.1) p := by fun_prop
  have hzproj : ContDiffAt ℝ 3 (fun x => x.1.2) p := by fun_prop
  have htproj : ContDiffAt ℝ 3 (fun x => x.2) p := by fun_prop
  have hγcast : ContDiffAt ℝ 3 (fun x => (x.1.1 : ℂ)) p := by
    exact ContDiffAt.comp p Complex.ofRealCLM.contDiff.contDiffAt hγproj
  have htcast : ContDiffAt ℝ 3 (fun x => (x.2 : ℂ)) p := by
    exact ContDiffAt.comp p Complex.ofRealCLM.contDiff.contDiffAt htproj
  have hmap : ContDiffAt ℝ 3 jointToComplex p := by
    change ContDiffAt ℝ 3
      (fun x => (((x.1.1 : ℂ), x.1.2), (x.2 : ℂ))) p
    fun_prop
  have hq0 : (jointToComplex p).1.1 ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact hp0
  have hnumAt : ContDiffAt ℝ 3 jointComplexNumerator (jointToComplex p) :=
    (jointComplexNumerator_contDiffAt hq0).restrict_scalars ℝ
  have hAt : ContDiffAt ℝ 3 jointCanceledNumerator p := by
    change ContDiffAt ℝ 3 (jointComplexNumerator ∘ jointToComplex) p
    fun_prop
  fun_prop

private noncomputable def jointThirdDerivative (q : (ℝ × ℂ) × ℝ) : ℂ :=
  iteratedFDeriv ℝ 3 jointCanceledNumerator q (fun _ : Fin 3 => ((0 : ℝ × ℂ), (1 : ℝ)))

private theorem jointCanceledNumerator_contDiffAt {q : (ℝ × ℂ) × ℝ}
    (hq : 0 < q.1.1) : ContDiffAt ℝ 3 jointCanceledNumerator q := by
  have hproj : Continuous (fun p : (ℝ × ℂ) × ℝ => p.1.1) := by fun_prop
  have hopen : IsOpen {p : (ℝ × ℂ) × ℝ | 0 < p.1.1} :=
    isOpen_lt continuous_const hproj
  exact jointCanceledNumerator_contDiffOn.contDiffAt (hopen.mem_nhds hq)

private theorem jointThirdDerivative_eq_iteratedDeriv
    (q : (ℝ × ℂ) × ℝ) (hq : 0 < q.1.1) :
    jointThirdDerivative q =
      iteratedDeriv 3 (fun t : ℝ => jointCanceledNumerator (q.1, t)) q.2 := by
  let line : ℝ → (ℝ × ℂ) × ℝ := fun t => (q.1, t)
  let v : (ℝ × ℂ) × ℝ := (0, 1)
  have hline : HasDerivAt line v q.2 := by
    simpa [line, v] using (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  have hlineD : deriv line = fun _ => v := by
    funext t
    exact ((hasDerivAt_const t q.1).prodMk (hasDerivAt_id t)).deriv
  have hline2 : iteratedDeriv 2 line q.2 = 0 := by
    rw [iteratedDeriv_succ, show iteratedDeriv 1 line = deriv line by simp, hlineD]
    simp
  have hline3 : iteratedDeriv 3 line q.2 = 0 := by
    rw [iteratedDeriv_succ]
    rw [show iteratedDeriv 2 line = fun _ => 0 by
      funext t
      rw [iteratedDeriv_succ, show iteratedDeriv 1 line = deriv line by simp, hlineD]
      simp]
    simp
  have hH : ContDiffAt ℝ 3 jointCanceledNumerator (line q.2) := by
    simpa [line] using jointCanceledNumerator_contDiffAt hq
  have hcomp := iteratedDeriv_vcomp_three
    (hg := hH)
    (hf := (by fun_prop))
  rw [hline2, hline3] at hcomp
  simp only [line, hlineD] at hcomp
  have hcross₁ :
      iteratedFDeriv ℝ 2 jointCanceledNumerator q ![0, v] = 0 := by
    apply ContinuousMultilinearMap.map_coord_zero _ 0
    simp
  have hcross₂ :
      iteratedFDeriv ℝ 2 jointCanceledNumerator q ![v, 0] = 0 := by
    apply ContinuousMultilinearMap.map_coord_zero _ 1
    simp
  rw [hcross₁, hcross₂] at hcomp
  simp at hcomp
  simpa [jointThirdDerivative, line, v, Function.comp_def] using hcomp.symm

private theorem jointThirdDerivative_continuousOn :
    ContinuousOn jointThirdDerivative {p : (ℝ × ℂ) × ℝ | 0 < p.1.1} := by
  have hproj : Continuous (fun p : (ℝ × ℂ) × ℝ => p.1.1) := by fun_prop
  have hopen : IsOpen {p : (ℝ × ℂ) × ℝ | 0 < p.1.1} :=
    isOpen_lt continuous_const hproj
  have hfd : ContinuousOn (iteratedFDeriv ℝ 3 jointCanceledNumerator)
      {p : (ℝ × ℂ) × ℝ | 0 < p.1.1} :=
    ContinuousOn.continuousOn_iteratedFDeriv jointCanceledNumerator_contDiffOn
      hopen (by norm_num)
  have heval : Continuous (fun f : ContinuousMultilinearMap ℝ
      (fun _ : Fin 3 => (ℝ × ℂ) × ℝ) ℂ =>
      f (fun _ => (0, 1))) := by
    fun_prop
  change ContinuousOn
    (fun q => iteratedFDeriv ℝ 3 jointCanceledNumerator q
      (fun _ => (0, 1)))
    {p : (ℝ × ℂ) × ℝ | 0 < p.1.1}
  exact heval.comp_continuousOn hfd

private theorem exists_jointThirdDerivative_bound {γ₀ : ℝ} {z₀ : ℂ}
    (hγ₀ : 0 < γ₀) :
    ∃ M : ℝ, ∀ (γ : ℝ) (z : ℂ) (t : ℝ),
      γ ∈ Set.Icc (γ₀ / 2) (γ₀ + 1) → ‖z - z₀‖ ≤ 1 → t ∈ Set.Icc 0 1 →
      ‖iteratedDeriv 3 (fun s : ℝ => jointCanceledNumerator ((γ, z), s)) t‖ ≤ M := by
  let K : Set ((ℝ × ℂ) × ℝ) :=
    (Set.Icc (γ₀ / 2) (γ₀ + 1) ×ˢ Metric.closedBall z₀ 1) ×ˢ Set.Icc 0 1
  have hKcompact : IsCompact K := by
    exact (isCompact_Icc.prod (isCompact_closedBall z₀ 1)).prod isCompact_Icc
  have hKpos : K ⊆ {p : (ℝ × ℂ) × ℝ | 0 < p.1.1} := by
    grind
  obtain ⟨M, hM⟩ := hKcompact.exists_bound_of_continuousOn
    (jointThirdDerivative_continuousOn.mono hKpos)
  refine ⟨M, ?_⟩
  intro γ z t hγ hz ht
  have hq : ((γ, z), t) ∈ K := by
    exact ⟨⟨hγ, Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hz)⟩, ht⟩
  have hM' := hM _ hq
  rw [jointThirdDerivative_eq_iteratedDeriv _
    (lt_of_lt_of_le (by positivity) hγ.1)] at hM'
  simpa using hM'

private noncomputable def jointNumeratorAt (γ : ℝ) (z : ℂ) : ℝ → ℂ :=
  fun t => jointCanceledNumerator ((γ, z), t)

private noncomputable def jointNumeratorComplexAt (γ : ℝ) (z : ℂ) : ℂ → ℂ :=
  fun t => jointComplexNumerator (((γ : ℂ), z), t)

private theorem jointNumeratorAt_eq_complex_restrict (γ : ℝ) (z : ℂ) :
    jointNumeratorAt γ z = fun t : ℝ => jointNumeratorComplexAt γ z t := by
  rfl

private theorem deriv_real_restrict (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    deriv (fun t : ℝ => F (t : ℂ)) = fun t : ℝ => deriv F (t : ℂ) := by
  funext t
  exact (hF t).hasDerivAt.comp_ofReal.deriv

private theorem jointNumeratorComplexAt_contDiff {γ : ℝ} (hγ : γ ≠ 0) (z : ℂ) :
    ContDiff ℂ 3 (jointNumeratorComplexAt γ z) := by
  have hγC : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ
  change ContDiff ℂ 3 (fun t =>
    ((γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z) ^ 2 * Complex.exp (-t) *
        (Complex.sinh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ))) -
      Complex.sinh (((γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z) * (t / 2)) ^ 2)
  fun_prop

private noncomputable def jointNumeratorComplexAtDerivative (γ : ℝ) (z t : ℂ) : ℂ :=
  let w := (γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z
  w ^ 2 * Complex.exp (-t) *
      ((γ : ℂ) / 4 * Complex.cosh (t * (γ : ℂ) / 4) *
          Complex.sinh (t / (γ : ℂ)) +
        (γ : ℂ)⁻¹ * Complex.sinh (t * (γ : ℂ) / 4) *
          Complex.cosh (t / (γ : ℂ)) -
        Complex.sinh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ))) -
    w * Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))

private theorem jointNumeratorComplexAt_deriv_eq (γ : ℝ) (z : ℂ) :
    deriv (jointNumeratorComplexAt γ z) = jointNumeratorComplexAtDerivative γ z := by
  funext t
  change deriv (fun t : ℂ =>
    ((γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z) ^ 2 * Complex.exp (-t) *
        (Complex.sinh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ))) -
      Complex.sinh (((γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z) * (t / 2)) ^ 2) t = _
  simp (disch := fun_prop) [jointNumeratorComplexAtDerivative, deriv_csinh,
    deriv_cexp]
  ring_nf
section
variable {γ : ℝ}

private theorem jointNumeratorComplexAt_deriv_zero (z : ℂ) : deriv (jointNumeratorComplexAt γ z) 0 = 0 := by
  rw [jointNumeratorComplexAt_deriv_eq]
  simp [jointNumeratorComplexAtDerivative]

private theorem jointNumeratorComplexAt_iteratedDeriv_two_zero (hγ : γ ≠ 0) (z : ℂ) :
    iteratedDeriv 2 (jointNumeratorComplexAt γ z) 0 = 0 := by
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
  have hγC : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ
  grind

end

private theorem jointNumerator_taylorWithinEval_zero (γ : ℝ) (z : ℂ)
    (hγ : 0 < γ) (t : ℝ) :
    taylorWithinEval (jointNumeratorAt γ z) 2 (Set.Icc 0 1) 0 t = 0 := by
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
    change iteratedDeriv 2 (fun t : ℝ => jointNumeratorComplexAt γ z t) 0 = 0
    rw [iteratedDeriv_succ]
    rw [show iteratedDeriv 1 (fun t : ℝ => jointNumeratorComplexAt γ z t) =
        deriv (fun t : ℝ => jointNumeratorComplexAt γ z t) by simp]
    rw [deriv_real_restrict _ hF]
    have hF' : Differentiable ℂ (deriv (jointNumeratorComplexAt γ z)) := by
      fun_prop
    calc
      deriv (fun t : ℝ => deriv (jointNumeratorComplexAt γ z) t) 0 =
          deriv (deriv (jointNumeratorComplexAt γ z)) 0 := ((hF' 0).hasDerivAt.comp_ofReal.deriv)
      _ = iteratedDeriv 2 (jointNumeratorComplexAt γ z) 0 := by
        rw [iteratedDeriv_succ]
        simp
      _ = 0 := jointNumeratorComplexAt_iteratedDeriv_two_zero (γ := γ)
        hγ.ne' z
  have hfAt : ContDiffAt ℝ 3 f 0 := by
    have hline : ContDiffAt ℝ 3 (fun s : ℝ => ((γ, z), s)) 0 := by fun_prop
    exact ContDiffAt.comp 0 (jointCanceledNumerator_contDiffAt (q := ((γ, z), 0)) hγ) hline
  have h0 : iteratedDerivWithin 0 f (Set.Icc 0 1) 0 = 0 := by
    assumption
  have h1 : iteratedDerivWithin 1 f (Set.Icc 0 1) 0 = 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (by norm_num))
      (hfAt.of_le (by norm_num)) (by simp)]
    simp_all
  have h2 : iteratedDerivWithin 2 f (Set.Icc 0 1) 0 = 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (by norm_num))
      (hfAt.of_le (by norm_num)) (by simp)]
    exact hftwo
  aesop

private theorem exists_jointNumerator_taylor_bound {γ₀ : ℝ} {z₀ : ℂ}
    (hγ₀ : 0 < γ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : ℝ) (z : ℂ) (t : ℝ),
      γ ∈ Set.Icc (γ₀ / 2) (γ₀ + 1) → ‖z - z₀‖ ≤ 1 → t ∈ Set.Icc 0 1 →
      ‖jointNumeratorAt γ z t‖ ≤ C * t ^ 3 := by
  obtain ⟨M, hM⟩ := exists_jointThirdDerivative_bound (z₀ := z₀) hγ₀
  have hMnonneg : 0 ≤ M := by
    have h := hM γ₀ z₀ 0 (by grind) (by norm_num) (by norm_num)
    exact (norm_nonneg _).trans h
  refine ⟨M, hMnonneg, ?_⟩
  intro γ z t hγ hz ht
  have hγpos := lt_of_lt_of_le (by positivity) hγ.1
  let f := jointNumeratorAt γ z
  have hfCont : ContDiffOn ℝ 3 f (Set.Icc 0 1) := by
    intro y hy
    have hline : ContDiffAt ℝ 3 (fun s => ((γ, z), s)) y := by fun_prop
    exact (ContDiffAt.comp y (jointCanceledNumerator_contDiffAt hγpos) hline).contDiffWithinAt
  have hderiv : ∀ y ∈ Set.Icc 0 1,
      ‖iteratedDerivWithin 3 f (Set.Icc 0 1) y‖ ≤ M := by
    intro y hy
    have hline : ContDiffAt ℝ 3 (fun s => ((γ, z), s)) y := by fun_prop
    have hcomp := ContDiffAt.comp y (jointCanceledNumerator_contDiffAt hγpos) hline
    change ContDiffAt ℝ 3 f y at hcomp
    have hEq :=
      iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
      hcomp hy
    rw [hEq]
    exact hM γ z y hγ hz hy
  have hTaylor := taylor_mean_remainder_bound
    (by norm_num) hfCont ht hderiv
  rw [jointNumerator_taylorWithinEval_zero γ z hγpos t] at hTaylor
  norm_num at hTaylor
  have hnonneg : 0 ≤ M * t ^ 3 := mul_nonneg hMnonneg (pow_nonneg ht.1 _)
  exact hTaylor.trans (by linarith)
section
variable {γ : ℝ}
section
variable (hγ : 0 < γ) (z : ℂ)
include hγ

private theorem jointW_eq_source :
    (γ : ℂ) / 4 + (γ : ℂ)⁻¹ - z = (Q γ / 2 : ℝ) - z := by
  have hqR : Q γ / 2 = γ / 4 + γ⁻¹ := by
    unfold Q
    ring
  simp_all

private theorem jointNumeratorAt_eq_source (t : ℝ) :
    jointNumeratorAt γ z t =
      (Q γ / 2 - z) ^ 2 * Real.exp (-t) *
          (Real.sinh (t * γ / 4) * Real.sinh (t / γ) : ℂ) -
        Complex.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2 := by
  simp only [jointNumeratorAt, jointCanceledNumerator, jointToComplex,
    jointComplexNumerator]
  rw [jointW_eq_source hγ z]
  simp

private theorem upsilonLogIntegrand_eq_jointNumerator_div {t : ℝ} (ht : 0 < t) :
    upsilonLogIntegrand γ z t =
      jointNumeratorAt γ z t / ((realDenom γ t : ℂ) * (t : ℂ)) := by
  rw [upsilonLogIntegrand, jointNumeratorAt_eq_source hγ]
  have hD : (realDenom γ t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (realDenom_pos hγ ht).ne'
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hS₁ : (Real.sinh (t * γ / 4) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.2 (by positivity)).ne'
  have hS₂ : (Real.sinh (t / γ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.2 (div_pos ht hγ)).ne'
  have hRD : (realDenom γ t : ℂ) =
      (Real.sinh (t * γ / 4) : ℂ) * (Real.sinh (t / γ) : ℂ) := by
    norm_cast
  grind

private theorem upsilonLogIntegrand_norm_le_jointTaylor {C t : ℝ} (hC : 0 ≤ C)
    (hN : ‖jointNumeratorAt γ z t‖ ≤ C * t ^ 3)
    (ht : 0 < t) :
    ‖upsilonLogIntegrand γ z t‖ ≤ 4 * C := by
  have hDen := realDenom_pos hγ ht
  have hDLower := realDenom_ge_quadratic hγ ht
  have hDt : t ^ 3 / 4 ≤ realDenom γ t * t := by
    nlinarith
  have hDtPos := mul_pos hDen ht
  have hnormDen : ‖(realDenom γ t) * (t : ℂ)‖ = realDenom γ t * t := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hDen, abs_of_pos ht]
  rw [upsilonLogIntegrand_eq_jointNumerator_div hγ z ht, norm_div, hnormDen]
  calc
    ‖jointNumeratorAt γ z t‖ / (realDenom γ t * t) ≤
        (C * t ^ 3) / (realDenom γ t * t) :=
      div_le_div_of_nonneg_right hN (le_of_lt hDtPos)
    _ ≤ 4 * C := (div_le_iff₀ hDtPos).2 <| by
      nlinarith

end

end

private noncomputable def jointTailLower (γ₀ : ℝ) : ℝ :=
  ((1 - Real.exp (-2 * (γ₀ / 2 / 4))) / 2) *
    ((1 - Real.exp (-2 * (1 / (γ₀ + 1)))) / 2)

private theorem jointTailLower_pos {γ₀ : ℝ} (hγ₀ : 0 < γ₀) :
    0 < jointTailLower γ₀ := by
  have ha : 0 < γ₀ / 2 / 4 := by positivity
  have hb : 0 < 1 / (γ₀ + 1) := by positivity
  have h₁ : -2 * (γ₀ / 2 / 4) < 0 := by linarith
  have h₂ : -2 * (1 / (γ₀ + 1)) < 0 := by linarith
  have he₁ := Real.exp_lt_one_iff.mpr h₁
  have he₂ := Real.exp_lt_one_iff.mpr h₂
  unfold jointTailLower
  positivity
section
variable {γ₀ γ : ℝ}
section
variable (hγ₀ : 0 < γ₀) (hγ : γ ∈ Set.Icc (γ₀ / 2) (γ₀ + 1))
include hγ₀ hγ

private theorem jointTailLower_le :
    jointTailLower γ₀ ≤ tailConst γ := by
  have hγpos := lt_of_lt_of_le (by positivity) hγ.1
  have ha : 0 < γ₀ / 2 / 4 := by positivity
  have hb : 0 < 1 / (γ₀ + 1) := by positivity
  have hinv :=
    one_div_le_one_div_of_le hγpos hγ.2
  have he₁ : Real.exp (-2 * (γ / 4)) ≤ Real.exp (-2 * (γ₀ / 2 / 4)) :=
    Real.exp_le_exp.mpr (by grind)
  have he₂ : Real.exp (-2 * (1 / γ)) ≤ Real.exp (-2 * (1 / (γ₀ + 1))) :=
    by simp_all
  have hbase1 : -2 * (γ₀ / 2 / 4) < 0 := by
    linarith
  have hbase2 : -2 * (1 / (γ₀ + 1)) < 0 := by
    linarith
  have h₁ : 0 ≤ (1 - Real.exp (-2 * (γ₀ / 2 / 4))) / 2 := by
    have he : Real.exp (-2 * (γ₀ / 2 / 4)) < 1 := Real.exp_lt_one_iff.mpr hbase1
    positivity
  have h₂ : 0 ≤ (1 - Real.exp (-2 * (1 / (γ₀ + 1)))) / 2 := by
    have he : Real.exp (-2 * (1 / (γ₀ + 1))) < 1 := Real.exp_lt_one_iff.mpr hbase2
    positivity
  have h₁' : (1 - Real.exp (-2 * (γ₀ / 2 / 4))) / 2 ≤
      (1 - Real.exp (-2 * (γ / 4))) / 2 := by
    linarith
  have h₂' : (1 - Real.exp (-2 * (1 / (γ₀ + 1)))) / 2 ≤
      (1 - Real.exp (-2 * (1 / γ))) / 2 := by
    linarith only [he₂]
  have h₁actual :=
    le_trans h₁ h₁'
  exact mul_le_mul h₁' h₂' h₂ h₁actual

private theorem Q_le_jointUpper :
    Q γ ≤ (γ₀ + 1) / 2 + 4 / γ₀ := by
  have hγpos := lt_of_lt_of_le (by positivity) hγ.1
  have hinv₁ :=
    one_div_le_one_div_of_le (by positivity) hγ.1
  have hinv : 1 / γ ≤ 2 / γ₀ := by
    linarith
  have hinv2 : 2 / γ ≤ 4 / γ₀ := by
    grind
  have hγhalf : γ / 2 ≤ (γ₀ + 1) / 2 :=
    by grind
  unfold Q
  linarith

end

end

private noncomputable def jointStripMargin (γ₀ : ℝ) (z₀ : ℂ) : ℝ :=
  min (z₀.re / 4) ((Q γ₀ - z₀.re) / 4)

private noncomputable def jointWBound (γ₀ : ℝ) (z₀ : ℂ) : ℝ :=
  (γ₀ + 1) / 4 + 2 / γ₀ + ‖z₀‖ + 1

private noncomputable def jointMajorant (γ₀ : ℝ) (z₀ : ℂ) (C t : ℝ) : ℝ :=
  (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t) +
    (jointTailLower γ₀)⁻¹ * Real.exp (-jointStripMargin γ₀ z₀ * t)
section
variable {γ₀ : ℝ} {z₀ : ℂ}

private theorem jointMajorant_integrable {C : ℝ}
    (hγ₀ : 0 < γ₀) (hz₀ : 0 < z₀.re) (hzQ₀ : z₀.re < Q γ₀) (hC : 0 ≤ C) :
    Integrable (jointMajorant γ₀ z₀ C) (volume.restrict (Set.Ioi 0)) := by
  have hη : 0 < jointStripMargin γ₀ z₀ := by
    unfold jointStripMargin
    positivity
  have hA : 0 ≤ 4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2 := by
    positivity
  have hB :=
    le_of_lt (inv_pos.mpr (jointTailLower_pos hγ₀))
  have hmajor₁ : Integrable (fun t =>
      (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t))
      (volume.restrict (Set.Ioi 0)) := by
    simpa [mul_comm] using
      (exp_neg_integrableOn_Ioi 0 (b := 1) (by norm_num)).const_mul
        (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2)
  have hmajor₂ : Integrable (fun t =>
      (jointTailLower γ₀)⁻¹ * Real.exp (-jointStripMargin γ₀ z₀ * t))
      (volume.restrict (Set.Ioi 0)) := by
    simpa [mul_comm] using
      (exp_neg_integrableOn_Ioi 0 hη).const_mul
        ((jointTailLower γ₀)⁻¹)
  change Integrable (fun t =>
      (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t) +
        (jointTailLower γ₀)⁻¹ * Real.exp _)
    (volume.restrict (Set.Ioi 0))
  simp_all
section
variable (hγ₀ : 0 < γ₀) (hz₀ : 0 < z₀.re) (hzQ₀ : z₀.re < Q γ₀)
include hγ₀ hz₀ hzQ₀

private theorem jointIntegrand_norm_le_majorant {C : ℝ} (hC : 0 ≤ C)
    (hTaylor : ∀ γ z t, γ ∈ Set.Icc (γ₀ / 2) (γ₀ + 1) →
      ‖z - z₀‖ ≤ 1 → t ∈ Set.Icc 0 1 →
      ‖jointNumeratorAt γ z t‖ ≤ C * t ^ 3)
    {γ : ℝ} {z : ℂ} (hγ : γ ∈ Set.Icc (γ₀ / 2) (γ₀ + 1))
    (hz : ‖z - z₀‖ ≤ 1)
    (hleft : jointStripMargin γ₀ z₀ < z.re)
    (hright : jointStripMargin γ₀ z₀ < Q γ - z.re)
    {t : ℝ} (ht : 0 < t) :
    ‖upsilonLogIntegrand γ z t‖ ≤ jointMajorant γ₀ z₀ C t := by
  have hγpos := lt_of_lt_of_le (by positivity) hγ.1
  have hη : 0 < jointStripMargin γ₀ z₀ := by
    unfold jointStripMargin
    positivity
  have hzpos : 0 < z.re := by linarith
  have hzQ : z.re < Q γ := by linarith
  by_cases ht1 : t ≤ 1
  · have hN := hTaylor γ z t hγ hz ⟨le_of_lt ht, ht1⟩
    have hExp : 1 ≤ Real.exp (1 - t) := by
      simp_all
    have hExpEq : Real.exp (1 - t) = Real.exp 1 * Real.exp (-t) := by
      rw [← Real.exp_add]
      congr 1
    have hsmallBound : 4 * C ≤ (4 * C * Real.exp 1) * Real.exp (-t) := by
      nlinarith
    have hcoeff : 0 ≤ 4 * C * Real.exp 1 := by positivity
    have hsum : (4 * C * Real.exp 1) * Real.exp (-t) ≤
        jointMajorant γ₀ z₀ C t := by
      unfold jointMajorant
      have hExtra : 4 * C * Real.exp 1 ≤
          4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2 :=
        by bound
      have htail : 0 ≤ (jointTailLower γ₀)⁻¹ *
          Real.exp (-jointStripMargin γ₀ z₀ * t) := mul_nonneg (le_of_lt (inv_pos.mpr (jointTailLower_pos hγ₀)))
          (Real.exp_nonneg _)
      calc
        (4 * C * Real.exp 1) * Real.exp (-t) ≤
            (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t) := (mul_le_mul_of_nonneg_right hExtra (Real.exp_nonneg (-t)))
        _ ≤ (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t) +
            (jointTailLower γ₀)⁻¹ * Real.exp _ :=
              le_add_of_nonneg_right htail
    exact (upsilonLogIntegrand_norm_le_jointTaylor hγpos z hC hN ht).trans (hsmallBound.trans hsum)
  · have ht1' := le_of_not_ge ht1
    have hW : ‖(Q γ / 2) - z‖ ≤ jointWBound γ₀ z₀ := by
      have hzNorm : ‖z‖ ≤ ‖z₀‖ + 1 := by
        calc
          ‖z‖ = ‖(z - z₀) + z₀‖ := by simp
          _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le ..
          _ ≤ ‖z₀‖ + 1 := by linarith
      have hQpos : 0 < Q γ := by linarith
      have hQhalf : Q γ / 2 ≤ ((γ₀ + 1) / 2 + 4 / γ₀) / 2 :=
        div_le_div_of_nonneg_right (Q_le_jointUpper hγ₀ hγ) (by norm_num)
      have hQhalf' : Q γ / 2 ≤ (γ₀ + 1) / 4 + 2 / γ₀ := by
        calc
          Q γ / 2 ≤ ((γ₀ + 1) / 2 + 4 / γ₀) / 2 := hQhalf
          _ = (γ₀ + 1) / 4 + 2 / γ₀ := by ring
      have hnormQ : ‖(Q γ / 2 : ℂ)‖ = Q γ / 2 := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
        norm_num
      calc
        ‖(Q γ / 2) - z‖ ≤ ‖(Q γ / 2 : ℂ)‖ + ‖z‖ := norm_sub_le ..
        _ = Q γ / 2 + ‖z‖ := by linarith
        _ ≤ (γ₀ + 1) / 4 + 2 / γ₀ + ‖z₀‖ + 1 := by
          calc
            _ ≤ ((γ₀ + 1) / 4 + 2 / γ₀) + (‖z₀‖ + 1) :=
              add_le_add hQhalf' hzNorm
            _ = (γ₀ + 1) / 4 + 2 / γ₀ + ‖z₀‖ + 1 := by ring
        _ = jointWBound γ₀ z₀ := rfl
    have hw2 : ‖(Q γ / 2) - z‖ ^ 2 ≤ jointWBound γ₀ z₀ ^ 2 := by
      have hWnonneg : 0 ≤ jointWBound γ₀ z₀ := by
        unfold jointWBound
        positivity
      simpa [pow_two] using (mul_le_mul hW hW (norm_nonneg _) hWnonneg)
    have hκpos := jointTailLower_pos hγ₀
    have hinv :=
      (inv_le_inv₀ (tailConst_pos hγpos) hκpos).2 (jointTailLower_le hγ₀ hγ)
    let η := jointStripMargin γ₀ z₀
    have hleftη := hleft
    have hrightη : η < Q γ - z.re := hright
    have habsη : |Q γ / 2 - z.re| < Q γ / 2 - η := by
      rw [abs_lt]
      constructor <;> linarith
    have habs : |Q γ / 2 - z.re| < Q γ / 2 - jointStripMargin γ₀ z₀ := by
      simpa [η] using habsη
    have hδ : jointStripMargin γ₀ z₀ ≤ Q γ / 2 - |Q γ / 2 - z.re| := by
      linarith
    have hExp : Real.exp (-(Q γ / 2 - |Q γ / 2 - z.re|) * t) ≤
        Real.exp (-jointStripMargin γ₀ z₀ * t) := by
      apply Real.exp_le_exp.mpr
      linarith only [mul_le_mul_of_nonneg_right hδ ht.le]
    have hfirst : ‖(Q γ / 2 : ℂ) - z‖ ^ 2 * Real.exp (-t) ≤
        jointWBound γ₀ z₀ ^ 2 * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hw2 (Real.exp_nonneg _)
    have hsecond :=
      mul_le_mul hinv hExp (Real.exp_nonneg _)
        (le_of_lt (inv_pos.mpr hκpos))
    calc
      ‖upsilonLogIntegrand γ z t‖ ≤
          ‖(Q γ / 2 : ℂ) - z‖ ^ 2 * Real.exp (-t) +
            (tailConst γ)⁻¹ *
              Real.exp (-(Q γ / 2 - |Q γ / 2 - z.re|) * t) := (upsilonLogIntegrand_norm_le_tail hγpos z hzpos hzQ ht1')
      _ ≤ jointMajorant γ₀ z₀ C t := by
        unfold jointMajorant
        have hcoeff : jointWBound γ₀ z₀ ^ 2 ≤
            4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2 :=
          le_add_of_nonneg_left (by positivity)
        calc
          _ ≤ jointWBound γ₀ z₀ ^ 2 * Real.exp (-t) +
              (jointTailLower γ₀)⁻¹ * Real.exp _ :=
                add_le_add hfirst hsecond
          _ ≤ (4 * C * Real.exp 1 + jointWBound γ₀ z₀ ^ 2) * Real.exp (-t) +
              (jointTailLower γ₀)⁻¹ * Real.exp _ := add_le_add (mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg (-t))) le_rfl

theorem upsilonLog_continuousAt_joint :
    ContinuousAt (Function.uncurry upsilonLog) (γ₀, z₀) := by
  let gap := Q γ₀ - z₀.re
  have hgap : 0 < gap := by positivity
  have hγ₀ne : γ₀ ≠ 0 := hγ₀.ne'
  have hQcont : ContinuousAt Q γ₀ := by
    fun_prop [Q]
  obtain ⟨δQ, hδQ, hQδ⟩ := Metric.continuousAt_iff.mp hQcont
    (gap / 8) (by positivity)
  let ρz := min (z₀.re / 4) (min (gap / 8) 1)
  have hρz : 0 < ρz := by
    positivity
  let ε := min (δQ / 2) (min (γ₀ / 2) ρz)
  have hε : 0 < ε := by
    positivity
  have hεδQ : ε ≤ δQ / 2 := by grind
  have hεγ : ε ≤ γ₀ / 2 := by
    grind
  have hερ : ε ≤ ρz := by
    grind
  have hρz₀ : ρz ≤ z₀.re / 4 := by grind
  have hρgap : ρz ≤ gap / 8 := by
    grind
  have hρone : ρz ≤ 1 := by
    grind
  obtain ⟨C, hC, hTaylor⟩ :=
    exists_jointNumerator_taylor_bound hγ₀
  let B := jointMajorant γ₀ z₀ C
  have hBint : Integrable B (volume.restrict (Set.Ioi 0)) := by
    exact jointMajorant_integrable hγ₀ hz₀ hzQ₀ hC
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
    have hγdist : dist p.1 γ₀ < ε := by simp_all
    have hγabs : |p.1 - γ₀| < ε := by
      simpa [Real.dist_eq] using hγdist
    have hγmem : p.1 ∈ Set.Icc (γ₀ / 2) (γ₀ + 1) := by
      constructor <;> grind
    have hγQdist : dist p.1 γ₀ < δQ := by
      have hhalf : δQ / 2 < δQ := by linarith
      exact lt_of_lt_of_le hγdist (le_trans hεδQ hhalf.le)
    have hQclose : |Q p.1 - Q γ₀| < gap / 8 := by
      simpa [Real.dist_eq] using hQδ hγQdist
    have hzdist : dist p.2 z₀ < ε := by simp_all
    have hznorm : ‖p.2 - z₀‖ < ρz := by
      have hznorm' : ‖p.2 - z₀‖ < ε := by
        simpa [dist_eq_norm] using hzdist
      exact lt_of_lt_of_le hznorm' hερ
    have hzball : ‖p.2 - z₀‖ ≤ 1 := hznorm.le.trans hρone
    have hzreclose : |p.2.re - z₀.re| < ρz := by
      simpa using lt_of_le_of_lt (Complex.abs_re_le_norm (p.2 - z₀)) hznorm
    have hleft : jointStripMargin γ₀ z₀ < p.2.re := by
      have h := (abs_lt.mp hzreclose).1
      have hη : jointStripMargin γ₀ z₀ ≤ z₀.re / 4 := by
        exact min_le_left ..
      have hr := hρz₀
      linarith
    have hright : jointStripMargin γ₀ z₀ < Q p.1 - p.2.re := by
      have hqLower : Q γ₀ - gap / 8 < Q p.1 := by
        have h := (abs_lt.mp hQclose).1
        linarith
      have hzUpper : p.2.re < z₀.re + ρz := by
        have h := (abs_lt.mp hzreclose).2
        linarith
      have hη : jointStripMargin γ₀ z₀ ≤ gap / 4 := by
        exact min_le_right ..
      linarith
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact jointIntegrand_norm_le_majorant hγ₀ hz₀ hzQ₀ hC hTaylor hγmem hzball
      hleft hright ht
  have hCont : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
      ContinuousAt (fun p => F p t) (γ₀, z₀) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := ht
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htpos.ne'
    have hsin₁ : Real.sinh (t * γ₀ / 4) ≠ 0 :=
      by positivity
    have hsin₂ : Real.sinh (t / γ₀) ≠ 0 :=
      by positivity
    let w : ℝ × ℂ → ℂ := fun p => Q p.1 / 2 - p.2
    let D : ℝ × ℂ → ℂ := fun p =>
      (Real.sinh (t * p.1 / 4) : ℂ) * (Real.sinh (t / p.1) : ℂ)
    have hw : ContinuousAt w (γ₀, z₀) := by
      fun_prop
    have hD : ContinuousAt D (γ₀, z₀) := by
      fun_prop
    have hDne : D (γ₀, z₀) ≠ 0 := by
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hsin₁)
        (Complex.ofReal_ne_zero.mpr hsin₂)
    have hA : ContinuousAt (fun p => w p ^ 2 * Real.exp (-t))
        (γ₀, z₀) := by
      fun_prop
    have hS : ContinuousAt (fun p =>
        Complex.sinh (w p * (t / 2)) ^ 2) (γ₀, z₀) := by
      fun_prop
    have hNum : ContinuousAt (fun p =>
        w p ^ 2 * Real.exp (-t) - Complex.sinh (w p * (t / 2)) ^ 2 / D p)
        (γ₀, z₀) := by fun_prop
    have hres : ContinuousAt (fun p =>
        (w p ^ 2 * Real.exp (-t) - Complex.sinh _ ^ 2 / D p) /
          (t : ℂ)) _ := hNum.div continuousAt_const htC
    simpa [F, upsilonLogIntegrand, w, D] using hres
  exact continuousAt_of_dominated hMeas hBound hBint hCont

end

end


end DOZZ.Proofs

end
