/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.InverseRecursion
public import DOZZ.GMC.SharpMoments.LaplaceApriori
public import DOZZ.GMC.SharpMoments.LaplaceBase
public import DOZZ.GMC.SharpMoments.QuadraticRecursion
public import DOZZ.GMC.SharpMoments.StretchedTailMoment

/-! # Inverse moments of the reference mass, uniformly in the cutoff

Given the two-branch inequality at every fine cutoff, the supremum over all cutoffs of the
reference Laplace transforms satisfies the quadratic recursion of `InverseRecursion` at fine
cutoffs and the Gaussian base bound at coarse cutoffs. Paley–Zygmund keeps it below one, so it
tends to zero and then decays stretched-exponentially. Small-value probabilities inherit this
decay, and every inverse moment of the cutoff reference mass is bounded uniformly in the cutoff. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The supremum over cutoffs of the reference Laplace transforms. -/
noncomputable def cutoffLaplaceSup {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (γ : ℝ) (A : Set ℂ) (x : ℝ) : ℝ :=
  ⨆ r : Set.Ici (0 : ℝ), cutoffLaplace P Xc γ r A x
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
section
variable (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (γ : ℝ) (A : Set ℂ)
include hX

theorem cutoffLaplaceSup_bddAbove
    (x : ℝ) :
    BddAbove (Set.range fun r : Set.Ici (0 : ℝ) => cutoffLaplace P Xc γ r A x) :=
  ⟨1, by rintro _ ⟨r, rfl⟩; exact cutoffLaplace_le_one P X hX Xc γ r A x⟩

theorem le_cutoffLaplaceSup
    (r : ℝ) (hr : 0 ≤ r) (x : ℝ) :
    cutoffLaplace P Xc γ r A x ≤ cutoffLaplaceSup P Xc γ A x :=
  le_ciSup (cutoffLaplaceSup_bddAbove P X hX Xc γ A x) ⟨r, hr⟩

theorem cutoffLaplaceSup_nonneg
    (x : ℝ) :
    0 ≤ cutoffLaplaceSup P Xc γ A x :=
  (cutoffLaplace_nonneg P Xc γ 0 A x).trans
    (le_cutoffLaplaceSup P X hX Xc γ A 0 le_rfl x)

end

theorem cutoffLaplaceSup_le_of_forall
    (Xc : Ω → ℂ → ℝ → ℝ) (γ : ℝ) (A : Set ℂ) (x b : ℝ)
    (h : ∀ r : ℝ, 0 ≤ r → cutoffLaplace P Xc γ r A x ≤ b) :
    cutoffLaplaceSup P Xc γ A x ≤ b :=
  ciSup_le fun r => h r r.2

theorem cutoffLaplaceSup_antitone
    (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (A : Set ℂ) (hA : MeasurableSet A) :
    Antitone (cutoffLaplaceSup P Xc γ A) := by
  intro x y hxy
  refine cutoffLaplaceSup_le_of_forall P Xc γ A y _ (fun r hr => ?_)
  exact (cutoffLaplace_antitone P X hX Xc hXc γ r A hA hxy).trans
    (le_cutoffLaplaceSup P X hX Xc γ A r hr x)

end

/-- Arithmetic for the a-priori level: with `0 < π`, the level `1 - π/2` times the recursion
factor `1 + π/4` stays below one. -/
theorem inverseUniform_level_mul_lt_one (π : ℝ) (hπ : 0 < π) :
    (1 - π / 2) * (1 + π / 4) < 1 := by
  nlinarith
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
section
variable (hX : IsEquatorGFF P X)
include hX

/-- The supremum Laplace transform satisfies the quadratic recursion with a Gaussian error. -/
theorem cutoffLaplaceSup_recursion
    (γ : ℝ) (hγ : 0 < γ)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (C : ℝ≥0) (hC : 0 < C)
    (h2B : ∀ r : ℝ, Real.log 4 + 1 ≤ r → ∀ x : ℝ,
      cutoffLaplace P Xc γ r (Metric.ball 0 (1 / 8)) x ≤
        ∫ ξ, cutoffLaplace P Xc γ r (Metric.ball invSubCenterLeft (1 / 4 * (1 / 8)))
            (x + γ * ξ - γ ^ 2 * C / 2) *
          cutoffLaplace P Xc γ r (Metric.ball invSubCenterRight (1 / 4 * (1 / 8)))
            (x + γ * ξ - γ ^ 2 * C / 2) ∂gaussianReal 0 C)
    (ε : ℝ) (hε : 0 < ε) (A₂ c₂ : ℝ) (hc₂ : 0 < c₂)
    (hbase : ∀ r : ℝ, 0 ≤ r → r ≤ Real.log 4 + 1 → ∀ x : ℝ, 0 ≤ x →
      cutoffLaplace P Xc γ r (Metric.ball 0 (1 / 8)) x ≤ A₂ * Real.exp (-c₂ * x ^ 2)) :
    ∃ A c : ℝ, 0 ≤ A ∧ 0 < c ∧ ∀ x : ℝ, 0 ≤ x →
      cutoffLaplaceSup P Xc γ (Metric.ball 0 (1 / 8)) x ≤
        A * Real.exp (-c * x ^ 2) + (1 + ε) * cutoffLaplaceSup P Xc γ (Metric.ball 0 (1 / 8))
          (3 / 4 * x - -(2 * Real.log (1 / 4) + γ ^ 2 / 2 * Real.log (1 / 4) -
            γ ^ 2 * C / 2)) ^ 2 := by
  set D := Metric.ball (0 : ℂ) _ with hD
  set a : ℝ := 2 * Real.log _ + γ ^ 2 / 2 * Real.log _ - γ ^ 2 * C / 2 with ha
  have hlog4 : 0 < Real.log 4 := by positivity
  have hγ2 : 0 < γ ^ 2 := by positivity
  have hCr : (0 : ℝ) < C := hC
  set k₁ : ℝ := 1 / (128 * γ ^ 2 * C) with hk₁
  set k₂ : ℝ := 1 / (64 * γ ^ 2 * Real.log 4) with hk₂
  have hk₁pos : 0 < k₁ := by positivity
  have hk₂pos : 0 < k₂ := by positivity
  set c := min c₂ (min k₁ k₂) with hc
  have hcpos : 0 < c := by positivity
  set A : ℝ := 1 + (1 + 1 / ε) + |A₂| with hA
  have hεinv : 0 ≤ 1 / ε := by positivity
  have hApos : 0 ≤ A := by positivity
  refine ⟨A, c, hApos, hcpos, fun x hx => ?_⟩
  have hdecay : ∀ k : ℝ, c ≤ k → Real.exp (-k * x ^ 2) ≤ Real.exp (-c * x ^ 2) := by
    intro k hk
    apply Real.exp_le_exp.mpr
    have := sq_nonneg x
    nlinarith
  have hGsq : ∀ r : ℝ, 1 ≤ r →
      cutoffLaplace P Xc γ r D (3 / 4 * x + a) ^ 2 ≤
        cutoffLaplaceSup P Xc γ D (3 / 4 * x - -a) ^ 2 := by
    intro r hr
    rw [show 3 / 4 * x - -a = 3 / 4 * x + a by ring]
    exact pow_le_pow_left₀ (cutoffLaplace_nonneg P Xc γ r D _)
      (le_cutoffLaplaceSup P X hX Xc γ D r (by linarith) _) 2
  have hGnn : 0 ≤ cutoffLaplaceSup P Xc γ D (3 / 4 * x - -a) ^ 2 := sq_nonneg _
  refine cutoffLaplaceSup_le_of_forall P Xc γ D x _ (fun r hr => ?_)
  by_cases hrbig : Real.log 4 + 1 ≤ r
  · have hstep := cutoffLaplace_recursion_step P X hX γ hγ Xc hXc C hC r hrbig (h2B r hrbig)
      ε hε x hx
    have hr1 : 1 ≤ r - Real.log 4 := by linarith
    have h1 : Real.exp (-x ^ 2 / (128 * γ ^ 2 * C)) ≤ Real.exp (-c * x ^ 2) := by
      rw [show -x ^ 2 / (128 * γ ^ 2 * C) = -k₁ * x ^ 2 by ring]
      exact hdecay k₁ ((min_le_right ..).trans (min_le_left ..))
    have h2 : Real.exp (-x ^ 2 / (64 * γ ^ 2 * Real.log 4)) ≤ Real.exp (-c * x ^ 2) := by
      rw [show -x ^ 2 / (64 * γ ^ 2 * Real.log 4) = -k₂ * x ^ 2 by ring]
      exact hdecay k₂ ((min_le_right ..).trans (min_le_right ..))
    have h3 := hGsq _ hr1
    have hexp : 0 ≤ Real.exp (-c * x ^ 2) := by positivity
    have hA₂ : 0 ≤ |A₂| * Real.exp (-c * x ^ 2) := by positivity
    calc cutoffLaplace P Xc γ r D x
        ≤ Real.exp _ +
            (1 + 1 / ε) * Real.exp _ +
            (1 + ε) * cutoffLaplace P Xc γ _ D _ ^ 2 := hstep
      _ ≤ Real.exp _ + (1 + 1 / ε) * Real.exp _ +
            (1 + ε) * cutoffLaplaceSup P Xc γ D _ ^ 2 := by
          gcongr
      _ ≤ A * Real.exp _ + (1 + ε) * cutoffLaplaceSup P Xc γ D _ ^ 2 := by
          nlinarith
  · have hb := hbase r hr (le_of_lt (lt_of_not_ge hrbig)) x hx
    have hexp : 0 ≤ Real.exp (-c * x ^ 2) := (Real.exp_pos _).le
    have hA₂ : A₂ * Real.exp (-c₂ * x ^ 2) ≤ |A₂| * Real.exp (-c * x ^ 2) := by
      calc A₂ * Real.exp _ ≤ |A₂| * Real.exp _ :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
        _ ≤ |A₂| * Real.exp _ :=
            mul_le_mul_of_nonneg_left (hdecay c₂ (min_le_left ..)) (abs_nonneg _)
    have hAle : |A₂| * Real.exp (-c * x ^ 2) ≤ A * Real.exp (-c * x ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ hexp
      linarith
    have hε1 : 0 ≤ (1 + ε) * cutoffLaplaceSup P Xc γ D (3 / 4 * x - -a) ^ 2 :=
      mul_nonneg (by linarith) hGnn
    linarith

/-- Given the two-branch inequality at every fine cutoff, every inverse moment of the cutoff mass
of the reference disk is bounded uniformly in the cutoff. -/
theorem regularizedGMC_reference_inverse_moment_uniform_of_twoBranch
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (C : ℝ≥0) (hC : 0 < C)
    (h2B : ∀ r : ℝ, Real.log 4 + 1 ≤ r → ∀ x : ℝ,
      cutoffLaplace P Xc γ r (Metric.ball 0 (1 / 8)) x ≤
        ∫ ξ, cutoffLaplace P Xc γ r (Metric.ball invSubCenterLeft (1 / 4 * (1 / 8)))
            (x + γ * ξ - γ ^ 2 * C / 2) *
          cutoffLaplace P Xc γ r (Metric.ball invSubCenterRight (1 / 4 * (1 / 8)))
            (x + γ * ξ - γ ^ 2 * C / 2) ∂gaussianReal 0 C)
    (q : ℝ) (hq : 0 < q) :
    ∃ K : ℝ, ∀ r : ℝ, 0 ≤ r →
      ∫⁻ ω, (regularizedGMC P Xc γ r ω (Metric.ball 0 (1 / 8))) ^ (-q) ∂P ≤ ENNReal.ofReal K := by
  let _ := hX.1
  set D := Metric.ball (0 : ℂ) _ with hD
  have hDmeas : MeasurableSet D := Metric.isOpen_ball.measurableSet
  -- a-priori bound below one
  obtain ⟨π₀, hπ₀, hPZ⟩ := cutoffLaplace_apriori P X hX Xc hXc γ hγ hγ2 (1 / 8) (by norm_num)
    (by norm_num)
  set π := min π₀ 1 with hπdef
  have hπ : 0 < π := lt_min hπ₀ one_pos
  have hπ1 : π ≤ 1 := min_le_right ..
  set h₀ := (1 / 2) * (gmcReferenceMeasure D).toReal with hh₀
  have hD0 : gmcReferenceMeasure D ≠ 0 :=
    (DOZZ.Proofs.laplaceBase_ball_pos (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num)).ne'
  have hDtop : gmcReferenceMeasure D ≠ ⊤ :=
    ne_top_of_le_ne_top gmcReferenceMeasure_univ_ne_top (measure_mono (Set.subset_univ _))
  have hh₀pos : 0 < h₀ := by
    exact mul_pos (by norm_num) (ENNReal.toReal_pos hD0 hDtop)
  -- base bound at coarse cutoffs
  obtain ⟨A₂, c₂, hc₂, hbase⟩ := cutoffLaplace_le_gaussian_bounded_cutoff P X hX Xc hXc γ hγ
    (1 / 8) (Real.log 4 + 1) (by norm_num) (by norm_num) (by positivity)
  -- recursion for the supremum
  set ε := π / 4 with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨A, c, hA, hc, hrec⟩ := cutoffLaplaceSup_recursion P X hX γ hγ Xc hXc C hC h2B ε hεpos
    A₂ c₂ hc₂ hbase
  set G := cutoffLaplaceSup P Xc γ D with hG
  set c₀ := -(2 * Real.log _ + γ ^ 2 / 2 * Real.log _ - γ ^ 2 * C / 2) with hc₀
  have hGanti : Antitone G := cutoffLaplaceSup_antitone P X hX Xc hXc γ D hDmeas
  have hG0 : ∀ x, 0 ≤ G x := fun x => cutoffLaplaceSup_nonneg P X hX Xc γ D x
  have hrec' : ∀ x, 0 ≤ x → G x ≤ A * Real.exp (-c * x ^ 2) + (1 + ε) * G (3 / 4 * x - c₀) ^ 2 :=
    hrec
  -- G tends to zero
  have hdecay : Tendsto (fun x => A * Real.exp (-c * x ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x => -c * x ^ 2) atTop atBot := by
      exact (tendsto_neg_atTop_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop hc)).congr (fun x => by simp)
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul A
  have hsmall : ∀ᶠ x in atTop, G x ≤ 1 - π / 2 := by
    have hlim : Tendsto (fun x => Real.exp (-(Real.exp x) * h₀)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x => -(Real.exp x) * h₀) atTop atBot := by
        exact (tendsto_neg_atTop_atBot.comp (Real.tendsto_exp_atTop.atTop_mul_const hh₀pos)).congr (fun x => by simp)
      exact Real.tendsto_exp_atBot.comp h1
    filter_upwards [hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < π / 2))] with x hx
    refine cutoffLaplaceSup_le_of_forall P Xc γ D x _ (fun r hr => ?_)
    have := hPZ r hr x
    have hπle : π ≤ π₀ := min_le_left ..
    linarith
  have hGlim : Tendsto G atTop (𝓝 0) :=
    quadRec_tendsto_zero G (fun x => A * Real.exp _) hGanti hG0 _ c₀ _
      0 _ (by norm_num) (by linarith)
      (by rw [hε]; exact inverseUniform_level_mul_lt_one π hπ) hdecay hrec' hsmall
  -- stretched-exponential decay
  obtain ⟨C', d, β, hd, hβ, hstretch⟩ := quadRec_stretched_exp G hGanti hG0 hGlim (3 / 4) c₀ A
    (1 + ε) c 0 (by norm_num) (by norm_num) hA (by linarith) hc hrec'
  -- tail of the cutoff mass
  obtain ⟨K, hK⟩ := lintegral_rpow_neg_le_of_stretched_tail (Real.exp 1 * C') d β q hd hβ hq
  refine ⟨K, fun r hr => ?_⟩
  have hmeas : Measurable (fun ω => regularizedGMC P Xc γ r ω D) :=
    (Measure.measurable_coe hDmeas).comp (regularizedGMC_measurable P X hX Xc hXc γ r)
  apply hK P (fun ω => regularizedGMC P Xc γ r ω D) hmeas.aemeasurable
  intro x hx
  have hsub : {ω | regularizedGMC P Xc γ r ω D ≤ ENNReal.ofReal (Real.exp (-x))} ⊆
      {ω | (regularizedGMC P Xc γ r ω D).toReal ≤ Real.exp (-x)} := by
    intro ω hω
    exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hω
  calc P {ω | regularizedGMC P Xc γ r ω D ≤ ENNReal.ofReal _}
      ≤ P {ω | (regularizedGMC P Xc γ r ω D).toReal ≤ Real.exp (-x)} := measure_mono hsub
    _ ≤ ENNReal.ofReal _ :=
        measure_toReal_le_le_exp_mul_laplace P _
          (measurable_regularizedGMC_apply_toReal P X hX Xc hXc γ r D hDmeas)
          (fun _ => ENNReal.toReal_nonneg) x
    _ ≤ ENNReal.ofReal (Real.exp 1 * C' * Real.exp (-d * x ^ β)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
        exact (le_cutoffLaplaceSup P X hX Xc γ D r hr x).trans (hstretch x hx)

end

end

end DOZZ.Proofs
