/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.BarrierCauchyMass
public import DOZZ.GMC.Construction.BarrierCauchyKernel
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.Complex.Tietze

/-! Tonelli identities connecting growing-barrier test masses to their spatial pair kernel. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]


/-- A selected admissible Wick weight has extended expectation one at every allowed cutoff. -/
theorem compatibleAdmissibleSelectedWickWeight_lintegral_eq_one

    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (b : Bool) (ε : ℝ) (hε : 0 < ε)
    (hεcut : ε ≤ min ε₀ ε₁) (x : ℂ) (γ : ℝ) :
    ∫⁻ ω, admissibleLogWickWeight P (if b then Y else Z) γ ε x ω ∂P = 1 := by
  let q : Fin 1 → ℝ × ℂ := fun _ => (ε, x)
  let V : Ω → Fin 1 → ℝ := fun ω _ => (if b then Y else Z) ω ε x
  have hq : ∀ i, 0 < (q i).1 ∧ (q i).1 ≤ min ε₀ ε₁ := by
    intro i
    simp only [q]
    exact ⟨hε, hεcut⟩
  have hqY : ∀ i, 0 < (q i).1 ∧ (q i).1 ≤ ε₀ := by
    intro i
    exact ⟨(hq i).1, le_trans (hq i).2 (min_le_left _ _)⟩
  have hqZ : ∀ i, 0 < (q i).1 ∧ (q i).1 ≤ ε₁ := by
    intro i
    exact ⟨(hq i).1, le_trans (hq i).2 (min_le_right _ _)⟩
  have hV : IsCenteredJointlyGaussian P V := by
    cases b with
    | false => simpa [V] using hZ.gaussian 1 q hqZ
    | true => simpa [V] using hY.gaussian 1 q hqY
  exact wick_exponential_lintegral_expectation P V hV 0 γ


/-- The mixed growing-barrier pair kernel is measurable in its two spatial roots. -/
theorem compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel_measurable

    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (γ a : ℝ) (k₀ : ℕ) (r s : ℝ) (b₁ b₂ : Bool) :
    Measurable (fun p : ℂ × ℂ =>
      compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel
        P Y Z γ a k₀ r s p.1 p.2 b₁ b₂) := by
  have compatibleAdmissibleSelectedWickWeight_measurable (b : Bool) (γ ε : ℝ) : Measurable (fun q : Ω × ℂ =>
        admissibleLogWickWeight P (if b then Y else Z) γ ε q.2 q.1) := by
    cases b with
    | false =>
        change Measurable (fun q : Ω × ℂ => ENNReal.ofReal (Real.exp
          (γ * Z q.1 ε q.2 - γ ^ 2 / 2 *
            gaussianVariance P (fun ω => Z ω ε q.2))))
        have hv0 := admissibleLogRegularization_variance_measurable
          P U dens ε₁ Z hZ ε
        have hvar : Measurable (fun q : Ω × ℂ => gaussianVariance P
            (fun ω => Z ω ε q.2)) := hv0.comp measurable_snd
        have hfield :=
          hZ.measurableAtScale ε
        fun_prop
    | true =>
        change Measurable (fun q : Ω × ℂ => ENNReal.ofReal (Real.exp
          (γ * Y q.1 ε q.2 - γ ^ 2 / 2 *
            gaussianVariance P (fun ω => Y ω ε q.2))))
        have hv0 := admissibleLogRegularization_variance_measurable
          P U dens ε₀ Y hY ε
        have : Measurable (fun q : Ω × ℂ => gaussianVariance P
            (fun ω => Y ω ε q.2)) := hv0.comp measurable_snd
        have :=
          hY.measurableAtScale ε
        fun_prop
  classical
  let F : Ω × (ℂ × ℂ) → ℝ≥0∞ := fun q =>
    admissibleLogWickWeight P (if b₁ then Y else Z) γ (Real.exp (-r)) q.2.1 q.1 *
      admissibleLogWickWeight P (if b₂ then Y else Z) γ (Real.exp (-s)) q.2.2 q.1 *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
        (fun _ => (1 : ℝ≥0∞)) (q.1, q.2.1) *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ s)
        (fun _ => (1 : ℝ≥0∞)) (q.1, q.2.2)
  have : Measurable (fun q : Ω × (ℂ × ℂ) =>
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
        (fun _ => (1 : ℝ≥0∞)) (q.1, q.2.1)) := measurable_const.indicator
      (admissibleGrowingBarrierSet_measurable P U dens ε₀ Y hY a k₀ r |>.preimage
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
  have : Measurable (fun q : Ω × (ℂ × ℂ) =>
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ s)
        (fun _ => (1 : ℝ≥0∞)) (q.1, q.2.2)) := measurable_const.indicator
      (admissibleGrowingBarrierSet_measurable P U dens ε₀ Y hY a k₀ s |>.preimage
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have : Measurable (fun q : Ω × (ℂ × ℂ) =>
      admissibleLogWickWeight P (if b₁ then Y else Z) γ
        (Real.exp (-r)) q.2.1 q.1) := by
    have h := compatibleAdmissibleSelectedWickWeight_measurable b₁ γ (Real.exp (-r))
    exact h.comp (f := fun q : Ω × (ℂ × ℂ) => (q.1, q.2.1))
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have : Measurable (fun q : Ω × (ℂ × ℂ) =>
      admissibleLogWickWeight P (if b₂ then Y else Z) γ
        (Real.exp (-s)) q.2.2 q.1) := by
    have h := compatibleAdmissibleSelectedWickWeight_measurable b₂ γ (Real.exp (-s))
    exact h.comp (f := fun q : Ω × (ℂ × ℂ) => (q.1, q.2.2))
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have : Measurable F := by fun_prop
  have hEq : (fun p : ℂ × ℂ =>
      compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel
        P Y Z γ a k₀ r s p.1 p.2 b₁ b₂) =
      fun p => ∫⁻ ω, F (ω, p) ∂P := by rfl
  rw [hEq]
  fun_prop

end DOZZ.Proofs
