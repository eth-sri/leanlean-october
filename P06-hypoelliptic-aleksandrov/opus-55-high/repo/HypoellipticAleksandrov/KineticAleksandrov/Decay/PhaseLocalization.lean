module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SmoothTestOrder
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.PhaseExclusion
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Closed phase strips from vanishing forbidden-region tests

The two strictly forbidden open sets have zero mass. Their complement is the
source's closed phase strip, interpreted as an almost-everywhere measure statement.
-/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Two signs of vanishing smooth tests place a finite measure in the closed phase strip. -/
theorem ae_phase_strip_of_forbidden_tests {d : ℕ}
    {μ : Measure (EvolutionAmbientState d)} [IsFiniteMeasure μ]
    {D : Set (EvolutionAmbientState d)} (hD : IsOpen D) (hμ : μ Dᶜ = 0)
    {q : EvolutionAmbientState d → ℝ} (hq : Continuous q) (c : ℝ)
    (htest : ∀ sgn : ℝ, sgn = 1 ∨ sgn = -1 →
      ∀ φ : EvolutionAmbientState d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ {x | 0 < sgn * q x - c} ∩ D →
        (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ = 0) :
    ∀ᵐ x ∂μ, |q x| ≤ c := by
  have hzero : ∀ sgn : ℝ, sgn = 1 ∨ sgn = -1 → μ {x | 0 < sgn * q x - c} = 0 := by
    intro sgn hs
    apply measure_eq_zero_of_smooth_integral_eq_zero_of_support
      (isOpen_lt continuous_const ((continuous_const.mul hq).sub continuous_const)) hD hμ
    aesop
  apply ae_iff.mpr
  apply measure_mono_null (fun x hx => ?_)
    (measure_union_null (hzero 1 (Or.inl rfl)) (hzero _ (Or.inr rfl)))
  change ¬ |q x| ≤ c at hx
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Decay
