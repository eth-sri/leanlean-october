module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.Cancellation
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-! # Interior unit-block cancellation at phase error one quarter -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic

/-- Pi-separated phase factors are exact opposites. -/
theorem phaseFactor_add_eq_zero_of_sub_eq_pi {Φ1 Φ2 : ℝ}
    (hΦ : Φ2 - Φ1 = Real.pi) : phaseFactor Φ1 + phaseFactor Φ2 = 0 := by
  have he : Φ2 = Φ1 + Real.pi := by linarith
  rw [he]
  unfold phaseFactor
  have hc : -Complex.I * ((Φ1 + Real.pi : ℝ)) =
      -Complex.I * Φ1 - Real.pi * Complex.I := by
    push_cast
    ring
  simp_all

/-- The source interior cancellation estimate, with the retained mass floor discharged. -/
theorem block_interior_cancellation {d : ℕ}
    (ξ z0 : PDE.Vec d) (M F1 F2 : Measure (EvolutionAmbientState d))
    [IsFiniteMeasure M] [IsFiniteMeasure F1] [IsFiniteMeasure F2]
    (Θ : Measure (PDE.Vec d)) (m0 h q0 Φ1 Φ2 : ℝ)
    (hM : M.real univ ≤ 1) (hF : F1 + F2 ≤ M)
    (hΘ1 : F1.map Prod.fst = Θ) (hΘ2 : F2.map Prod.fst = Θ)
    (hmass : m0 * h * q0 / 2 ≤ Θ.real univ)
    (hΦ : Φ2 - Φ1 = Real.pi)
    (hs1 : ∀ᵐ x ∂F1, |phaseCoordinate ξ z0 x - Φ1| ≤ 1 / 4)
    (hs2 : ∀ᵐ x ∂F2, |phaseCoordinate ξ z0 x - Φ2| ≤ 1 / 4)
    (ν : ComplexMeasure (PDE.Vec d))
    (hν : IsPhaseProjection (phaseCoordinate ξ z0) M ν) :
    TV ν ≤ 1 - (3 / 2) * Θ.real univ ∧ TV ν ≤ 1 - (3 / 4) * m0 * h * q0 := by
  have hψ : Measurable (phaseCoordinate ξ z0) := by
    unfold phaseCoordinate PDE.vecDot
    fun_prop
  have he := totalVariation_toReal_le_of_cancellation hψ hF hΘ1 hΘ2
    (by norm_num) (by norm_num)
    (phaseFactor_add_eq_zero_of_sub_eq_pi hΦ) hs1 hs2 hν
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Decay
