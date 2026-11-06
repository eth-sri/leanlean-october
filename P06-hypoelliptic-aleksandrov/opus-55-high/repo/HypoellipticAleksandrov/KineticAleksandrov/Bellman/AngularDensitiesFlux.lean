module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativeFunctionals
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativePrimitiveWeak
import Mathlib.Tactic

/-! # Constructing the actual angular flux from the angular weak equation -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The angular equation gives a literal locally integrable flux with a weighted-measure
derivative. -/
theorem bellmanAngularFlux_weak (R β : ℝ) (F H : Measure ℝ)
    (hang : IsBellmanAngularAdjointPair 1 R β F H) :
    ∃ j : ℝ, ∀ φ : BellmanRealTest,
      (∫ x, deriv φ x ∂H) =
        (1 / 3 : ℝ) * (∫ x, x ^ 2 * φ x ∂F) -
          (∫ x, φ x * (j - ((β - 2) / 3) * bellmanMeasurePrimitive F id 0 x)) := by
  let  := hang.1
  let  := hang.2.2.1
  let A := bellmanMeasurePrimitive F id 0
  have hA : LocallyIntegrable A volume :=
    bellmanMeasurePrimitive_locallyIntegrable F id continuous_id
  have h1H : LocallyIntegrable (fun _ : ℝ => (1 : ℝ)) H :=
    continuous_const.locallyIntegrable
  have h2F : LocallyIntegrable (fun x : ℝ => x ^ 2) F :=
    (continuous_id.pow 2).locallyIntegrable
  let L  :=
    (bellmanWeightedTestIntegral H (fun _ => 1)).comp bellmanTestDerivativeLinearMap -
      (1 / 3 : ℝ) • bellmanWeightedTestIntegral F (fun x => x ^ 2) -
      ((β - 2) / 3) • bellmanWeightedTestIntegral volume A
  have hL (φ : BellmanRealTest) : L φ = (∫ x, deriv φ x ∂H) -
      (1 / 3) * (∫ x, φ x * x ^ 2 ∂F) -
      ((β - 2) / 3) * (∫ x, φ x * A x) := by
    change bellmanWeightedTestIntegral H _ (bellmanTestDerivative φ) -
      (1 / 3) * bellmanWeightedTestIntegral F _ φ -
      ((β - 2) / 3) * bellmanWeightedTestIntegral volume A φ = _
    rw [bellmanWeightedTestIntegral_apply H _ h1H,
      bellmanWeightedTestIntegral_apply F _ h2F,
      bellmanWeightedTestIntegral_apply volume A hA]
    aesop
  have hzero : ∀ φ : BellmanRealTest, L (bellmanTestDerivative φ) = 0 := by
    intro φ
    rw [hL]
    change (∫ x, deriv (deriv φ) x ∂H) -
      (1 / 3) * (∫ x, deriv φ x * x ^ 2 ∂F) -
      ((β - 2) / 3) * (∫ x, deriv φ x * A x) = 0
    have he := hang.2.2.2.2.2.2 φ φ.contDiff φ.hasCompactSupport
    have hw := bellmanMeasurePrimitive_weak F id continuous_id φ
      φ.contDiff φ.hasCompactSupport
    grind
  obtain ⟨k, hk⟩ := bellman_test_derivative_kernel L hzero
  refine ⟨-k, ?_⟩
  intro φ
  have he := hk φ
  rw [hL] at he
  have hiA : Integrable (fun x => φ x * A x) volume := by
    simpa using
      hA.integrable_smul_left_of_hasCompactSupport φ.contDiff.continuous φ.hasCompactSupport
  have hiφ : Integrable (fun x => φ x) volume :=
    φ.contDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hJI : (∫ x, φ x * (-k - ((β - 2) / 3) * A x)) =
      -k * (∫ x, φ x) - ((β - 2) / 3) * (∫ x, φ x * A x) := by
    rw [show (fun x => φ x * (-k - ((β - 2) / 3) * A x)) =
        (fun x => -k * φ x - ((β - 2) / 3) * (φ x * A x)) by grind,
      integral_sub (hiφ.const_mul (-k)) (hiA.const_mul _),
      integral_const_mul, integral_const_mul]
  grind

end HypoellipticAleksandrov.KineticAleksandrov
