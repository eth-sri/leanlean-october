module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativeFunctionals
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativePrimitiveWeak
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensitiesMoments

@[expose] public noncomputable section

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
  let : IsFiniteMeasureOnCompacts F := hang.1
  let : IsFiniteMeasureOnCompacts H := hang.2.2.1
  let A := bellmanMeasurePrimitive F id 0
  have hA :=
    bellmanMeasurePrimitive_locallyIntegrable F id continuous_id
  have h1H : LocallyIntegrable (fun _ => (1 : ℝ)) H :=
    continuous_const.locallyIntegrable
  have h2F : LocallyIntegrable (fun x => x ^ 2) F :=
    (continuous_id.pow 2).locallyIntegrable
  let L :=
    (bellmanWeightedTestIntegral H (fun _ => 1)).comp bellmanTestDerivativeLinearMap -
      (1 / 3 : ℝ) • bellmanWeightedTestIntegral F (fun x => x ^ 2) -
      ((β - 2) / 3) • bellmanWeightedTestIntegral volume A
  have hL (φ : BellmanRealTest) : L φ = (∫ x, deriv φ x ∂H) -
      (1 / 3 : ℝ) * (∫ x, φ x * x ^ 2 ∂F) -
      ((β - 2) / 3) * (∫ x, φ x * A x) := by
    change bellmanWeightedTestIntegral H (fun _ => 1) (bellmanTestDerivative φ) -
      (1 / 3 : ℝ) * bellmanWeightedTestIntegral F (fun x => x ^ 2) φ -
      ((β - 2) / 3) * bellmanWeightedTestIntegral volume A φ = _
    rw [bellmanWeightedTestIntegral_apply H _ h1H,
      bellmanWeightedTestIntegral_apply F _ h2F,
      bellmanWeightedTestIntegral_apply volume A hA]
    simp
    rfl
  have hzero : ∀ φ : BellmanRealTest, L (bellmanTestDerivative φ) = 0 := by
    intro φ
    rw [hL]
    change (∫ x, deriv (deriv φ) x ∂H) -
      (1 / 3 : ℝ) * (∫ x, deriv φ x * x ^ 2 ∂F) -
      ((β - 2) / 3) * (∫ x, deriv φ x * A x) = 0
    have he := hang.2.2.2.2.2.2 φ φ.contDiff φ.hasCompactSupport
    have hswap : (∫ x, deriv φ x * A x) = -∫ x, x * φ x ∂F := by
      rw [show (fun x => deriv φ x * A x) = (fun x => A x * deriv φ x) by
        funext x; ring]
      exact bellmanMeasurePrimitive_weak F id continuous_id φ φ.contDiff φ.hasCompactSupport
    have hswap2 : (∫ x, deriv φ x * x ^ 2 ∂F) = ∫ x, x ^ 2 * deriv φ x ∂F := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => mul_comm _ _
    rw [hswap, hswap2]
    linear_combination he
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
        (fun x => -k * φ x - ((β - 2) / 3) * (φ x * A x)) by funext x; ring,
      integral_sub (hiφ.const_mul (-k)) (hiA.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [hJI, show (fun x => x ^ 2 * φ x) = (fun x => φ x * x ^ 2) by funext x; ring]
  linarith


/-- The angular weak equation and ellipticity produce densities and a locally AC flux. -/
theorem angular_has_densities (R β : ℝ) (hR : 1 ≤ R) (F H : Measure ℝ)
    (hang : IsBellmanAngularAdjointPair 1 R β F H) :
    ∃ f h J : ℝ → ℝ,
      F = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
      H = volume.withDensity (fun y => ENNReal.ofReal (h y)) ∧
      LocallyIntegrable f volume ∧ (∀ᵐ y ∂volume, 0 ≤ f y) ∧
      (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) ∧
      (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b) ∧
      (∀ᵐ y ∂volume, f y ≤ h y ∧ h y ≤ R * f y) ∧
      (∀ᵐ y ∂volume, deriv h y = J y - y ^ 2 * f y / 3) ∧
      (∀ᵐ y ∂volume, deriv J y = -(β - 2) / 3 * y * f y) := by
  let : IsFiniteMeasureOnCompacts F := hang.1
  let : IsFiniteMeasureOnCompacts H := hang.2.2.1
  obtain ⟨j, hj⟩ := bellmanAngularFlux_weak R β F H hang
  let A := bellmanMeasurePrimitive F id 0
  let J := fun x => j - ((β - 2) / 3) * A x
  have hJ : LocallyIntegrable J volume := by
    convert! (continuous_const : Continuous (fun _ => j)).locallyIntegrable.sub
      ((bellmanMeasurePrimitive_locallyIntegrable F id continuous_id).smul ((β - 2) / 3)) using 1
  obtain ⟨c, hH, hnH⟩ := bellman_measure_density_of_flux F H (fun x => x ^ 2) J
    (continuous_id.pow 2) hJ (1 / 3) hj
  let h := fun x => c + (∫ z in 0..x, J z) -
    (1 / 3 : ℝ) * bellmanMeasurePrimitive F (fun z => z ^ 2) 0 x
  have hFH : F ≤ H := by simpa using hang.2.2.2.2.1
  have hFvol : F ≪ volume := hFH.absolutelyContinuous.trans (by
    rw [hH]; exact withDensity_absolutelyContinuous _ _)
  let f := fun x => (F.rnDeriv volume x).toReal
  have hfm := (Measure.measurable_rnDeriv F volume).ennreal_toReal
  have hf := bellman_rnDeriv_locallyIntegrable F volume
  have hfn : ∀ᵐ x ∂volume, 0 ≤ f x := ae_of_all _ fun _ => ENNReal.toReal_nonneg
  have hF :=
    bellman_rnDeriv_density F hFvol
  have hJeq : J = fun y => j - ((β - 2) / 3) * (∫ z in 0..y, z * f z) := by
    funext y
    dsimp [J, A]
    rw [bellmanMeasurePrimitive_eq_rnMoment F hFvol]
    rfl
  have hheq : h = fun y => c + (∫ z in 0..y, J z) -
      (1 / 3 : ℝ) * (∫ z in 0..y, z ^ 2 * f z) := by
    funext y
    dsimp [h]
    rw [bellmanMeasurePrimitive_eq_rnMoment F hFvol]
  have hhac : ∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b := by
    intro a b hab
    rw [hheq]
    convert! ((bellman_const_locallyAC c a b).add
      (bellman_lebesguePrimitive_locallyAC J hJ a b hab)).sub
      ((bellman_moment_locallyAC f hf 2 a b hab).const_mul (1 / 3)) using 1
  have hJac : ∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b := by
    intro a b hab
    rw [hJeq]
    have hi : LocallyIntegrable (fun x => x * f x) volume := by
      simpa using bellman_polynomial_locallyIntegrable f hf 1
    convert! (bellman_const_locallyAC j a b).sub
      ((bellman_lebesguePrimitive_locallyAC _ hi a b hab).const_mul ((β - 2) / 3)) using 1
  have hhn := hnH
  have hRf : ∀ᵐ x ∂volume, 0 ≤ R * f x := by
    filter_upwards [hfn] with x hx
    exact mul_nonneg (by linarith) hx
  have hHR : ∀ᵐ x ∂volume, h x ≤ R * f x := by
    apply bellman_density_le_of_measure_le h (fun x => R * f x) ((bellman_locallyAC_continuous hhac).measurable) hhn hRf
    have he : volume.withDensity (fun x => ENNReal.ofReal (R * f x)) =
        ENNReal.ofReal R • F := by
      rw [show (fun x => ENNReal.ofReal (R * f x)) =
        ENNReal.ofReal R • (fun x => ENNReal.ofReal (f x)) by
          funext x; exact ENNReal.ofReal_mul (by linarith),
        withDensity_smul _ hfm.ennreal_ofReal, ← hF]
    rw [← hH, he]
    exact hang.2.2.2.2.2.1
  refine ⟨f, h, J, hF, hH, hf, hfn, hhac, hJac, ?_, ?_, ?_⟩
  · filter_upwards [(bellman_density_le_of_measure_le f h hfm hfn hhn (by rw [← hF, ← hH]; exact hFH)), hHR] with x hx hy
    exact ⟨hx, hy⟩
  · rw [hheq]
    exact bellman_momentDensity_deriv f J hf hJ c
  · rw [hJeq]
    filter_upwards [bellman_momentFlux_deriv f hf j ((β - 2) / 3)] with x hx
    rw [hx]
    ring

end HypoellipticAleksandrov.KineticAleksandrov

