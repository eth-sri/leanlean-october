module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegration
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationSetting
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationProductIntegrals
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationRadialTest
import Mathlib.Tactic

/-! # Derivation of the source angular weak equation from the actual adjoint pair -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The actual homogeneous stationary pair has angular measures satisfying the source
equation. -/
theorem exists_angular_adjoint (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (μ η : Measure BellmanPuncturedPlane) (hp : IsBellmanAdjointPair 1 R β μ η) :
    ∃ F H : Measure ℝ,
      (μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β F ∧
        η.restrict {q | 0 < q.val.1} = bellmanAngularRep β H) ∧
      IsBellmanAngularAdjointPair 1 R β F H := by
  obtain ⟨F, H, hrep, hF, hFi, hH, hHi, hlo, hhi⟩ :=
    angular_disintegration R β hR hβ μ η hp
  let := hF
  let := hH
  refine ⟨F, H, hrep, hF, hFi, hH, hHi, ?_, hhi, ?_⟩
  · simpa using hlo
  intro φ hφ hcφ
  obtain ⟨ζ, hζ, hcζ, hsζ, hK, hrel⟩ := exists_bellmanAngularRadialTest β
  have hsζp : tsupport ζ ⊆ Ioi 0 :=
    fun s hs => lt_trans (by norm_num) (hsζ hs).1
  have he := hp.2.2.2.2.2.1 (bellmanAngularTest ζ φ) (bellmanAngularTest_contDiff ζ φ hζ hφ hsζp) ((bellmanAngularTest_support_data ζ φ hcζ hcφ hsζp).1) (bellmanAngularTest_support_punctured ζ φ hcζ hcφ hsζp)
  let fx :=
    fun q => q.2 * fderiv ℝ (bellmanAngularTest ζ φ) q (1, 0)
  let fv :=
    fun q => fderiv ℝ (fun z => fderiv ℝ (bellmanAngularTest ζ φ) z (0, 1)) q (0, 1)
  have hts := (bellmanAngularTest_support_data ζ φ hcζ hcφ hsζp).2
  rw [← bellman_integral_positive_restrict μ fx (tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ (1, 0)).trans hts)),
    ← bellman_integral_positive_restrict η fv ((tsupport_fderiv_apply_subset ℝ (0, 1)).trans ((tsupport_fderiv_apply_subset ℝ (0, 1)).trans hts)), hrep.1, hrep.2] at he
  rw [bellmanAngularRep_transport_integral β F ζ φ hζ hφ hcζ hcφ hsζp,
    bellmanAngularRep_velocity_integral β H ζ φ hζ hφ, hrel] at he
  have hzero : (∫ s, ζ s.val / s.val ^ 2 ∂bellmanRadialWeight β) *
      ((∫ y, deriv (deriv φ) y ∂H) - (1 / 3) * (∫ y, y ^ 2 * deriv φ y ∂F) +
        ((β - 2) / 3) * (∫ y, y * φ y ∂F)) = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hzero).resolve_left hK.ne'

end HypoellipticAleksandrov.KineticAleksandrov
