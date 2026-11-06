module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoHomogeneity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileBounds

/-! # Classical flattened-profile regularity in dimensions at least two -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set Filter

/- The explicit selected flattening jets are the classical jets almost everywhere. -/
theorem flatProfile_jets_ae_of_profile {d alpha}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ q ∂volume, flatProfilePositionJet h r q = dx (selectedFlatProfile h r) q ∧
      flatProfileVelocityJet h r q = dv (selectedFlatProfile h r) q ∧
      flatProfileHessian h r q = dvv (selectedFlatProfile h r) q := by
  filter_upwards [((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.1), ((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)] with q hj hH
  refine ⟨?_, ?_, ?_⟩
  · ext i
    unfold dx selectedFlatProfile
    rw [fderiv_flatProfile _ _ _ hr q (hH.differentiableAt (by norm_num))]
    change -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) *
      profilePositionJet h q i =
        -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) * dx (profileFunction h) q i
    rw [hj.1]
  · ext i
    unfold dv selectedFlatProfile
    rw [fderiv_flatProfile _ _ _ hr q (hH.differentiableAt (by norm_num))]
    change -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) *
      profileVelocityJet h q i =
        -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) * dv (profileFunction h) q i
    rw [hj.2.1]
  · ext i k
    rw [selectedFlatProfile, dvv_flatProfile_of_contDiffAt _ _ _ hr q hH i k]
    unfold flatProfileHessian
    rw [hj.2.1, hj.2.2]

/- The literal stationary operator equals the source formula a.e. in the classical branch. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
