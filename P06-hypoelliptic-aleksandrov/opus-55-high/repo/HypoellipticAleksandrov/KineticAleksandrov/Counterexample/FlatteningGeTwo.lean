module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoHomogeneity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileBounds

/-! # Classical flattened-profile regularity in dimensions at least two -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set Filter

variable {d : ℕ} {alpha : ℝ} (h : CounterProfileStatement d alpha) (r : ℝ)

/-- The explicit selected flattening jets are the classical jets almost everywhere. -/
theorem flatProfile_jets_ae_of_profile  (hr : 0 < r) :
    ∀ᵐ q ∂volume, flatProfilePositionJet h r q = dx (selectedFlatProfile h r) q ∧
      flatProfileVelocityJet h r q = dv (selectedFlatProfile h r) q ∧
      flatProfileHessian h r q = dvv (selectedFlatProfile h r) q := by
  have hC2 := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hjets := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  filter_upwards [hjets, hC2] with q hj hH
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
    simp_all
  · ext i k
    rw [selectedFlatProfile, dvv_flatProfile_of_contDiffAt _ _ _ hr q hH i k]
    unfold flatProfileHessian
    simp_all

/-- The literal stationary operator equals the source formula a.e. in the classical branch. -/
theorem flatProfile_operator_ae_of_profile  (hr : 0 < r) :
    ∀ᵐ q ∂volume, statOp (profileMatrix h) (selectedFlatProfile h r) q =
      flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q := by
  filter_upwards [flatProfile_jets_ae_of_profile h r hr,
    flatProfile_representatives_source h r] with q hj hs
  aesop

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
