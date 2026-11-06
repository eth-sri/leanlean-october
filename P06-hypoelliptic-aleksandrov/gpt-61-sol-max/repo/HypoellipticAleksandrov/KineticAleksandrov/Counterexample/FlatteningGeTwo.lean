module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoHomogeneity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileBounds

/-! # Classical flattened-profile regularity in dimensions at least two -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory

variable {d : ℕ} {alpha : ℝ} (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)

include hr
/-- The explicit selected flattening jets are the classical jets almost everywhere. -/
theorem flatProfile_jets_ae_of_profile  :
    ∀ᵐ q, flatProfilePositionJet h r q = dx (selectedFlatProfile h r) q ∧
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

/-- The literal stationary operator equals the source formula a.e. in the classical branch. -/
theorem flatProfile_operator_ae_of_profile  :
    ∀ᵐ q, statOp (profileMatrix h) (selectedFlatProfile h r) q =
      flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q := by
  filter_upwards [flatProfile_jets_ae_of_profile h r hr,
    flatProfile_representatives_source h r] with q hj hs
  unfold statOp
  rw [← hj.1, ← hj.2.2]
  exact hs

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
