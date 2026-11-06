module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningSourceProfile

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffProfileChain
public import PDEFoundation.Calculus.RegularityOrder


/-! # Global compact-test identities for the explicit cutoff jets -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample


variable {d : ℕ} {alpha : ℝ} (h : CounterProfileStatement d alpha) (r mu R t : ℝ) (x : PDE.Vec (d + d))

/-- The literal cutoff value before the fixed collar extension, in packed coordinates. -/
def spatialPackedCutoffValue  : ℝ :=
  timeCutoffTheta (selectedFlatProfile h r (spatialCoordinateCLE d x) -
    spatialPackedBarrier d mu R t x)

/-- The first chain-rule representative, including the derivative of the barrier. -/
def spatialPackedCutoffGradient  (i : Fin (d + d)) : ℝ :=
  deriv timeCutoffTheta (selectedFlatProfile h r (spatialCoordinateCLE d x) -
    spatialPackedBarrier d mu R t x) *
    (spatialPackedGradient (flatProfilePositionJet h r) (flatProfileVelocityJet h r) x i -
      PDE.classicalGradient (spatialPackedBarrier d mu R t) x i)

/-- The velocity Hessian representative includes the favorable convexity term. -/
def spatialPackedCutoffVelocityHessian  (i k : Fin d) : ℝ :=
  let s := selectedFlatProfile h r (spatialCoordinateCLE d x) - spatialPackedBarrier d mu R t x
  let g := fun j => flatProfileVelocityJet h r (spatialCoordinateCLE d x) j -
    PDE.classicalGradient (spatialPackedBarrier d mu R t) x (Fin.natAdd d j)
  deriv timeCutoffTheta s *
    (flatProfileHessian h r (spatialCoordinateCLE d x) i k -
      PDE.classicalGradient
        (fun y => PDE.classicalGradient (spatialPackedBarrier d mu R t) y (Fin.natAdd d k))
        x (Fin.natAdd d i)) +
    deriv (deriv timeCutoffTheta) s * g i * g k

section
variable (hflat : ∀ {d : ℕ}, 1 ≤ d → ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 → ∀ h : CounterProfileStatement d alpha, ∀ r : ℝ, 0 < r → FlatProfileSourceStatement h r) {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1) (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) (mu R t : ℝ)

include hflat hd ha ha1 hr
/-- The actual first cutoff jets satisfy global compact-test identities. -/
theorem spatialPackedCutoff_weak_first_of_flatProfile_source
     (i : Fin (d + d)) (test : PDE.Vec (d + d) → ℝ)
    (ht : ContDiff ℝ PDE.smoothOrder test) (hs : HasCompactSupport test) :
    (∫ x, spatialPackedCutoffValue h r mu R t x * fderiv ℝ test x (PDE.basisVec i)) =
      -(∫ x, spatialPackedCutoffGradient h r mu R t x i * test x) := by
  apply weakPartial_global_of_locals i _ _ _ test ht hs
  intro D hD
  exact weakGradient_timeCutoffProfile_of_flatProfile_source
    hflat hd ha ha1 h r hr hD mu R t i

/-- The derivative of the first velocity jet is the literal second-chain representative. -/
theorem spatialPackedCutoff_velocityJet_weak_of_flatProfile_source
     (i k : Fin d) (test : PDE.Vec (d + d) → ℝ)
    (ht : ContDiff ℝ PDE.smoothOrder test) (hs : HasCompactSupport test) :
    (∫ x, spatialPackedCutoffGradient h r mu R t x (Fin.natAdd d k) *
      fderiv ℝ test x (PDE.basisVec (Fin.natAdd d i))) =
      -(∫ x, spatialPackedCutoffVelocityHessian h r mu R t x i k * test x) := by
  apply weakPartial_global_of_locals (Fin.natAdd d i) _ _ _ test ht hs
  intro D hD
  simpa only [spatialPackedCutoffGradient, spatialPackedCutoffVelocityHessian,
    spatialPackedGradient, Fin.addCases_right] using!
    weakSecond_timeCutoffProfile_of_flatProfile_source hflat hd ha ha1 h r hr hD mu R t i k
end


variable {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1) (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) (mu R t : ℝ)

include hd ha ha1 hr
/-- The proved flattened-profile theorem discharges the complete source interface. -/
theorem spatialPackedCutoff_weak_first_of_profile
     (i : Fin (d + d)) (test : PDE.Vec (d + d) → ℝ)
    (ht : ContDiff ℝ PDE.smoothOrder test) (hs : HasCompactSupport test) : type_of% (spatialPackedCutoff_weak_first_of_flatProfile_source flatProfile_source
    hd ha ha1 h r hr mu R t i test ht hs) :=
  spatialPackedCutoff_weak_first_of_flatProfile_source flatProfile_source
    hd ha ha1 h r hr mu R t i test ht hs

/-- The proved flattened-profile theorem discharges the complete source interface. -/
theorem spatialPackedCutoff_velocityJet_weak_of_profile
     (i k : Fin d) (test : PDE.Vec (d + d) → ℝ)
    (ht : ContDiff ℝ PDE.smoothOrder test) (hs : HasCompactSupport test) : type_of% (spatialPackedCutoff_velocityJet_weak_of_flatProfile_source flatProfile_source
    hd ha ha1 h r hr mu R t i k test ht hs) :=
  spatialPackedCutoff_velocityJet_weak_of_flatProfile_source flatProfile_source
    hd ha ha1 h r hr mu R t i k test ht hs

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
