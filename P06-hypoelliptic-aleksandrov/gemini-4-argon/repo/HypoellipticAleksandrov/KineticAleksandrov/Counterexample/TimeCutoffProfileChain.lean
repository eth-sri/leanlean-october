module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningSourceProfile

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffProfileSobolev
public import PDEFoundation.Sobolev.W1p.Smooth
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffWeakSecond
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffSecondBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningProfile
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyWeakCoordinates
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffWeak
import Mathlib.Topology.MetricSpace.ProperSpace

/-! # The first weak chain rule applied to the literal flattened profile and barrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set MeasureTheory
open scoped ENNReal

/- The literal velocity barrier in the measure-preserving spatial chart. -/
def spatialPackedBarrier (d ) (mu R t : ℝ) (x : PDE.Vec (d + d)) : ℝ :=
  barrier mu R ⟨t, (spatialCoordinateCLE d x).1, (spatialCoordinateCLE d x).2⟩

/- The packed barrier is globally smooth at every finite order. -/
theorem contDiff_spatialPackedBarrier (d : ℕ) (mu R t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialPackedBarrier d mu R t) := by
  simpa only [spatialPackedBarrier, barrier, Function.comp_apply] using!
    (contDiff_const (c := Real.exp (-mu * t))).mul ((contDiff_const (c := (2 : ℝ))).sub
      ((PDE.contDiff_vecNormSq.comp (spatialCoordinateCLE d).contDiff.snd).div_const (R ^ 2)))

/- The first weak chain rule for the actual cutoff profile. All regularity of the
flattened profile is discharged by the complete published upstream source theorem. -/
theorem weakGradient_timeCutoffProfile_of_flatProfile_source
    (hflat : ∀ {d : ℕ}, 1 ≤ d → ∀ {alpha : ℝ}, 0 < alpha → alpha < 1 →
      ∀ h : CounterProfileStatement d alpha, ∀ r : ℝ, 0 < r →
        FlatProfileSourceStatement h r)
    {d } (hd : 1 ≤ d) {alpha } (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    {D } (hD : PDE.IsOpenBoundedConvexDomain D)
    (mu R t : ℝ) :
    PDE.HasWeakGradientOn D
      (fun x => timeCutoffTheta
        (selectedFlatProfile h r (spatialCoordinateCLE d x) - spatialPackedBarrier d mu R t x))
      (fun x i => deriv timeCutoffTheta
        (selectedFlatProfile h r (spatialCoordinateCLE d x) - spatialPackedBarrier d mu R t x) *
        (spatialPackedGradient (flatProfilePositionJet h r) (flatProfileVelocityJet h r) x i -
          PDE.classicalGradient (spatialPackedBarrier d mu R t) x i)) := by
  let u := flatProfileW1p_of_flatProfile_source hflat hd ha ha1 h r hr hD
  let B := PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain (p := 2) hD
    ((contDiff_spatialPackedBarrier d mu R t).of_le (by simp))
  simpa only [u, B, flatProfileW1p_of_flatProfile_source,
    PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
    PDE.W1pFunction.ofContDiffOnIsSobolevRegularDomain] using!
    weakGradient_timeCutoff_sub hD (by norm_num) (by norm_num) u B

/- The actual velocity Hessian chain rule for the cutoff profile, proved using the
same first and second upstream weak representatives and the smooth barrier. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
