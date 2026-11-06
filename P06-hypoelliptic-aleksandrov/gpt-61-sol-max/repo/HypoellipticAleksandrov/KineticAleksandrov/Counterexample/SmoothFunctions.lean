module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ExtensionContinuity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyHeight
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifySupport
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifySource
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Height
import Batteries.Tactic.Alias



/-! # Actual smooth functions from the fixed-domain zero extension -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set MeasureTheory

/-- The actual smooth function, obtained by spatial smoothing after zero extension. -/
def smoothedZeroExtendedProfile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ)
    (phi : ContDiffBump (0 : XV d)) (P : KineticPoint d) : ℝ :=
  spatialMollify phi (fun y => zeroExtendedProfile (profileFunction h) alpha r mu R
    ⟨P.time, y.1, y.2⟩) (P.position, P.velocity)

/-- Smoothness is joint in the native product chart. -/
alias smoothedZeroExtendedProfile_contDiff := _root_.HypoellipticAleksandrov.KineticAleksandrov.Counterexample.spatial_zeroExtendedProfile_contDiff_of_profile

variable {d : ℕ} {alpha : ℝ} (h : CounterProfileStatement d alpha) (r mu R : ℝ) (phi : ContDiffBump (0 : XV d)) (P : KineticPoint d)

/-- Each constructed smooth function is globally nonnegative. -/
theorem smoothedZeroExtendedProfile_nonneg  :
    0 ≤ smoothedZeroExtendedProfile h r mu R phi P :=
  spatialMollify_nonneg phi _
    (fun y => zeroExtendedProfile_nonneg _ alpha r mu R ⟨P.time, y.1, y.2⟩) _

/-- All nonpositive times remain identically zero after spatial smoothing. -/
theorem smoothedZeroExtendedProfile_eq_zero_of_time  (ht : P.time ≤ 0) :
    smoothedZeroExtendedProfile h r mu R phi P = 0 := by
  unfold smoothedZeroExtendedProfile spatialMollify
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  change phi.normed volume y * zeroExtendedProfile (profileFunction h) alpha r mu R
    ⟨P.time, P.position - y.1, P.velocity - y.2⟩ = 0
  rw [zeroExtendedProfile_eq_zero_of_time _ alpha r mu R
    ⟨P.time, P.position - y.1, P.velocity - y.2⟩ ht, mul_zero]

/-- Spatial smoothing leaves a fixed outer collar whenever its radius is small enough. -/
theorem smoothedZeroExtendedProfile_eq_zero_outside_thickening
    (hq : (P.position, P.velocity) ∉
      Metric.thickening phi.rOut {q | profileFunction h q ≤ 1}) :
    smoothedZeroExtendedProfile h r mu R phi P = 0 := by
  apply spatialMollify_eq_zero_outside_thickening phi _ _ _ _ hq
  exact (subset_tsupport _).trans
    (zeroExtendedProfile_tsupport_subset h r mu R P.time)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
