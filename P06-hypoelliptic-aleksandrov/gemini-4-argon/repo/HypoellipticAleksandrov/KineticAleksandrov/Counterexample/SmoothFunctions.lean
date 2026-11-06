module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ExtensionContinuity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyHeight
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifySupport
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifySource
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Height
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffOperator
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeRegularityExtension
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Piecewise

/-! # Actual smooth functions from the fixed-domain zero extension -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set MeasureTheory

/- The actual smooth function, obtained by spatial smoothing after zero extension. -/
def smoothedZeroExtendedProfile {d alpha}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ)
    (phi : ContDiffBump (0 : XV d)) (P : KineticPoint d) : ℝ :=
  spatialMollify phi (fun y => zeroExtendedProfile (profileFunction h) alpha r mu R
    ⟨P.time, y.1, y.2⟩) (P.position, P.velocity)

/- Smoothness is joint in the native product chart. -/
theorem smoothedZeroExtendedProfile_contDiff {d alpha}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha)
    (r mu R : ℝ) (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2)
    (phi : ContDiffBump (0 : XV d)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × XV d =>
      smoothedZeroExtendedProfile h r mu R phi ((KineticPoint.equivProd d).symm z)) :=
  spatial_zeroExtendedProfile_contDiff_of_profile ha h r mu R hr hmu hR hvel phi

/- Each constructed smooth function is globally nonnegative. -/
theorem smoothedZeroExtendedProfile_nonneg {d alpha}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ)
    (phi : ContDiffBump (0 : XV d)) (P : KineticPoint d) :
    0 ≤ smoothedZeroExtendedProfile h r mu R phi P :=
  spatialMollify_nonneg phi _
    (fun y => zeroExtendedProfile_nonneg _ alpha r mu R ⟨P.time, y.1, y.2⟩) _

/- All nonpositive times remain identically zero after spatial smoothing. -/
theorem smoothedZeroExtendedProfile_eq_zero_of_time {d alpha}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ)
    (phi : ContDiffBump (0 : XV d)) (P : KineticPoint d) (ht : P.time ≤ 0) :
    smoothedZeroExtendedProfile h r mu R phi P = 0 := by
  unfold smoothedZeroExtendedProfile spatialMollify
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  change phi.normed volume y * zeroExtendedProfile (profileFunction h) alpha r mu R
    ⟨P.time, P.position - y.1, P.velocity - y.2⟩ = 0
  rw [zeroExtendedProfile_eq_zero_of_time _ alpha r mu R
    ⟨P.time, P.position - y.1, P.velocity - y.2⟩ ht, mul_zero]

/- Spatial smoothing leaves a fixed outer collar whenever its radius is small enough. -/
theorem smoothedZeroExtendedProfile_eq_zero_outside_thickening {d alpha}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ)
    (phi : ContDiffBump (0 : XV d)) (P : KineticPoint d)
    (hq : (P.position, P.velocity) ∉
      Metric.thickening phi.rOut {q | profileFunction h q ≤ 1}) :
    smoothedZeroExtendedProfile h r mu R phi P = 0 := by
  apply spatialMollify_eq_zero_outside_thickening phi _ _ _ _ hq
  have _h_xinl_0 : tsupport (fun q : XV d => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨P.time, q.1, q.2⟩) ⊆ {q | profileFunction h q ≤ 1} := by
    let t := P.time
    apply closure_minimal ?_ (isClosed_le ((selectedProfile_spec h).2.2.2.2.2.2.1) continuous_const)
    intro q hq
    by_contra hn
    exact hq (zeroExtendedProfile_eq_zero_of_profile _ alpha r mu R _ (not_le.mp hn).le)
  exact (subset_tsupport _).trans
    _h_xinl_0

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
