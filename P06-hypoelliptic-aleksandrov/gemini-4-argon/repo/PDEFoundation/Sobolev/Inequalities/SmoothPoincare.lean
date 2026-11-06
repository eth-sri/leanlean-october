module

public import PDEFoundation.Measure.SegmentDouble
public import PDEFoundation.Sobolev.Inequalities.SmoothSegment
public import PDEFoundation.Sobolev.Mean
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Prod
import PDEFoundation.Measure.AffineVolume
import PDEFoundation.Measure.Jensen
import PDEFoundation.Measure.NormalizedLp

/-!
# Smooth convex-domain Poincaré estimates

This file collects the bounded-domain integrability facts and analytic
estimates used before passing the diameter-only Poincaré inequality from
globally smooth functions to Sobolev representatives.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal
open scoped Pointwise

/- For a fixed point, the `p`th power of the smooth pairwise oscillation is
integrable on a bounded Sobolev-regular domain. -/
theorem integrableOn_abs_sub_integralAverage_rpow_of_contDiff
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U)
    {u : Vec d → ℝ} (hu : ContDiff ℝ 0 u)
    {p : ℝ} (hp : 0 ≤ p) :
    IntegrableOn
      (fun x => |u x - integralAverage U u| ^ p)
      U volume := by
  have huCont : Continuous u :=
    hu.continuous
  have hcont :
      Continuous
        (fun x => |u x - integralAverage U u| ^ p) :=
    Real.continuous_rpow_const hp
      |>.comp (huCont.sub continuous_const).abs
  have hclosureCompact : IsCompact (closure U) :=
    hU.isBoundedDomain.isBounded.isCompact_closure
  exact
    (hcont.continuousOn.integrableOn_compact
      hclosureCompact).mono_set subset_closure

/- The `p`th power of pairwise smooth oscillation is integrable on the
product of a bounded Sobolev-regular domain with itself. -/
theorem integrableOn_prod_abs_sub_rpow_of_contDiff
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U)
    {u : Vec d → ℝ} (hu : ContDiff ℝ 0 u)
    {p : ℝ} (hp : 0 ≤ p) :
    IntegrableOn
      (fun z : Vec d × Vec d =>
        |u z.1 - u z.2| ^ p)
      (U ×ˢ U) (volume.prod volume) := by
  have huCont : Continuous u :=
    hu.continuous
  have hcont :
      Continuous
        (fun z : Vec d × Vec d =>
          |u z.1 - u z.2| ^ p) :=
    Real.continuous_rpow_const hp
      |>.comp
        ((huCont.comp continuous_fst).sub
          (huCont.comp continuous_snd)).abs
  have hclosureCompact :
      IsCompact (closure U ×ˢ closure U) :=
    hU.isBoundedDomain.isBounded.isCompact_closure.prod
      hU.isBoundedDomain.isBounded.isCompact_closure
  have hprod :
      IntegrableOn
        (fun z : Vec d × Vec d =>
          |u z.1 - u z.2| ^ p)
        (closure U ×ˢ closure U)
        (volume.prod volume) :=
    hcont.continuousOn.integrableOn_compact
      hclosureCompact
  exact hprod.mono_set (Set.prod_mono subset_closure subset_closure)

/- Integrated Jensen inequality comparing oscillation about the arithmetic
mean with the normalized pairwise oscillation. -/
end PDE
