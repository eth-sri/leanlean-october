module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassInfinite
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceWeakGreenSigned

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter SectionTwo TheoremA Evolution
open scoped Topology ENNReal

/-- The actual finite-horizon source potential obeys the exact quadratic interval estimate. -/
theorem stripPotentialOfRealization_abs_le_quadratic
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (g : BoundedBorel Point) (C : ℝ) (hC : 0 ≤ C) (hg : ∀ p, |g p| ≤ C) :
    |stripPotentialOfKernel H E.2 T g e| ≤
      C * ((e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)) := by
  let q := (e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)
  have hq : 0 ≤ q :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr e.2.2.1.le) (sub_nonneg.mpr e.2.2.2.le))
      (by positivity)
  have hm : (stripGreenOfKernel H E.2 T e).real univ ≤ q := by
    have hmass := stripGreenOfRealization_quadratic_mass hH hlam hLam A H E hE T e
    change stripGreenOfKernel H E.2 T e univ ≤ ENNReal.ofReal q at hmass
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass).trans_eq
      (ENNReal.toReal_ofReal hq)
  have hb : |stripPotentialOfKernel H E.2 T g e| ≤
      C * (stripGreenOfKernel H E.2 T e).real univ := by
    simpa [stripPotentialOfKernel] using
      norm_integral_le_of_norm_le_const (f := (g : Point → ℝ))
        (μ := stripGreenOfKernel H E.2 T e)
        (Eventually.of_forall fun p => by simpa using hg p)
  exact hb.trans (mul_le_mul_of_nonneg_left hm hC)


/-- Exchange physical position and velocity in a bounded Borel source. -/
def nativeStripSource (g : BoundedBorel Point) : BoundedBorel Point :=
  ⟨g ∘ sectionTwoPoint, g.measurable.comp (continuous_sectionTwoPoint 1).measurable, by
    obtain ⟨C, hC, hg⟩ := g.exists_bound
    exact ⟨C, hC, fun p => hg _⟩⟩

/-- The physical source potential is the actual Duhamel potential in native coordinates. -/
def stripSourcePotential (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))
    (T : ℝ) (g : BoundedBorel Point) (p : Point) : ℝ :=
  duhamelPotential K T (nativeStripSource g) (sectionTwoPoint p)

/-- Every valid physical pole has the actual signed bounded-source Green representation. -/
theorem stripSourcePotential_eq_green (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (T : ℝ)
    (g : BoundedBorel Point) (e : StripPole H (T : WithTop ℝ)) :
    stripSourcePotential H K T g e.1 = stripPotentialOfKernel H K T g e := by
  rw [stripPotentialOfKernel, stripGreenOfKernel,
    integral_map (measurable_elapsedPhysicalPoint _ _).aemeasurable
      (show AEStronglyMeasurable (fun p => g p) _ from
        g.measurable.aestronglyMeasurable)]
  exact duhamelPotential_eq_green_bounded H K T (nativeStripSource g) e.1.time (WithTop.coe_lt_coe.mp e.2.1) (stripPoleState H T e) (greenMeasure K e.1.time _ (stripHorizon_pos H T e) _) (greenMeasure_spec K _ _ _ _)

/-- Exchanging physical coordinates converts the actual source potential to native weak forcing. -/
theorem stripSourcePotential_weak {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E)
    (T : ℝ) (g : BoundedBorel Point) :
    IsKineticWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1)
      (evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T)
      (stripSourcePotential H E.2 T g ∘ sectionTwoPoint)
      (fun p => -nativeStripSource g p) := by
  have heq : (stripSourcePotential H E.2 T g ∘ sectionTwoPoint) =
      duhamelPotential E.2 T (nativeStripSource g) := by
    funext p
    change duhamelPotential E.2 T (nativeStripSource g)
      (sectionTwoPoint (sectionTwoPoint p)) = _
    rw [sectionTwoPoint_involutive p]
  rw [heq]
  exact strip_duhamel_weak A H E hE T (nativeStripSource g)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

