module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionFuture
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassSupport

/-! # Independence of the named lower observation time below the initial pole -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- A supported exit mixture stays strictly later than a common lower pole bound. -/
theorem enlargedExitMixture_ae_time_gt_lower
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T L : ℝ)
    (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, L ≤ p.time) :
    ∀ᵐ q ∂(enlargedVisitExitKernel hH hLE hlam hLam A H T ∘ₘ mu), L < q.time := by
  apply Measure.ae_comp_of_ae_ae
    (isOpen_lt continuous_const continuous_time).measurableSet
  filter_upwards [hmu] with p hp
  exact (enlargedVisitExitKernel_ae_time_gt hH hLE hlam hLam A H T p).mono
    fun q hq => hp.trans_lt hq

/-- Below a supported exit time, changing the named observation lower bound changes no face. -/
theorem enlargedBoundary_restrict_lower_eq (I J : Interval) (s L T : ℝ) (hs : s ≤ L)
    (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, L < p.time) :
    mu.restrict (visitBoundary s T I J) = mu.restrict (visitBoundary L T I J) := by
  apply Measure.restrict_congr_set
  filter_upwards [hmu] with p hp
  have hsp := hs.trans_lt hp
  simp only [visitBoundary, mem_ofPred_eq, hsp, hp, true_and]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
