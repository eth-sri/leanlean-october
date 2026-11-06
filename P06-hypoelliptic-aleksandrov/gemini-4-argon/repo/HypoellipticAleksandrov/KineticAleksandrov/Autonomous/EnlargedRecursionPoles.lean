module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsPieces
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalPoleMixtures

/-! # Physical-to-subtype mixtures for the canonical enlarged-strip kernels -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/- Mapping the union poles back recovers the entire supported physical source. -/
theorem enlargedUnionPoleMeasure_map (H : FiniteIntervalUnion) (T : ℝ) (mu )
    (hmu : ∀ᵐ p ∂mu, p ∈ enlargedVisitPoleSet H T) :
    (visitUnionPoleMeasure H T mu).map Subtype.val = mu := by
  apply visitPoleMeasure_map_comap _ (measurableSet_finiteUnionPole H T)
  exact hmu.mono fun p hp => ⟨WithTop.coe_lt_coe.mpr hp.1, hp.2⟩

/- Any actual union-pole family has the same mixture as its physical zero extension. -/
theorem enlargedExtendKernel_comp_unionPole (H : FiniteIntervalUnion) (T : ℝ)
    (f : FiniteUnionPole H (T : WithTop ℝ) → Measure Point) (hf : Measurable f)
    (mu ) (hmu : ∀ᵐ p ∂mu, p ∈ enlargedVisitPoleSet H T) :
    visitExtendKernel (enlargedVisitPoleSet H T) (measurableSet_enlargedVisitPoleSet H T)
      (fun p => f (enlargedVisitPole H T p)) (hf.comp (measurable_enlargedVisitPole H T))
      ∘ₘ mu = (visitUnionPoleMeasure H T mu).bind f := by
  classical
  let nu := visitUnionPoleMeasure H T mu
  let k := visitExtendKernel (enlargedVisitPoleSet H T) (measurableSet_enlargedVisitPoleSet H T)
    (fun p => f (enlargedVisitPole H T p)) (hf.comp (measurable_enlargedVisitPole H T))
  have hm := enlargedUnionPoleMeasure_map H T mu hmu
  have hb := nested_bind_map nu Subtype.val measurable_subtype_coe k k.measurable
  change mu.bind k = nu.bind f
  rw [← hm]
  apply hb.trans
  apply Measure.bind_congr_right
  apply Filter.Eventually.of_forall
  intro e
  have hp : e.1 ∈ enlargedVisitPoleSet H T :=
    ⟨WithTop.coe_lt_coe.mp e.2.1, e.2.2⟩
  have hi : enlargedVisitPole H T ⟨e.1, hp⟩ = e := Subtype.ext rfl
  change (if ht : e.1 ∈ enlargedVisitPoleSet H T then
    f (enlargedVisitPole H T ⟨e.1, ht⟩) else 0) = f e
  rw [dite_eq_left hp, hi]

/- The actual physical Green composition is exactly the nested theorem's Green mixture. -/
theorem enlargedGreenKernel_comp_poles
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ) (mu )
    (hmu : ∀ᵐ p ∂mu, p ∈ enlargedVisitPoleSet H T) :
    enlargedVisitGreenKernel hH hLE hlam hLam A H T ∘ₘ mu =
      finiteUnionGreenMixture hH hLE hlam hLam A H T (visitUnionPoleMeasure H T mu) :=
  enlargedExtendKernel_comp_unionPole H T _ (finiteUnionGreen_measurable hH hLE hlam hLam A H T)
    mu hmu

/- The actual physical exit composition is exactly the nested theorem's exit mixture. -/
theorem enlargedExitKernel_comp_poles
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ) (mu )
    (hmu : ∀ᵐ p ∂mu, p ∈ enlargedVisitPoleSet H T) :
    enlargedVisitExitKernel hH hLE hlam hLam A H T ∘ₘ mu =
      finiteUnionExitMixture hH hLE hlam hLam A H T (visitUnionPoleMeasure H T mu) :=
  enlargedExtendKernel_comp_unionPole H T _ (finiteUnionExit_measurable hH hLE hlam hLam A H T)
    mu hmu

/- Including source poles into the larger union retains exactly their physical measure. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
