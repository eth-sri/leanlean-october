module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsPieces
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalPoleMixtures

/-! # Physical-to-subtype mixtures for the canonical enlarged-strip kernels -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory ProbabilityTheory

variable (H : FiniteIntervalUnion) (T : ℝ)

/-- Mapping the union poles back recovers the entire supported physical source. -/
theorem enlargedUnionPoleMeasure_map  (mu : Measure Point)
    (hmu : ∀ᵐ p ∂mu, p ∈ enlargedVisitPoleSet H T) :
    (visitUnionPoleMeasure H T mu).map Subtype.val = mu := by
  apply visitPoleMeasure_map_comap _ (measurableSet_finiteUnionPole H T)
  exact hmu.mono fun p hp => ⟨WithTop.coe_lt_coe.mpr hp.1, hp.2⟩

/-- Any actual union-pole family has the same mixture as its physical zero extension. -/
theorem enlargedExtendKernel_comp_unionPole
    (f : FiniteUnionPole H (T : WithTop ℝ) → Measure Point) (hf : Measurable f)
    (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, p ∈ enlargedVisitPoleSet H T) :
    visitExtendKernel _ (measurableSet_enlargedVisitPoleSet H T)
      (fun p => f (enlargedVisitPole H T p)) (hf.comp (measurable_enlargedVisitPole H T))
      ∘ₘ mu = (visitUnionPoleMeasure H T mu).bind f := by
  classical
  let nu := visitUnionPoleMeasure H T mu
  let k := visitExtendKernel _ (measurableSet_enlargedVisitPoleSet H T)
    (fun p => f (enlargedVisitPole H T p)) (hf.comp (measurable_enlargedVisitPole H T))
  have hm  := enlargedUnionPoleMeasure_map H T mu hmu
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

section
variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : ℝ) (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, p ∈ enlargedVisitPoleSet H T)

include hmu
/-- The actual physical Green composition is exactly the nested theorem's Green mixture. -/
theorem enlargedGreenKernel_comp_poles
     :
    enlargedVisitGreenKernel hH hLE hlam hLam A H T ∘ₘ mu =
      finiteUnionGreenMixture hH hLE hlam hLam A H T (visitUnionPoleMeasure H T mu) :=
  enlargedExtendKernel_comp_unionPole H T _ (finiteUnionGreen_measurable hH hLE hlam hLam A H T)
    mu hmu

/-- The actual physical exit composition is exactly the nested theorem's exit mixture. -/
theorem enlargedExitKernel_comp_poles
     :
    enlargedVisitExitKernel hH hLE hlam hLam A H T ∘ₘ mu =
      finiteUnionExitMixture hH hLE hlam hLam A H T (visitUnionPoleMeasure H T mu) :=
  enlargedExtendKernel_comp_unionPole H T _ (finiteUnionExit_measurable hH hLE hlam hLam A H T)
    mu hmu
end


variable (H1 H2 : FiniteIntervalUnion) (hsub : H1.carrier ⊆ H2.carrier) (T : ℝ) (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, p ∈ enlargedVisitPoleSet H1 T)

include hmu
/-- Including source poles into the larger union retains exactly their physical measure. -/
theorem enlargedUnionPoleMeasure_nested_map  :
    ((visitUnionPoleMeasure H1 T mu).map
      (finiteUnionNestedPoleInclusion H1 H2 hsub T)).map Subtype.val = mu := by
  rw [Measure.map_map measurable_subtype_coe
    (measurable_finiteUnionNestedPoleInclusion H1 H2 hsub T)]
  exact enlargedUnionPoleMeasure_map H1 T mu hmu

/-- Mapping smaller source poles into the larger domain is exactly the larger pole pullback. -/
theorem enlargedUnionPoleMeasure_nested_eq  :
    (visitUnionPoleMeasure H1 T mu).map (finiteUnionNestedPoleInclusion H1 H2 hsub T) =
      visitUnionPoleMeasure H2 T mu := (MeasurableEmbedding.map_injective (MeasurableEmbedding.subtype_coe (measurableSet_finiteUnionPole H2 T))
  (Eq.trans (enlargedUnionPoleMeasure_nested_map H1 H2 hsub T mu hmu)
    (Eq.symm (enlargedUnionPoleMeasure_map H2 T mu (Filter.Eventually.mono hmu fun p hp => ⟨hp.left, hsub hp.right⟩)))))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
