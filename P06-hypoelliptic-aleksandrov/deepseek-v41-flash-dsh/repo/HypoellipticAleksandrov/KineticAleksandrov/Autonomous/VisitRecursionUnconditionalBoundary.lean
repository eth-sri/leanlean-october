module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalPoleMixtures
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInternalFaces

/-! # Actual supported exit mixtures split into outer exits and internal visit faces -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
section
variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)

/-- An actual supported physical exit mixture lies on its prescribed finite-union exit set. -/
theorem visitUnionExitKernel_comp_ae_exit
     (H : FiniteIntervalUnion) (s T : ℝ) (mu : Measure Point)
    (hmu : ∀ᵐ p ∂mu, p ∈ visitPoleSet H s T) :
    ∀ᵐ p ∂(visitUnionExitKernel hH hLE hlam hLam A H s T ∘ₘ mu),
      p ∈ finiteUnionExitSet H s T := by
  rw [ae_iff, visitUnionExitKernel_comp_poles hH hLE hlam hLam A H s T mu hmu]
  exact finiteUnionExitMixture_compl_exit hH hLE hlam hLam A H s T _
    (visitUnionPoleMeasure_ae_time_gt H s T mu hmu)

/-- Retaining everything except internal restarts is precisely restriction to actual outer exits. -/
theorem visitUnionExitKernel_retained_eq_outer
     (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (s T : ℝ) (mu : Measure Point)
    (hmu : ∀ᵐ p ∂mu, p ∈ visitPoleSet H1 s T) :
    let O := visitUnionExitKernel hH hLE hlam hLam A H1 s T ∘ₘ mu
    O.restrict (finiteUnionInternalExit H1 H2 s T)ᶜ =
      O.restrict (finiteUnionExitSet H2 s T) := by
  apply Measure.restrict_congr_set
  filter_upwards [visitUnionExitKernel_comp_ae_exit hH hLE hlam hLam A H1 s T mu hmu]
    with p hp
  apply propext
  constructor
  · intro hn
    have hh := (congrArg (fun S : Set Point => p ∈ S)
      (finiteUnionExitSet_nested_split H1 H2 hsub s T)).mp hp
    rcases hh with hh | hh
    · exact hh.2
    · exact False.elim (hn hh)
  · intro ho hi
    exact Set.disjoint_left.mp (finiteUnionExitSet_disjoint_internal H1 H2 s T) ho hi

/-- The retained active exit term of the counting proof is exactly the actual outer exit term. -/
theorem visitActiveExitKernel_retained_eq_outer
     (c : Clock) (J : Interval) (s T : ℝ) (mu : Measure Point)
    (hmu : ∀ᵐ p ∂mu, p ∈ visitPoleSet (visitActiveUnion c J) s T) :
    let O := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu
    O.restrict (visitBoundary s T (visitActiveInterval c) J)ᶜ =
      O.restrict (finiteUnionExitSet J.toFiniteUnion s T) := by
  rw [← visitActive_internalExit c J s T]
  have hsub : (visitActiveUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
    rw [visitActiveUnion_carrier, Interval.toFiniteUnion_carrier]
    exact inter_subset_right
  exact visitUnionExitKernel_retained_eq_outer hH hLE hlam hLam A _ _ hsub s T mu hmu
end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
