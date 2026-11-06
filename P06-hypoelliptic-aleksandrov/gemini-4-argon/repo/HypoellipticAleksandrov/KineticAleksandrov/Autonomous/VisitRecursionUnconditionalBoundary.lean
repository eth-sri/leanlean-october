module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalPoleMixtures
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInternalFaces
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsBoundary

/-! # Actual supported exit mixtures split into outer exits and internal visit faces -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/- An actual supported physical exit mixture lies on its prescribed finite-union exit set. -/
theorem visitUnionExitKernel_retained_eq_outer
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (s T : ℝ) (mu : Measure Point)
    (hmu : ∀ᵐ p ∂mu, p ∈ visitPoleSet H1 s T) :
    let O := visitUnionExitKernel hH hLE hlam hLam A H1 s T ∘ₘ mu
    O.restrict (finiteUnionInternalExit H1 H2 s T)ᶜ =
      O.restrict (finiteUnionExitSet H2 s T) := by
  apply Measure.restrict_congr_set
  have _h_inl_6 : ∀ᵐ p ∂(visitUnionExitKernel hH hLE hlam hLam A H1 s T ∘ₘ mu),
      p ∈ finiteUnionExitSet H1 s T := by
      rw [ae_iff, visitUnionExitKernel_comp_poles hH hLE hlam hLam A H1 s T mu hmu]
      exact finiteUnionExitMixture_compl_exit hH hLE hlam hLam A H1 s T _
        (visitUnionPoleMeasure_ae_time_gt H1 s T mu hmu)

    /- Retaining everything except internal restarts is precisely restriction to actual outer exits. -/
  filter_upwards [_h_inl_6]
    with p hp
  apply propext
  constructor
  · intro hn
    have _h_xinl_0 : finiteUnionExitSet H1 s T = (finiteUnionExitSet H1 s T ∩ finiteUnionExitSet H2 s T) ∪ finiteUnionInternalExit H1 H2 s T := by
      ext p
      constructor
      · intro hp
        rcases hp with hp | hp
        · exact Or.inl ⟨Or.inl hp, Or.inl ⟨hp.1, closure_mono hsub hp.2⟩⟩
        · by_cases hv : p.velocity 0 ∈ H2.carrier
          · exact Or.inr ⟨hp.1, hp.2.1, hp.2.2, hv⟩
          · refine Or.inl ⟨Or.inr hp, Or.inr ⟨hp.1, hp.2.1, ?_⟩⟩
            rw [frontier, H2.isOpen_carrier.interior_eq]
            exact ⟨closure_mono hsub (frontier_subset_closure hp.2.2), hv⟩
      · rintro (hp | hp)
        · exact hp.1
        · exact finiteUnionInternalExit_subset_exit H1 H2 s T hp
    have hh := (congrArg (fun S : Set Point => p ∈ S)
      _h_xinl_0).mp hp
    rcases hh with hh | hh
    · exact hh.2
    · exact False.elim (hn hh)
  · intro ho hi
    have _h_xinl_0 : Disjoint (finiteUnionExitSet H2 s T) (finiteUnionInternalExit H1 H2 s T) := by
        apply Set.disjoint_left.mpr
        intro p hp hs
        rcases hp with hp | hp
        · exact (ne_of_lt hs.2.1) hp.1
        · exact Set.disjoint_left.mp
            (disjoint_frontier_iff_isOpen.mpr H2.isOpen_carrier) hp.2.2 hs.2.2.2

      /- The internal restart set is Borel in physical coordinates. -/
    exact Set.disjoint_left.mp _h_xinl_0 ho hi

/- The retained active exit term of the counting proof is exactly the actual outer exit term. -/
theorem visitActiveExitKernel_retained_eq_outer
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (mu : Measure Point)
    (hmu : ∀ᵐ p ∂mu, p ∈ visitPoleSet (visitActiveUnion c J) s T) :
    let O := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu
    O.restrict (visitBoundary s T (visitActiveInterval c) J)ᶜ =
      O.restrict (finiteUnionExitSet J.toFiniteUnion s T) := by
  rw [← visitActive_internalExit c J s T]
  have hsub : (visitActiveUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
    rw [visitActiveUnion_carrier, Interval.toFiniteUnion_carrier]
    exact inter_subset_right
  exact visitUnionExitKernel_retained_eq_outer hH hLE hlam hLam A _ _ hsub s T mu hmu

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
