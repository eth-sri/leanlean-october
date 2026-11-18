module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalPoleMixtures
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInternalFaces
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationFiniteBounds

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory


/-- The real masses of all retained active exits in a finite visit sum add to at most one. -/
theorem visitRetainedExit_partial_real_mass_le_one
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
    ∑ n ∈ Finset.range N,
      (((visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ
        visitEntrancePiece hH hLE hlam hLam A c J s T P n).restrict
          (visitBoundary s T (visitActiveInterval c) J)ᶜ) univ).toReal ≤ 1   := by
  have visitUnionExitKernel_mass_le_one (H : FiniteIntervalUnion) (p : Point) :
      visitUnionExitKernel hH hLE hlam hLam A H s T p univ ≤ 1 := by
    classical
    change (if hp : p ∈ visitPoleSet H s T then
      finiteUnionExit hH hLE hlam hLam A H T
        (visitPoleInclusion H s T ⟨p, hp⟩) else 0) univ ≤ 1
    split
    · simp
    · exact zero_le
  have visitActiveExitKernel_retained_eq_outer (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, p ∈ visitPoleSet (visitActiveUnion c J) s T) :
      let O := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ mu
    O.restrict (visitBoundary s T (visitActiveInterval c) J)ᶜ =
      O.restrict (finiteUnionExitSet J.toFiniteUnion s T) := by
    have visitUnionExitKernel_retained_eq_outer (H1 : FiniteIntervalUnion) (H2 : FiniteIntervalUnion) (hsub : H1.carrier ⊆ H2.carrier) (s : ℝ) (T : ℝ) (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, p ∈ visitPoleSet H1 s T) :
        let O := visitUnionExitKernel hH hLE hlam hLam A H1 s T ∘ₘ mu
      O.restrict (finiteUnionInternalExit H1 H2 s T)ᶜ =
        O.restrict (finiteUnionExitSet H2 s T) := by
      have visitUnionExitKernel_comp_ae_exit (H : FiniteIntervalUnion) (s : ℝ) (T : ℝ) (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, p ∈ visitPoleSet H s T) :
          ∀ᵐ p ∂(visitUnionExitKernel hH hLE hlam hLam A H s T ∘ₘ mu),
          p ∈ finiteUnionExitSet H s T := by
        rw [ae_iff, visitUnionExitKernel_comp_poles hH hLE hlam hLam A H s T mu hmu]
        exact finiteUnionExitMixture_compl_exit hH hLE hlam hLam A H s T _
          (visitUnionPoleMeasure_ae_time_gt H s T mu hmu)
      apply Measure.restrict_congr_set
      filter_upwards [visitUnionExitKernel_comp_ae_exit H1 s T mu hmu]
        with p hp
      apply propext
      constructor
      · intro hn
        have hh := (congrArg (fun S => p ∈ S)
          (finiteUnionExitSet_nested_split H1 H2 hsub s T)).mp hp
        rcases hh with hh | hh
        · exact hh.2
        · exact False.elim (hn hh)
      · intro ho hi
        exact Set.disjoint_left.mp (finiteUnionExitSet_disjoint_internal H1 H2 s T) ho hi
    rw [← visitActive_internalExit c J s T]
    have hsub : (visitActiveUnion c J).carrier ⊆ J.toFiniteUnion.carrier := by
      rw [visitActiveUnion_carrier, Interval.toFiniteUnion_carrier]
      exact inter_subset_right
    exact visitUnionExitKernel_retained_eq_outer _ _ hsub s T mu hmu
  have hm := ((visitActiveExit_partial_le hH hLE hlam hLam A c J s T hT P hP N) univ).trans
    (visitUnionExitKernel_mass_le_one J.toFiniteUnion P)
  have hr := ENNReal.toReal_mono (by simp) hm
  rw [ENNReal.toReal_one, visit_partial_real_mass _ N univ MeasurableSet.univ] at hr
  convert hr using 1
  apply Finset.sum_congr rfl
  intro n _
  rw [visitActiveExitKernel_retained_eq_outer _
    (visitEntrancePiece_ae_activePole hH hLE hlam hLam A c J s T P hP n)]

/-- On an interior physical pole, the single-interval union kernel is the original strip Green. -/
theorem visitOuterGreen_eq_strip
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (J : Interval) (s T : ℝ) (P : Point)
    (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) :
    visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T P =
      stripGreen hH hLE hlam hLam A J T
        ⟨P, WithTop.coe_lt_coe.mpr hP.2.1, hP.2.2⟩ := by
  classical
  have hp : P ∈ visitPoleSet J.toFiniteUnion s T := by
    exact ⟨hP.1, hP.2.1, by simpa only [Interval.toFiniteUnion_carrier] using hP.2.2⟩
  change (if ht : P ∈ visitPoleSet J.toFiniteUnion s T then
    finiteUnionGreen hH hLE hlam hLam A J.toFiniteUnion T
      (visitPoleInclusion _ s T ⟨P, ht⟩) else 0) = _
  rw [dite_eq_left hp]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

