module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitTimeWindowIntegrals
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassOutgoing
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitTimeIntegrals

/-! # Genuine per-entrance short-time counting inequalities before outer domination -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/- The actual localized quadratic is bounded above by nine-sixteenths r squared everywhere. -/
theorem visitTimeQuadratic_le (c : Clock) (b : ℝ) (p : Point) :
    visitTimeCutoff b c.r c.positive p.time * visitQuadratic c (p.velocity 0) ≤
      9 * c.r ^ 2 / 16 := by
  have he := (visitTimeCutoff_properties b c.r c.positive).2 p.time
  have h := mul_le_mul_of_nonneg_left (visitQuadratic_le c (p.velocity 0)) he.1
  have hh := mul_le_mul_of_nonneg_right he.2 (by positivity : 0 ≤ 9 * c.r ^ 2 / 16)
  simp only [one_mul] at hh
  exact h.trans hh

/- Removing the zero internal face bounds the localized exit integral by retained exit mass. -/
theorem visitTimeQuadratic_partial_mass_bound : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
      (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
      (c : Clock) (J : Interval) (s T b : ℝ) (P : Point)
      (_hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ),
      let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P
      let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
      let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
      let B := visitBoundary s T (visitActiveInterval c) J
      5 * c.r ^ 2 / 16 *
        (∑ n ∈ Finset.range N, (mu n {p | p.time ∈ Icc b (b + c.r ^ 2)}).toReal) ≤
        9 * c.r ^ 2 / 16 *
          (∑ n ∈ Finset.range N, (((E ∘ₘ mu n).restrict Bᶜ) univ).toReal) +
        (9 * D / 16 + 2 * Lam) *
          (∑ n ∈ Finset.range N,
            ((G ∘ₘ mu n) {p | p.time ∈ Icc (b - c.r ^ 2) (b + 2 * c.r ^ 2)}).toReal) := by
  obtain ⟨D, hD, hd⟩ :
      ∃ D : ℝ, 0 ≤ D ∧
          ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
            (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
            (c : Clock) (J : Interval) (s T b : ℝ) (P : Point)
            (_hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (n : ℕ),
            let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P n
            let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
            let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
            let B := visitBoundary s T (visitActiveInterval c) J
            5 * c.r ^ 2 / 16 * (mu {p | p.time ∈ Icc b (b + c.r ^ 2)}).toReal ≤
              9 * c.r ^ 2 / 16 * (((E ∘ₘ mu).restrict Bᶜ) univ).toReal +
                (9 * D / 16 + 2 * Lam) *
                  ((G ∘ₘ mu) {p | p.time ∈ Icc (b - c.r ^ 2) (b + 2 * c.r ^ 2)}).toReal := by
    obtain ⟨D, hD, hd⟩ := visitTimeQuadratic_activeGreen_integral_bound
    refine ⟨D, hD, ?_⟩
    intro hH hLE lam Lam hlam hLam A c J s T b P hP n
    dsimp only
    let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P n
    have hx :
        let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P n
            let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
            let B := visitBoundary s T (visitActiveInterval c) J
            (∫ p, visitTimeCutoff b c.r c.positive p.time * visitQuadratic c (p.velocity 0)
              ∂E ∘ₘ mu) ≤ 9 * c.r ^ 2 / 16 * (((E ∘ₘ mu).restrict Bᶜ) univ).toReal := by
      dsimp only
      let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P n
      let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
      let B := visitBoundary s T (visitActiveInterval c) J
      let f := fun p : Point => visitTimeCutoff b c.r c.positive p.time *
        visitQuadratic c (p.velocity 0)
      have hiE : Integrable f (E ∘ₘ mu) :=
        visitTimeQuadratic_integrable_activeExitMixture hH hLE hlam hLam A c J s T b mu
      have hi := integral_mono_ae (hiE.restrict (s := Bᶜ))
        (integrable_const (9 * c.r ^ 2 / 16))
        (Filter.Eventually.of_forall (visitTimeQuadratic_le c b))
      have hx : (∫ p, f p ∂(E ∘ₘ mu).restrict Bᶜ) ≤
          9 * c.r ^ 2 / 16 * (((E ∘ₘ mu).restrict Bᶜ) univ).toReal := by
        simpa only [integral_const, smul_eq_mul, Measure.real, mul_comm] using hi
      have hz : (∫ p, f p ∂(E ∘ₘ mu).restrict B) = 0 :=
        visitTimeQuadratic_outgoing_integral_zero hH hLE hlam hLam A c J s T b P n
      have hs := integral_add_compl (measurableSet_visitBoundary s T (visitActiveInterval c) J) hiE
      rw [hz, zero_add] at hs
      exact hs.symm.le.trans hx
    have hg := hd hH hLE lam Lam hlam hLam A c J s T b mu inferInstance
    have hh :
        let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P n
            let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
            let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
            let f := fun q : Point => visitTimeCutoff b c.r c.positive q.time *
              visitQuadratic c (q.velocity 0)
            (∫ p, f p ∂mu) = (∫ p, f p ∂E ∘ₘ mu) -
              ∫ p, forwardScalarOperator A.a f p ∂G ∘ₘ mu := by
      classical
      dsimp only
      let mu := visitEntrancePiece hH hLE hlam hLam A c J s T P n
      let E := visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
      let G := visitUnionGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) s T
      let f := fun q : Point => visitTimeCutoff b c.r c.positive q.time *
        visitQuadratic c (q.velocity 0)
      let g := fun p => forwardScalarOperator A.a f p
      have hE :=
        visitTimeQuadratic_integrable_activeExitMixture hH hLE hlam hLam A c J s T b mu
      have hG :=
        visitTimeQuadratic_operator_integrable_activeGreenMixture hH hLE hlam hLam A c J s T b mu
      have hiE : Integrable (fun p => ∫ q, f q ∂E p) mu := by
        rw [Measure.comp_eq_comp_const_apply] at hE
        simpa only [Kernel.const_apply] using hE.integral_comp
      have hiG : Integrable (fun p => ∫ q, g q ∂G p) mu := by
        rw [Measure.comp_eq_comp_const_apply] at hG
        simpa only [Kernel.const_apply] using hG.integral_comp
      have hp : f =ᵐ[mu] fun p => (∫ q, f q ∂E p) - ∫ q, g q ∂G p := by
        filter_upwards [visitEntrancePiece_ae_activePole hH hLE hlam hLam A c J s T P hP n]
          with p hp
        let ep := visitPoleInclusion (visitActiveUnion c J) s T ⟨p, hp⟩
        have he : E p = finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) T ep := by
          change (if ht : p ∈ visitPoleSet (visitActiveUnion c J) s T then
            finiteUnionExit hH hLE hlam hLam A (visitActiveUnion c J) T
              (visitPoleInclusion _ s T ⟨p, ht⟩) else 0) = _
          rw [dite_eq_left hp]
        have hg : G p = finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T ep := by
          change (if ht : p ∈ visitPoleSet (visitActiveUnion c J) s T then
            finiteUnionGreen hH hLE hlam hLam A (visitActiveUnion c J) T
              (visitPoleInclusion _ s T ⟨p, ht⟩) else 0) = _
          rw [dite_eq_left hp]
        have hh := visitTimeQuadratic_active_identity hH hLE hlam hLam A c J b T ep
        dsimp only at hh
        rw [← he, ← hg] at hh
        exact hh
      change (∫ p, f p ∂mu) = (∫ p, f p ∂E ∘ₘ mu) - ∫ p, g p ∂G ∘ₘ mu
      rw [integral_congr_ae hp, integral_sub hiE hiG]
      rw [nested_integral_bind mu E E.measurable f hE,
        nested_integral_bind mu G G.measurable g hG]
    dsimp only at hx hg hh
    have hi := (visitTimeQuadratic_entrance_integral_lower
      hH hLE hlam hLam A c J s T b P n).trans hh.le
    rw [sub_eq_add_neg] at hi
    exact hi.trans (add_le_add hx hg)

  refine ⟨D, hD, ?_⟩
  intro hH hLE lam Lam hlam hLam A c J s T b P hP N
  have h := Finset.sum_le_sum (s := Finset.range N)
    (fun n _ => hd hH hLE lam Lam hlam hLam A c J s T b P hP n)
  dsimp only at h ⊢
  simpa only [Finset.mul_sum, Finset.sum_add_distrib] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
