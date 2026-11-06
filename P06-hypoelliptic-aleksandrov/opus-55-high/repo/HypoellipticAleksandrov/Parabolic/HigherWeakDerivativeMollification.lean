module

public import HypoellipticAleksandrov.Parabolic.OrdinaryDerivativeIndexPredecessor
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2

/-!
# Higher weak derivatives and spacetime mollification

This file identifies every selected ordinary derivative of one mollified zero
representative with the mollification of the corresponding selected weak
derivative.  It also records smoothness of that common approximant and strong
`L²` convergence of each selected entry.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal Topology

namespace ParabolicWeakDerivativeFamily

variable {d m : ℕ} (gamma : TimeVelocityDerivativeIndex d m) {root : TimeVelocity d → ℝ} (G : ParabolicWeakDerivativeFamily d (2 * m) Set.univ root) (ε : ℝ) (beta : TimeVelocityDerivativeIndex d m)

private theorem ordinaryRepresentative_memLp_volume
     :
    MemLp (G.ordinaryRepresentative beta) (2 : ℝ≥0∞)
      (volume : Measure (TimeVelocity d)) := by
  have h := G.ordinaryRepresentative_memLp beta
  change MemLp _ _
    (volume.restrict Set.univ) at h
  simp_all

private theorem ordinary_timeSucc_eq_add_single
    
    (h : gamma.1.order + 1 ≤ m) :
    (TimeVelocityDerivativeIndex.timeSucc gamma h).1 =
      gamma.1 + Pi.single (timeCoord d) 1 := by
  aesop

private theorem ordinary_velocitySucc_eq_add_single
     (i : Fin d)
    (h : gamma.1.order + 1 ≤ m) :
    (TimeVelocityDerivativeIndex.velocitySucc gamma i h).1 =
      gamma.1 + Pi.single (velocityCoord i) 1 := by
  ext c
  cases c with
  | inl _ =>
      rfl
  | inr j =>
      by_cases hji : j = i
      · subst j
        simp [TimeVelocityMultiIndex.ofTimeVelocity, TimeVelocityMultiIndex.velocity,
          velocityCoord]
      · simp [TimeVelocityMultiIndex.ofTimeVelocity, TimeVelocityMultiIndex.velocity,
          velocityCoord, hji]

/-- Every selected ordinary derivative of the one mollified zero
representative is the mollification of the corresponding selected entry. -/
theorem coordinateIteratedFDeriv_spacetimeMollification_ordinaryRepresentative
     (hε : 0 < ε)
    (beta : TimeVelocityDerivativeIndex d m) :
    TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
        (SpacetimeMollifier.spacetimeMollification ε
          (G.ordinaryRepresentative
            (TimeVelocityDerivativeIndex.zero d m))) =
      SpacetimeMollifier.spacetimeMollification ε
        (G.ordinaryRepresentative beta) := by
  let f := SpacetimeMollifier.spacetimeMollification ε
    (G.ordinaryRepresentative (TimeVelocityDerivativeIndex.zero d m))
  have hf : ContDiff ℝ _ f :=
    SpacetimeMollifier.contDiff_spacetimeMollification hε _
      (by
        exact (ordinaryRepresentative_memLp_volume G
          _).locallyIntegrable (by norm_num))
  generalize hn : beta.1.order = n
  induction n using Nat.strong_induction_on generalizing beta with
  | h n ih =>
      rcases TimeVelocityDerivativeIndex.eq_zero_or_eq_timeSucc_or_eq_velocitySucc beta with
        hzero | htime | hvelocity
      · subst beta
        funext z
        exact TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero f z
      · rcases htime with ⟨gamma, hgamma, rfl⟩
        have hlt : gamma.1.order <
            (TimeVelocityDerivativeIndex.timeSucc gamma hgamma).1.order := by
          rw [ordinary_timeSucc_eq_add_single]
          simp
        have hind := ih gamma.1.order (hn ▸ hlt) gamma rfl
        rw [ordinary_timeSucc_eq_add_single]
        funext z
        calc
          TimeVelocityMultiIndex.coordinateIteratedFDeriv
              _ f z =
              timeDerivative
                _ z := by
            rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single]
            · rfl
            · exact contDiff_infty.mp hf _
          _ = timeDerivative
              _ z := by rw [hind]
          _ = SpacetimeMollifier.spacetimeMollification ε
              _ z := by
            exact congrFun
              (SpacetimeMollifier.timeDerivative_spacetimeMollification hε
            _
            _
            (by
              exact (ordinaryRepresentative_memLp_volume G gamma).locallyIntegrable
                (by norm_num))
            (by
              exact (ordinaryRepresentative_memLp_volume G
                _).locallyIntegrable
                  (by norm_num))
            (G.hasWeakTimeDerivOn_ordinaryRepresentative_timeSucc gamma hgamma)) z
      · rcases hvelocity with ⟨i, gamma, hgamma, rfl⟩
        have hlt : gamma.1.order <
            (TimeVelocityDerivativeIndex.velocitySucc gamma i hgamma).1.order := by
          rw [ordinary_velocitySucc_eq_add_single]
          simp
        have hind := ih gamma.1.order (hn ▸ hlt) gamma rfl
        rw [ordinary_velocitySucc_eq_add_single]
        funext z
        calc
          TimeVelocityMultiIndex.coordinateIteratedFDeriv
              _ f z =
              velocityGradient
                _ z i := by
            rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single]
            · rfl
            · exact contDiff_infty.mp hf _
          _ = velocityGradient
              _ z i := by rw [hind]
          _ = SpacetimeMollifier.spacetimeMollification ε
              _ z := by
            exact congrFun
              (SpacetimeMollifier.velocityGradient_spacetimeMollification hε i
            _
            _
            (by
              exact (ordinaryRepresentative_memLp_volume G gamma).locallyIntegrable
                (by norm_num))
            (by
              exact (ordinaryRepresentative_memLp_volume G
                _).locallyIntegrable
                  (by norm_num))
            (G.hasWeakVelocityPartialDerivOn_ordinaryRepresentative_velocitySucc
              gamma i hgamma)) z

/-- The common mollified zero representative is globally smooth. -/
theorem contDiff_spacetimeMollification_ordinaryRepresentative_zero
     (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞)
      (SpacetimeMollifier.spacetimeMollification ε
        (G.ordinaryRepresentative
          (TimeVelocityDerivativeIndex.zero d m))) := SpacetimeMollifier.contDiff_spacetimeMollification hε _
    (by
      exact (ordinaryRepresentative_memLp_volume G
        _).locallyIntegrable (by norm_num))

/-- Each mollified selected ordinary entry converges strongly in ambient `L²`. -/
theorem tendsto_eLpNorm_spacetimeMollification_ordinaryRepresentative_sub
     :
    Filter.Tendsto
      (fun ε : ℝ ↦
        eLpNorm
          (SpacetimeMollifier.spacetimeMollification ε
              (G.ordinaryRepresentative beta) -
            G.ordinaryRepresentative beta)
          (2 : ℝ≥0∞)
          (volume : Measure (TimeVelocity d)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub
    _ (ordinaryRepresentative_memLp_volume G beta)

end ParabolicWeakDerivativeFamily

end HypoellipticAleksandrov.Parabolic
