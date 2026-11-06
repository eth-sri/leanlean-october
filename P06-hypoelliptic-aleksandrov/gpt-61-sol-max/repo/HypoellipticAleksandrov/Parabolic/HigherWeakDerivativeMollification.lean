module

public import HypoellipticAleksandrov.Parabolic.OrdinaryDerivativeIndexPredecessor
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
import Mathlib.Tactic.Bound
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder





/-!
# Higher weak derivatives and spacetime mollification

This file identifies every selected ordinary derivative of one mollified zero
representative with the mollification of the corresponding selected weak
derivative.  It also records smoothness of that common approximant and strong
`L²` convergence of each selected entry.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal Topology

namespace ParabolicWeakDerivativeFamily

variable {d m : ℕ}

private theorem ordinaryRepresentative_memLp_volume
     {root : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (G : ParabolicWeakDerivativeFamily d (2 * m) Set.univ root)
    (beta : TimeVelocityDerivativeIndex d m) :
    MemLp (G.ordinaryRepresentative beta) (2 )
       := by
  have h := G.ordinaryRepresentative_memLp beta
  change MemLp (G.ordinaryRepresentative beta) (2 )
    ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d).restrict Set.univ) at h
  simpa only [Measure.restrict_univ] using h

variable (gamma : TimeVelocityDerivativeIndex d m)

private theorem ordinary_timeSucc_eq_add_single

    (h : gamma.1.order + 1 ≤ m) :
    (TimeVelocityDerivativeIndex.timeSucc gamma h).1 =
      gamma.1 + Pi.single (timeCoord d) 1 := by
  bound

private theorem ordinary_velocitySucc_eq_add_single
      (i : Fin d)
    (h : gamma.1.order + 1 ≤ m) :
    (TimeVelocityDerivativeIndex.velocitySucc gamma i h).1 =
      gamma.1 + Pi.single (velocityCoord i) 1 := by
  ext c
  cases c with
  | inl _ =>
      change gamma.1 (Sum.inl ()) = gamma.1 (Sum.inl ())
      rfl
  | inr j =>
      by_cases hji : j = i
      · simp_all [TimeVelocityDerivativeIndex.velocitySucc, TimeVelocityMultiIndex.ofTimeVelocity, TimeVelocityMultiIndex.velocity, velocityCoord]
      · simp_all [TimeVelocityDerivativeIndex.velocitySucc, TimeVelocityMultiIndex.ofTimeVelocity, TimeVelocityMultiIndex.velocity, velocityCoord]

variable {root : HypoellipticAleksandrov.Parabolic.ScalarField d} (G : ParabolicWeakDerivativeFamily d (2 * m) Set.univ root)

section
variable (ε : ℝ) (hε : 0 < ε)

include hε
/-- Every selected ordinary derivative of the one mollified zero
representative is the mollification of the corresponding selected entry. -/
theorem coordinateIteratedFDeriv_spacetimeMollification_ordinaryRepresentative


    (beta : TimeVelocityDerivativeIndex d m) :
    TimeVelocityMultiIndex.coordinateIteratedFDeriv beta.1
        (SpacetimeMollifier.spacetimeMollification ε
          (G.ordinaryRepresentative
            (TimeVelocityDerivativeIndex.zero d m))) =
      SpacetimeMollifier.spacetimeMollification ε
        (G.ordinaryRepresentative beta) := by
  let f := SpacetimeMollifier.spacetimeMollification ε
    (G.ordinaryRepresentative (TimeVelocityDerivativeIndex.zero d m))
  have hf : ContDiff ℝ PDE.smoothOrder f :=
    SpacetimeMollifier.contDiff_spacetimeMollification hε _
      ((ordinaryRepresentative_memLp_volume G
          (TimeVelocityDerivativeIndex.zero d m)).locallyIntegrable (by norm_num))
  generalize hn : beta.1.order = n
  induction n using Nat.strong_induction_on generalizing beta with
  | h n ih =>
      rcases TimeVelocityDerivativeIndex.eq_zero_or_eq_timeSucc_or_eq_velocitySucc beta with
        hzero | htime | hvelocity
      · subst beta
        funext z
        exact TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero f z
      · rcases htime with ⟨gamma, hgamma, rfl⟩

        have hind := ih gamma.1.order (hn ▸ (by
            rw [ordinary_timeSucc_eq_add_single]
            simp only [TimeVelocityMultiIndex.order_add,
              TimeVelocityMultiIndex.order_single]
            omega)) gamma rfl
        rw [ordinary_timeSucc_eq_add_single]
        funext z
        calc
          TimeVelocityMultiIndex.coordinateIteratedFDeriv
              (gamma.1 + Pi.single (timeCoord d) 1) f z =
              timeDerivative
                (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.1 f) z := by
            rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single]
            · rfl
            · exact contDiff_infty.mp hf _
          _ = timeDerivative
              (SpacetimeMollifier.spacetimeMollification ε
                (G.ordinaryRepresentative gamma)) z := by rw [hind]
          _ = SpacetimeMollifier.spacetimeMollification ε
              (G.ordinaryRepresentative
                (TimeVelocityDerivativeIndex.timeSucc gamma hgamma)) z := congrFun
              (SpacetimeMollifier.timeDerivative_spacetimeMollification hε
            (G.ordinaryRepresentative gamma)
            (G.ordinaryRepresentative
              (TimeVelocityDerivativeIndex.timeSucc gamma hgamma))
            ((ordinaryRepresentative_memLp_volume G gamma).locallyIntegrable
                (by norm_num))
            ((ordinaryRepresentative_memLp_volume G
                (TimeVelocityDerivativeIndex.timeSucc gamma hgamma)).locallyIntegrable
                  (by norm_num))
            (G.hasWeakTimeDerivOn_ordinaryRepresentative_timeSucc gamma hgamma)) z
      · rcases hvelocity with ⟨i, gamma, hgamma, rfl⟩

        have hind := ih gamma.1.order (hn ▸ (by
            rw [ordinary_velocitySucc_eq_add_single]
            simp only [TimeVelocityMultiIndex.order_add,
              TimeVelocityMultiIndex.order_single]
            omega)) gamma rfl
        rw [ordinary_velocitySucc_eq_add_single]
        funext z
        calc
          TimeVelocityMultiIndex.coordinateIteratedFDeriv
              (gamma.1 + Pi.single (velocityCoord i) 1) f z =
              velocityGradient
                (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma.1 f) z i := by
            rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single]
            · rfl
            · exact contDiff_infty.mp hf _
          _ = velocityGradient
              (SpacetimeMollifier.spacetimeMollification ε
                (G.ordinaryRepresentative gamma)) z i := by rw [hind]
          _ = SpacetimeMollifier.spacetimeMollification ε
              (G.ordinaryRepresentative
                (TimeVelocityDerivativeIndex.velocitySucc gamma i hgamma)) z := congrFun
              (SpacetimeMollifier.velocityGradient_spacetimeMollification hε i
            (G.ordinaryRepresentative gamma)
            (G.ordinaryRepresentative
              (TimeVelocityDerivativeIndex.velocitySucc gamma i hgamma))
            ((ordinaryRepresentative_memLp_volume G gamma).locallyIntegrable
                (by norm_num))
            ((ordinaryRepresentative_memLp_volume G
                (TimeVelocityDerivativeIndex.velocitySucc gamma i hgamma)).locallyIntegrable
                  (by norm_num))
            (G.hasWeakVelocityPartialDerivOn_ordinaryRepresentative_velocitySucc
              gamma i hgamma)) z

/-- The common mollified zero representative is globally smooth. -/
theorem contDiff_spacetimeMollification_ordinaryRepresentative_zero

     :
    ContDiff ℝ PDE.smoothOrder
      (SpacetimeMollifier.spacetimeMollification ε
        (G.ordinaryRepresentative
          (TimeVelocityDerivativeIndex.zero d m))) := SpacetimeMollifier.contDiff_spacetimeMollification hε _
    ((ordinaryRepresentative_memLp_volume G
        (TimeVelocityDerivativeIndex.zero d m)).locallyIntegrable (by norm_num))
end


/-- Each mollified selected ordinary entry converges strongly in ambient `L²`. -/
theorem tendsto_eLpNorm_spacetimeMollification_ordinaryRepresentative_sub

    (beta : TimeVelocityDerivativeIndex d m) :
    Filter.Tendsto
      (fun ε  ↦
        eLpNorm
          (SpacetimeMollifier.spacetimeMollification ε
              (G.ordinaryRepresentative beta) -
            G.ordinaryRepresentative beta)
          (2 )
          )
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub
    _ (ordinaryRepresentative_memLp_volume G beta)

end ParabolicWeakDerivativeFamily

end HypoellipticAleksandrov.Parabolic
