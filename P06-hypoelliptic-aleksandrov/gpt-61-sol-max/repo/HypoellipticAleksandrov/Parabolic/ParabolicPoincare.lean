module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareSpatial
public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareTime
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import HypoellipticAleksandrov.Parabolic.ContactMap
import Lean.Elab.Tactic.SolveByElim
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import all HypoellipticAleksandrov.Parabolic.ParabolicPoincareTime

open private HypoellipticAleksandrov.Parabolic.continuous_parabolicMorreyUnitAffineProjection from HypoellipticAleksandrov.Parabolic.ParabolicPoincareTime


/-!
# Smooth normalized parabolic Poincare estimate

This module assembles the spatial and temporal unit-box estimates into the
second-order parabolic Poincare inequality modulo the canonical affine moment
projection.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators

variable {d : Nat}

variable {u : HypoellipticAleksandrov.Parabolic.ScalarField d}

private theorem continuous_timeDerivative_local
      (hu : ContDiff Real 2 u) :
    Continuous (timeDerivative u) := (continuous_timeDerivative hu)


private theorem continuous_velocityHessian_local
      (hu : ContDiff Real 2 u) :
    Continuous (velocityHessian u) := (continuous_velocityHessian hu)

private theorem stronglyMeasurable_parabolicMorreyUnitSpatialAffineProjection
      (hu : Continuous u) :
    StronglyMeasurable (parabolicMorreyUnitSpatialAffineProjection u) := by
  let V  := velocityCube (0 : PDE.Vec d) 1
  let ν : Measure (PDE.Vec d) := volume.restrict V
  have huStrong : StronglyMeasurable
      (Function.uncurry fun t  => fun v : PDE.Vec d => u (t, v)) := by
    change StronglyMeasurable u
    exact hu.stronglyMeasurable
  have hAverage : StronglyMeasurable (parabolicMorreyUnitVelocityAverage u) := by
    unfold parabolicMorreyUnitVelocityAverage
    apply stronglyMeasurable_const.mul
    simpa only [ν, V] using (huStrong.integral_prod_right (ν := ν))
  have hCoeff : ∀ i : Fin d,
      StronglyMeasurable (fun t => parabolicMorreyUnitVelocityCoeffAt u t i) := by
    intro i
    have huCoordinate : StronglyMeasurable
        (Function.uncurry fun t  => fun v : PDE.Vec d => u (t, v) * v i) := by
      change StronglyMeasurable (fun z  => u z * z.2 i)
      exact (hu.mul ((continuous_apply i).comp continuous_snd)).stronglyMeasurable
    unfold parabolicMorreyUnitVelocityCoeffAt
    apply stronglyMeasurable_const.mul
    simpa only [ν, V] using (huCoordinate.integral_prod_right (ν := ν))
  unfold parabolicMorreyUnitSpatialAffineProjection
  apply (hAverage.comp_measurable measurable_fst).add
  rw [← Finset.sum_fn]
  refine Finset.stronglyMeasurable_sum Finset.univ fun i _ => ?_
  exact ((hCoeff i).comp_measurable measurable_fst).mul
    (((continuous_apply i).comp continuous_snd).stronglyMeasurable)




/-- Smooth normalized second-order parabolic Poincare inequality modulo the
canonical time-independent velocity-affine moment projection. -/
theorem exists_parabolicMorreyUnitAffinePoincareConst (d : Nat)
    (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ u : HypoellipticAleksandrov.Parabolic.ScalarField d,
        ContDiff Real 2 u ->
        parabolicLpNormOn d
            (fun z => u z - parabolicMorreyUnitAffineProjection u z)
            (parabolicMorreyUnitBox d) <=
          C *
            (parabolicLpNormOn d (timeDerivative u)
                (parabolicMorreyUnitBox d) +
              ∑ i : Fin d, ∑ j : Fin d,
                parabolicLpNormOn d
                  (fun z => velocityHessian u z i j)
                  (parabolicMorreyUnitBox d)) := by
  obtain ⟨Cs, hCsPos, hCs⟩ :=
    exists_parabolicMorreyUnitSpatialAffinePoincareConst d hd
  obtain ⟨CsENN, _hCsENNPos, hCsENN⟩ :=
    exists_parabolicMorreyUnitSpatialAffinePoincareELpConst d hd
  let Ct : Real := 1 + 3 * (d : Real)
  refine ⟨Cs + Ct, ?_, ?_⟩
  · positivity
  · intro u hu
    let S  := fun z =>
      u z - parabolicMorreyUnitSpatialAffineProjection u z
    let D  := fun z =>
      parabolicMorreyUnitSpatialAffineProjection u z -
        parabolicMorreyUnitAffineProjection u z
    let T  :=
      parabolicELpNormOn d (timeDerivative u) (parabolicMorreyUnitBox d)
    let H  := ∑ i : Fin d, ∑ j : Fin d,
      parabolicELpNormOn d (fun z => velocityHessian u z i j)
        (parabolicMorreyUnitBox d)

    have hHijfin (i : Fin d) (j : Fin d) :
        parabolicELpNormOn d (fun z => velocityHessian u z i j)
          (parabolicMorreyUnitBox d) ≠ ⊤ := (Continuous.memLp_parabolicMorreyUnitBox
        ((continuous_pi_iff.mp (continuous_pi_iff.mp
          (continuous_velocityHessian_local hu) i)) j)).eLpNorm_ne_top


    have hSfin : parabolicELpNormOn d S (parabolicMorreyUnitBox d) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (show H ≠ ⊤ by
          dsimp only [H]
          refine ENNReal.sum_ne_top.mpr fun i _ => ?_
          exact ENNReal.sum_ne_top.mpr fun j _ => hHijfin i j)) (hCsENN u hu)

    have hDfin : parabolicELpNormOn d D (parabolicMorreyUnitBox d) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (show T ≠ ⊤ by
          dsimp only [T]
          exact (Continuous.memLp_parabolicMorreyUnitBox
            (continuous_timeDerivative_local hu)).eLpNorm_ne_top)) (parabolicMorreyUnitTemporalAffinePoincareELpNorm_le d u hu)




    have hdecomp :
        (fun z => u z - parabolicMorreyUnitAffineProjection u z) = S + D := by
      funext z
      dsimp only [S, D, Pi.add_apply]
      ring



    have hSReal : (parabolicELpNormOn d S (parabolicMorreyUnitBox d)).toReal <=
        Cs * ∑ i : Fin d, ∑ j : Fin d,
          (parabolicELpNormOn d (fun z => velocityHessian u z i j)
            (parabolicMorreyUnitBox d)).toReal := by
      exact hCs u hu
    have hDReal : (parabolicELpNormOn d D (parabolicMorreyUnitBox d)).toReal <=
        Ct * (parabolicELpNormOn d (timeDerivative u)
          (parabolicMorreyUnitBox d)).toReal := by
      exact parabolicMorreyUnitTemporalAffinePoincareLpNorm_le d u hu
    have hTnonneg : 0 <= (parabolicELpNormOn d (timeDerivative u)
        (parabolicMorreyUnitBox d)).toReal := ENNReal.toReal_nonneg
    have hHnonneg : 0 <= H.toReal := ENNReal.toReal_nonneg
    have hCtNonneg : 0 <= Ct := by
      dsimp only [Ct]
      positivity
    unfold parabolicLpNormOn
    have hHtoReal : H.toReal = ∑ i : Fin d, ∑ j : Fin d,
        (parabolicELpNormOn d (fun z => velocityHessian u z i j)
          (parabolicMorreyUnitBox d)).toReal := by
      dsimp only [H]
      rw [ENNReal.toReal_sum fun i _ =>
        ENNReal.sum_ne_top.mpr fun j _ => hHijfin i j]
      apply Finset.sum_congr rfl
      intro i _
      exact ENNReal.toReal_sum fun j _ => hHijfin i j
    rw [← hHtoReal] at hSReal
    rw [← hHtoReal]
    calc
      (parabolicELpNormOn d
        (fun z => u z - parabolicMorreyUnitAffineProjection u z)
        (parabolicMorreyUnitBox d)).toReal <=
          (parabolicELpNormOn d S (parabolicMorreyUnitBox d)).toReal +
            (parabolicELpNormOn d D (parabolicMorreyUnitBox d)).toReal := (by
                rw [hdecomp]
                have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hSfin, hDfin⟩) (MeasureTheory.eLpNorm_add_le (by
                        simpa only [parabolicExponent] using
                          (le_add_of_nonneg_left (show (0 : ENNReal) <= d from bot_le))))
                rw [ENNReal.toReal_add hSfin hDfin] at h
                exact h)
      _ <= Cs * H.toReal + Ct * T.toReal := by
        linarith
      _ <= (Cs + Ct) * (T.toReal + H.toReal) := by
        let sharedTerm_6231907d94 := ((parabolicELpNormOn d (timeDerivative u) (parabolicMorreyUnitBox d)).toReal)
        change Cs * H.toReal + Ct *
          sharedTerm_6231907d94 <=
            (Cs + Ct) *
              (sharedTerm_6231907d94 + H.toReal)
        nlinarith [hCsPos.le]

end HypoellipticAleksandrov.Parabolic
