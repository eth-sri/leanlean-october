module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareSpatial
public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareTime
import HypoellipticAleksandrov.Parabolic.ParabolicMorreyReferenceCollarCutoff

/-!
# Smooth normalized parabolic Poincare estimate

This module assembles the spatial and temporal unit-box estimates into the
second-order parabolic Poincare inequality modulo the canonical affine moment
projection.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators ENNReal

/-- Smooth normalized second-order parabolic Poincare inequality modulo the
canonical time-independent velocity-affine moment projection. -/
theorem exists_parabolicMorreyUnitAffinePoincareConst (d : Nat)
    (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ u : TimeVelocity d -> Real,
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
  obtain ⟨Cs, hCs, hs⟩ := exists_parabolicMorreyUnitSpatialAffinePoincareELpConst d hd
  let Ct : ℝ := 1 + 3 * (d : ℝ)
  have hCt : 0 < Ct := by dsimp [Ct]; positivity
  refine ⟨Cs + Ct, add_pos hCs hCt, fun u hu => ?_⟩
  let S := fun z => u z - parabolicMorreyUnitSpatialAffineProjection u z
  let D := fun z => parabolicMorreyUnitSpatialAffineProjection u z - parabolicMorreyUnitAffineProjection u z
  let N := fun f : TimeVelocity d → ℝ => parabolicELpNormOn d f (parabolicMorreyUnitBox d)
  let T := N (timeDerivative u)
  let H := fun i j => N (fun z => velocityHessian u z i j)
  have ht : T ≠ ⊤ :=
    (Continuous.memLp_parabolicMorreyUnitBox (timeDerivative_cutoff_continuous hu)).eLpNorm_ne_top
  have hh (i j : Fin d) : H i j ≠ ⊤ :=
    (Continuous.memLp_parabolicMorreyUnitBox (velocityHessian_cutoff_continuous (i := i) (j := j) hu)).eLpNorm_ne_top
  have hh' (i : Fin d) : (∑ j, H i j) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun j _ => hh i j
  have hp : (1 : ENNReal) ≤ parabolicExponent d := by simp [parabolicExponent]
  have hdecomp : (fun z => u z - parabolicMorreyUnitAffineProjection u z) = S + D := by
    ext z
    simp [S, D, sub_add_sub_cancel]
  have hb : N (S + D) ≤ ENNReal.ofReal (Cs + Ct) * (T + ∑ i, ∑ j, H i j) := by
    calc
      N (S + D) ≤ N S + N D := MeasureTheory.eLpNorm_add_le hp
      _ ≤ ENNReal.ofReal Cs * (∑ i, ∑ j, H i j) + ENNReal.ofReal Ct * T :=
        add_le_add (hs u hu) (parabolicMorreyUnitTemporalAffinePoincareELpNorm_le d u hu)
      _ ≤ _ := by
        rw [add_comm T, mul_add]
        gcongr <;> linarith
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.add_ne_top.mpr ⟨ht, ENNReal.sum_ne_top.mpr fun i _ => hh' i⟩)) hb
  rw [ENNReal.toReal_ofReal_mul _ _ (add_nonneg hCs.le hCt.le),
    ENNReal.toReal_add ht (ENNReal.sum_ne_top.mpr fun i _ => hh' i),
    ENNReal.toReal_sum (fun i _ => hh' i)] at h
  simp_rw [ENNReal.toReal_sum (fun j _ => hh _ j)] at h
  rw [hdecomp]
  exact h

end HypoellipticAleksandrov.Parabolic
