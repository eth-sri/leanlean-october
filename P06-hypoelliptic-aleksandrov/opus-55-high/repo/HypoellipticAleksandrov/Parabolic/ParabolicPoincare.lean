module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareSpatial
public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareTime

/-!
# Smooth normalized parabolic Poincare estimate

This module assembles the spatial and temporal unit-box estimates into the
second-order parabolic Poincare inequality modulo the canonical affine moment
projection.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators ENNReal

variable {d : Nat} {u : TimeVelocity d -> Real}

private theorem continuous_timeDerivative_local
     (hu : ContDiff Real 2 u) :
    Continuous (timeDerivative u) := ((hu.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).continuous

private theorem continuous_velocityHessian_local
     (hu : ContDiff Real 2 u) :
    Continuous (velocityHessian u) := by
  apply continuous_matrix
  intro i j
  have hdu : ContDiff Real 1 (fderiv Real u) :=
    hu.fderiv_right (m := 1) (by norm_num)
  exact (((hdu.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const).continuous

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
  obtain ⟨Cs, hCsPos, hCs⟩ :=
    exists_parabolicMorreyUnitSpatialAffinePoincareConst d hd
  obtain ⟨CsENN, _hCsENNPos, hCsENN⟩ :=
    exists_parabolicMorreyUnitSpatialAffinePoincareELpConst d hd
  let Ct  := 1 + 3 * (d : Real)
  refine ⟨Cs + Ct, ?_, ?_⟩
  · positivity
  · intro u hu
    let S : TimeVelocity d -> Real := fun z =>
      u z - parabolicMorreyUnitSpatialAffineProjection u z
    let D : TimeVelocity d -> Real := fun z =>
      parabolicMorreyUnitSpatialAffineProjection u z -
        parabolicMorreyUnitAffineProjection u z
    let T : ENNReal :=
      parabolicELpNormOn d (timeDerivative u) (parabolicMorreyUnitBox d)
    let H : ENNReal := ∑ i : Fin d, ∑ j : Fin d,
      parabolicELpNormOn d (fun z => velocityHessian u z i j)
        (parabolicMorreyUnitBox d)
    have hTfin : T ≠ ⊤ := (Continuous.memLp_parabolicMorreyUnitBox
        (continuous_timeDerivative_local hu)).eLpNorm_ne_top
    have hHijfin (i : Fin d) (j : Fin d) :
        parabolicELpNormOn d (fun z => velocityHessian u z i j)
          (parabolicMorreyUnitBox d) ≠ ⊤ := (Continuous.memLp_parabolicMorreyUnitBox
        ((continuous_pi_iff.mp (continuous_pi_iff.mp
          (continuous_velocityHessian_local hu) i)) j)).eLpNorm_ne_top
    have hHfin : H ≠ ⊤ := by
      aesop
    have hSENN : parabolicELpNormOn d S (parabolicMorreyUnitBox d) <=
        ENNReal.ofReal CsENN * H := by
      grind
    have hSfin : parabolicELpNormOn d S (parabolicMorreyUnitBox d) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hHfin) hSENN
    have hDENN : parabolicELpNormOn d D (parabolicMorreyUnitBox d) <=
        ENNReal.ofReal Ct * T := by
      simpa only [D, T, Ct] using
        parabolicMorreyUnitTemporalAffinePoincareELpNorm_le d u hu
    have hDfin : parabolicELpNormOn d D (parabolicMorreyUnitBox d) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTfin) hDENN
    have hp : (1 : ENNReal) <= parabolicExponent d := by
      simpa only [parabolicExponent] using
        (le_add_of_nonneg_left (show (0 : ENNReal) <= d from bot_le))
    have hdecomp :
        (fun z => u z - parabolicMorreyUnitAffineProjection u z) = S + D := by
      aesop
    have htriangle : parabolicELpNormOn d (S + D) (parabolicMorreyUnitBox d) <=
        parabolicELpNormOn d S (parabolicMorreyUnitBox d) +
          parabolicELpNormOn d D (parabolicMorreyUnitBox d) := MeasureTheory.eLpNorm_add_le hp
    have hSDfin : parabolicELpNormOn d S (parabolicMorreyUnitBox d) +
        parabolicELpNormOn d D (parabolicMorreyUnitBox d) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hSfin, hDfin⟩
    have hRealTriangle :
        (parabolicELpNormOn d
          (fun z => u z - parabolicMorreyUnitAffineProjection u z)
          (parabolicMorreyUnitBox d)).toReal <=
          (parabolicELpNormOn d S (parabolicMorreyUnitBox d)).toReal +
            (parabolicELpNormOn d D (parabolicMorreyUnitBox d)).toReal := by
      rw [hdecomp]
      have h := ENNReal.toReal_mono hSDfin htriangle
      rw [ENNReal.toReal_add hSfin hDfin] at h
      exact h
    have hSReal : (parabolicELpNormOn d S (parabolicMorreyUnitBox d)).toReal <=
        Cs * ∑ i : Fin d, ∑ j : Fin d,
          (parabolicELpNormOn d (fun z => velocityHessian u z i j)
            (parabolicMorreyUnitBox d)).toReal := by
      aesop
    have hDReal : (parabolicELpNormOn d D (parabolicMorreyUnitBox d)).toReal <=
        Ct * (parabolicELpNormOn d (timeDerivative u)
          (parabolicMorreyUnitBox d)).toReal := by
      simpa only [D, Ct, parabolicLpNormOn] using
        parabolicMorreyUnitTemporalAffinePoincareLpNorm_le d u hu
    have hTnonneg : 0 <= (parabolicELpNormOn d (timeDerivative u)
        (parabolicMorreyUnitBox d)).toReal := ENNReal.toReal_nonneg
    have hHnonneg : 0 <= H.toReal := ENNReal.toReal_nonneg
    have hCtNonneg : 0 <= Ct := by
      positivity
    unfold parabolicLpNormOn
    have hHtoReal : H.toReal = ∑ i : Fin d, ∑ j : Fin d,
        (parabolicELpNormOn d (fun z => velocityHessian u z i j)
          (parabolicMorreyUnitBox d)).toReal := by
      rw [ENNReal.toReal_sum fun i _ =>
        ENNReal.sum_ne_top.mpr fun j _ => hHijfin i j]
      apply Finset.sum_congr rfl
      intro i _
      exact ENNReal.toReal_sum fun j _ => hHijfin i j
    rw [← hHtoReal] at hSReal
    rw [← hHtoReal]
    calc
      (parabolicELpNormOn d
        _
        _).toReal <=
          (parabolicELpNormOn d S _).toReal +
            (parabolicELpNormOn d D _).toReal := hRealTriangle
      _ <= Cs * H.toReal + Ct * T.toReal := add_le_add hSReal hDReal
      _ <= (Cs + Ct) * (T.toReal + H.toReal) := by
        nlinarith [hCsPos.le]

end HypoellipticAleksandrov.Parabolic
