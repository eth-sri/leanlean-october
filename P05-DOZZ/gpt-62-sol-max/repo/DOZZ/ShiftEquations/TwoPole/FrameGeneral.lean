/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.TwoPole.Frame
public import DOZZ.Statements.Correlations.UnitVolumeNPointCorrelation
import DOZZ.GMC.Moments.RhoCoulomb

/-!
# The structure constant in a finite frame

For arbitrary charges the inversion–translation–inversion chain of `Frame` gives
`E[I_{(0,2,-2)}^{q}] = 2^{-γ(α₂+α₃) q} E[ρ(α₁, α₂, α₃)^{q}]` with `q = -s`, so the unit-volume
structure constant in the frame `(0, 1, ∞)` is an explicit positive multiple of the finite-position
unit-volume moment at `(0, 2, -2)`:
`C̄(α₁, α₂, α₃) = 2^{γ(α₂+α₃)(-s)} / C(α, z) · C̄_{(0,2,-2)}(α)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ : ℝ)
include Ω X hX hγ hγ2 hM

/-- **The structure constant through a finite frame.** -/
theorem unitVolumeStructureConstant_eq_nPoint :
    unitVolumeStructureConstant P M γ α₁ α₂ α₃ =
      2 ^ (γ * (α₂ + α₃) * (-sExp γ α₁ α₂ α₃)) /
          nPointCoulombPrefactor ![α₁, α₂, α₃] ![0, 2, -2] *
        unitVolumeNPointCorrelation P M γ ![α₁, α₂, α₃] ![0, 2, -2] := by
  have hpref : 0 < nPointCoulombPrefactor ![α₁, α₂, α₃] ![0, 2, -2] := by
    unfold nPointCoulombPrefactor
    refine Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => ?_
    split_ifs with hij
    · refine Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr ?_)) _
      fin_cases i <;> fin_cases j
      all_goals first | (simp_all; done) | (simp_all; norm_num)
    · exact one_pos
  have hs : nPointSExp γ ![α₁, α₂, α₃] = sExp γ α₁ α₂ α₃ := by
    unfold nPointSExp sExp
    rw [Fin.sum_univ_three]
    simp
  have hframe := lintegral_coulombMass_frame_eq_rho P X hX γ hγ hγ2 M hM α₁ α₂ α₃
  have hrho : ∫⁻ ω, rho γ (M ω) α₁ α₂ α₃ ^ (-sExp γ α₁ α₂ α₃) ∂P =
      ENNReal.ofReal (2 ^ (γ * (α₂ + α₃) * (-sExp γ α₁ α₂ α₃))) *
        ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![α₁, α₂, α₃] ![0, 2, -2] 0)
          (-sExp γ α₁ α₂ α₃) ∂P := by
    rw [hframe, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add two_pos,
      add_neg_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
  unfold unitVolumeStructureConstant unitVolumeNPointCorrelation
  rw [hs, hrho, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  field_simp

end

end DOZZ.Proofs

end
