module

public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyLocality
public import HypoellipticAleksandrov.Analysis.FiniteSumL2Norm

/-!
# Squared L2 energy of a finite parabolic weak-derivative family
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily

open MeasureTheory
open HypoellipticAleksandrov.Analysis
open scoped BigOperators ENNReal

/-- The finite sum of squared restricted `L²` norms of all selected
derivatives. -/
noncomputable def squaredL2Norm
    {d L : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (F : ParabolicWeakDerivativeFamily d L U u) : ℝ :=
  ∑ beta : ParabolicDerivativeIndex d L,
    squaredL2Seminorm (timeVelocityVolumeOn U) (F.representative beta)

section
variable {d L : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
  (F : ParabolicWeakDerivativeFamily d L U u)

/-- The squared finite-family `L²` norm is nonnegative. -/
theorem squaredL2Norm_nonneg :
    0 ≤ squaredL2Norm F := Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Each squared component norm is bounded by the squared finite-family
norm. -/
theorem component_sq_le_squaredL2Norm
    (beta : ParabolicDerivativeIndex d L) :
    squaredL2Seminorm (timeVelocityVolumeOn U) (F.representative beta) ≤
      squaredL2Norm F := by
  exact Finset.single_le_sum (fun gamma _ => squaredL2Seminorm_nonneg _ (F.representative gamma))
    (Finset.mem_univ beta)

/-- The literal representative formula agrees with the squared norm of any
`L²` quotient built from any proof certificate. -/
theorem component_sq_eq_norm_toLp_sq
    (beta : ParabolicDerivativeIndex d L)
    (h : ParabolicMemLpOn U 2 (F.representative beta)) :
    squaredL2Seminorm (timeVelocityVolumeOn U) (F.representative beta) =
      ‖h.toLp (F.representative beta)‖ ^ 2 := by
  rw [Lp.norm_toLp]

end

/-- The literal finite-family formula agrees with the sum of the squared
`Lp` norms obtained from the family's stored membership certificates. -/
theorem squaredL2Norm_eq_sum_norm_toLp_sq
    {d L : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (F : ParabolicWeakDerivativeFamily d L U u) :
    squaredL2Norm F =
      ∑ beta : ParabolicDerivativeIndex d L,
        ‖(F.memLp beta).toLp (F.representative beta)‖ ^ 2 := by
  unfold squaredL2Norm
  apply Finset.sum_congr rfl
  intro beta _
  exact component_sq_eq_norm_toLp_sq F beta (F.memLp beta)

/-- Restricting a family to a smaller raw carrier cannot increase its
squared finite-family `L²` norm. -/
theorem squaredL2Norm_restrict_le
    {d L : ℕ} {U V : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (F : ParabolicWeakDerivativeFamily d L U u) (hVU : V ⊆ U) :
    squaredL2Norm (F.restrict hVU) ≤ squaredL2Norm F := by
  exact Finset.sum_le_sum fun beta _ => squaredL2Seminorm_mono_measure (F.memLp beta)
    (Measure.restrict_mono_set volume hVU)

end HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
