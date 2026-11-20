module

public import QPBT.Combining.Witnesses
public import QPBT.Combining.Points.Placement

/-!
# Positivity of the consistency defect on opposite placements

The error-inflation estimates for restricted line distributions apply to
nonnegative averages.  This module supplies the missing nonnegativity: the
integrand of `consistencyDefect` for two complete measurements placed on
opposite registers is a state quadratic form of a positive operator.  Indeed,
after separating the two placements along the corresponding tensor
bipartition, the off-diagonal sum is
`∑_a (place p₁ E_a) (place p₂ (∑_{b ≠ a} F_b))`, a sum of products of
positive operators supported on complementary registers.  The placement
algebra itself — additivity, the image of zero, positivity and the commutation
of opposite placements — is supplied by the placement identities proved in
`MIPStarRE.QPBT.Combining.Points.PlacementSupport` and
`MIPStarRE.QPBT.Observables.LineMeasurement.LinePointOverlap`.

## References

The consistency defect is blueprint `def:consistency`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248`.  The
placements and their bipartitions are blueprint `def:expanded-state`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`.  The
nonnegativity is the hypothesis of items 1 and 2 of
blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1058`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- Positive operators placed on a directed opposite pair of registers have a
positive product.  Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-450`,
blueprint `def:expanded-state`. -/
theorem place_mul_place_nonneg (S : ProjectiveSetting P ε)
    (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂)
    {X : Op (S.ExpandedLocalSpace p₁.side)}
    {Y : Op (S.ExpandedLocalSpace p₂.side)}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ S.place p₁ X * S.place p₂ Y := by
  exact Commute.mul_nonneg (S.place_nonneg p₁ hX) (S.place_nonneg p₂ hY)
    (S.place_comm p₁ p₂ hopp X Y)

section

variable (S : ProjectiveSetting P ε) (p q : Placement) (h : p.IsOpposite q)
include h

/-- A positive right effect preserves order in the left effect on opposite registers. -/
theorem placedCorrelation_mono_left {A B : Op (S.ExpandedLocalSpace p.side)}
    {C : Op (S.ExpandedLocalSpace q.side)} (hAB : A ≤ B) (hC : 0 ≤ C) :
    S.placedCorrelation p q A C ≤ S.placedCorrelation p q B C := by
  have hprod := S.place_mul_place_nonneg p q h (sub_nonneg.mpr hAB) hC
  rw [S.place_sub, sub_mul] at hprod
  exact DistanceCalculus.stateQForm_mono _ (sub_nonneg.mp hprod)

/-- A positive left effect preserves order in the right effect on opposite registers. -/
theorem placedCorrelation_mono_right {A : Op (S.ExpandedLocalSpace p.side)}
    {B C : Op (S.ExpandedLocalSpace q.side)} (hA : 0 ≤ A) (hBC : B ≤ C) :
    S.placedCorrelation p q A B ≤ S.placedCorrelation p q A C := by
  have hprod := S.place_mul_place_nonneg p q h hA (sub_nonneg.mpr hBC)
  rw [S.place_sub, mul_sub] at hprod
  exact DistanceCalculus.stateQForm_mono _ (sub_nonneg.mp hprod)

end

end ProjectiveSetting

/-! ## Nonnegativity of the pointwise consistency defect -/

section

variable {P : AdmissibleParams} {ε : ℝ}
    {α : Type*} [Fintype α] [DecidableEq α] (S : ProjectiveSetting P ε)
include P ε α S

/-- The integrand of the consistency defect of two complete measurements placed
on opposite registers is nonnegative.  This is the positivity hypothesis needed
by items 1 and 2 of blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1058`. -/
theorem consistencyDefect_integrand_nonneg
    (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂)
    (M₁ : MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p₁.side))
    (M₂ : MIPStarRE.Quantum.Measurement α (S.ExpandedLocalSpace p₂.side)) :
    0 ≤ ∑ a : α, ∑ b : α,
      if a = b then 0
      else S.placedCorrelation p₁ p₂ (M₁.effect a) (M₂.effect b) := by
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  split
  · exact le_rfl
  · exact DistanceCalculus.stateQForm_nonneg _
      (S.place_mul_place_nonneg p₁ p₂ hopp (M₁.pos a) (M₂.pos b))

/-- A complete pair of placed measurements has at most unit mismatch mass. -/
theorem consistencyDefect_integrand_le_one
    (p q : Placement) (h : p.IsOpposite q)
    (A : Measurement α (S.ExpandedLocalSpace p.side))
    (B : Measurement α (S.ExpandedLocalSpace q.side)) :
    (∑ a : α, ∑ b : α, if a = b then 0 else S.placedCorrelation p q (A.effect a) (B.effect b)) ≤ 1 := by
  have he := DistanceCalculus.point_defect_eq (S.placedMeasurement p A)
    (S.placedMeasurement q B) S.psiHat
  simp only [S.placedMeasurement_effect, S.psiHat_norm, one_pow] at he
  rw [he]
  exact sub_le_self _ (Finset.sum_nonneg fun a _ => DistanceCalculus.stateQForm_nonneg _
    (S.place_mul_place_nonneg p q h (A.pos a) (B.pos a)))

end

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε)
  {X α : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
  (p q : Placement) (μ : Distribution X)
  (A : X → Measurement α (S.ExpandedLocalSpace p.side))
  (B : X → Measurement α (S.ExpandedLocalSpace q.side))

theorem placedDefect_nonneg (h : p.IsOpposite q) : 0 ≤ S.placedDefect p q μ A B :=
  avgOver_nonneg _ _ fun x => consistencyDefect_integrand_nonneg S p q h (A x) (B x)

theorem placedDefect_le_one (h : p.IsOpposite q) (hμ : μ.IsProbability) :
    S.placedDefect p q μ A B ≤ 1 :=
  avgOver_le_of_weight_sum_le_one _ _ _ hμ.weight_sum_eq_one.le zero_le_one
    fun x => consistencyDefect_integrand_le_one S p q h (A x) (B x)

end ProjectiveSetting

end

end MIPStarRE.QPBT
