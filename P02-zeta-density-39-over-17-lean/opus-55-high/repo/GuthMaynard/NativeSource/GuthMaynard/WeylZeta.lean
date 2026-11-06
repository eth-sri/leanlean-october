module
public import GuthMaynard.NativeSource.GuthMaynard.WeylExplicit
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Finset Set
open scoped BigOperators

namespace GuthMaynard.NativeMoment

/-!
# Critical-line consequences of the Weyl estimate

The finite Abel lemma below transfers uniform bounds for unweighted phase
prefixes to monotone nonnegative weights.  It is then applied to the actual
`n^(-1/2-it)` critical-line weight.
-/

theorem norm_weighted_sum_le_of_antitone
    (f : Nat -> Real) (g : Nat -> Complex) (N : Nat) (B : Real)
    (hN : 0 < N)
    (hf : forall i, i < N -> 0 <= f i)
    (hanti : forall i, i + 1 < N -> f (i + 1) <= f i)
    (hpartial : forall j, j <= N -> ‖∑ i ∈ Finset.range j, g i‖ <= B) :
    ‖∑ i ∈ Finset.range N, f i • g i‖ <= f 0 * B := by
  have hparts := Finset.sum_Ico_by_parts f g hN
  rw [Finset.range_eq_Ico]
  calc
    ‖∑ i ∈ Finset.Ico 0 N, f i • g i‖ =
        ‖f (N - 1) • (∑ i ∈ Finset.range N, g i) -
          f 0 • (∑ i ∈ Finset.range 0, g i) -
          ∑ i ∈ Finset.Ico 0 (N - 1),
            (f (i + 1) - f i) • (∑ j ∈ Finset.range (i + 1), g j)‖ :=
      congrArg norm hparts
    _ = ‖(f (N - 1) : Complex) * (∑ i ∈ Finset.range N, g i) -
        ∑ i ∈ Finset.Ico 0 (N - 1),
          ((f (i + 1) - f i : Real) : Complex) *
            (∑ j ∈ Finset.range (i + 1), g j)‖ := by simp_all
    _ <= ‖(f (N - 1) : Complex) * (∑ i ∈ Finset.range N, g i)‖ +
        ‖∑ i ∈ Finset.Ico 0 (N - 1),
          ((f (i + 1) - f i : Real) : Complex) * (∑ j ∈ Finset.range (i + 1), g j)‖ :=
      norm_sub_le _ _
    _ <= f (N - 1) * B +
        ∑ i ∈ Finset.Ico 0 (N - 1), (f i - f (i + 1)) * B := by
      apply add_le_add
      · rw [norm_mul, norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hf (N - 1) (by omega))]
        exact mul_le_mul_of_nonneg_left (hpartial N le_rfl) (hf (N - 1) (by omega))
      · calc
          ‖∑ i ∈ Finset.Ico 0 (N - 1),
              ((f (i + 1) - f i : Real) : Complex) *
                (∑ j ∈ Finset.range (i + 1), g j)‖ <=
              ∑ i ∈ Finset.Ico 0 (N - 1),
                ‖((f (i + 1) - f i : Real) : Complex) *
                  (∑ j ∈ Finset.range (i + 1), g j)‖ := norm_sum_le _ _
          _ <= ∑ i ∈ Finset.Ico 0 (N - 1), (f i - f (i + 1)) * B := by
            pm_5926 abs_of_nonpos sub_nonpos.mpr hanti
            rw [neg_sub]
            pm_5614 hanti
    _ = f 0 * B := by
      have htel : ∑ i ∈ Finset.Ico 0 (N - 1), (f i - f (i + 1)) =
          f 0 - f (N - 1) := by
        rw [Nat.Ico_zero_eq_range, Finset.sum_range_sub']
      rw [← Finset.sum_mul, htel]
      ring

theorem logarithmicSum_eq_sum_range (t : Real) (A N : Nat) :
    logarithmicSum t A (A + N) =
      ∑ n ∈ Finset.range N, unitaryPhase (logarithmicPhase t (A + n)) := by
  unfold logarithmicSum phaseSum
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left, Nat.cast_add]

end GuthMaynard.NativeMoment
