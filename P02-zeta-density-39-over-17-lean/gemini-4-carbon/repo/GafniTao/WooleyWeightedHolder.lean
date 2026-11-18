module
public import Mathlib

@[expose] public section

/-!
# The weighted Hölder inequality used in Wooley (3.9)

Mathlib supplies the one-over-`p` form.  The source repeatedly uses its
`p`-th-power consequence.  We isolate that consequence with all positivity
hypotheses visible.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooley_weighted_rpow_sum_le
    {ι : Type*} (t : Finset ι) (w f : ι → ℝ) {p : ℝ}
    (hp : 1 ≤ p) (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) :
    (∑ i ∈ t, w i * f i) ^ p ≤
      (∑ i ∈ t, w i) ^ (p - 1) *
        ∑ i ∈ t, w i * f i ^ p := by
  let A := ∑ i ∈ t, w i * f i
  let W := ∑ i ∈ t, w i
  let D := ∑ i ∈ t, w i * f i ^ p
  have hA : 0 ≤ A := by
    exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i) (hf i)
  have hW : 0 ≤ W := by
    exact Finset.sum_nonneg fun i hi => hw i
  have hD : 0 ≤ D := by
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (hw i) (Real.rpow_nonneg (hf i) p)
  have hpPos := zero_lt_one.trans_le hp
  have hHolder : A ≤ W ^ (1 - p⁻¹) * D ^ p⁻¹ := by
    simpa using
      Real.inner_le_weight_mul_Lp_of_nonneg t hp w f hw hf
  calc
    A ^ p ≤ (W ^ (1 - p⁻¹) * D ^ p⁻¹) ^ p := (Real.rpow_le_rpow hA hHolder hpPos.le)
    _ = (W ^ (p - 1)) * D := by
      rw [Real.mul_rpow (Real.rpow_nonneg hW _) (Real.rpow_nonneg hD _),
        ← Real.rpow_mul hW, ← Real.rpow_mul hD]
      rw [inv_mul_cancel₀ (ne_of_gt hpPos), Real.rpow_one]
      congr 1
      field_simp
    _ = (∑ i ∈ t, w i) ^ (p - 1) *
        ∑ i ∈ t, w i * f i ^ p := by rfl


end

end GafniTao
