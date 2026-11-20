/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Algebra.Equations
public import CCDN.Determinant.ShiftMatrix
public import CCDN.Height.IntegerCoefficientHeight
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finsupp.MonomialOrder.DegLex

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
variable {n d M t : ℕ}

private lemma log_factorial_bound {s N : ℕ} (hs : s ≤ N) :
    Real.log s.factorial ≤ s * Real.log (N : ℝ) := by
  have hh : (s.factorial : ℝ) ≤ (N : ℝ) ^ s := by
    exact_mod_cast (Nat.factorial_le_pow s).trans (Nat.pow_le_pow_left hs s)
  simpa using Real.log_le_log (by positivity) hh

/-- The archimedean half of the determinant comparison, with the exact Hilbert rank. -/
theorem homogeneous_no_auxiliary_box_comparison
    (order : MonomialOrder (Fin (n+1))) (f : IntegerPolynomial (n+1))
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (z : Fin t → IntPoint (n+1)) (hz : ∀ i, eval (z i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B)
    (hrel : ∀ g : IntegerPolynomial (n+1), g.IsHomogeneous M →
      (∀ i, eval (z i) g = 0) → f ∣ g) :
    ∃ (s : ℕ) (a : Fin s → Fin t), Function.Injective a ∧ s < formDim n M ∧
      s + formDim n (M-d) = formDim n M ∧
      let A := evaluationMatrix (homogeneousMonomials n M) (z ∘ a)
      LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row ∧
      Real.log (Int.Matrix.minorGcd A : ℝ) ≤ Real.log s.factorial +
        s * M * Real.log B - ((formDim n M : ℝ) - s) * Real.log |((order.leadingCoeff f : ℤ) : ℝ)| := by
  have hc := order.leadingCoeff_ne_zero_iff.mpr hf0
  obtain ⟨s, a, ha, hs, hr, hi, h⟩ := homogeneous_coefficient_minor_bound order f hf hf0 hdM z hz hB hbox
    hrel _ hc (.inl rfl)
  refine ⟨s, a, ha, hs, hr, hi, ?_⟩
  let D := Int.Matrix.minorGcd (evaluationMatrix (homogeneousMonomials n M) (z ∘ a))
  have hD : (0:ℝ) < D := by exact_mod_cast one_pos.trans_le (Int.Matrix.one_le_minorGcd hi)
  change D * |((order.leadingCoeff f : ℤ) : ℝ)| ^ _ ≤ _ at h
  have hh := Real.log_le_log (mul_pos hD (pow_pos (abs_pos.mpr (by exact_mod_cast hc)) _)) h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow] at hh
  have hr' : (s:ℝ) + formDim n (M-d) = formDim n M := by exact_mod_cast hr
  rw [show (formDim n M : ℝ) - s = formDim n (M-d) by linarith only [hr']]
  linarith only [hh]

/-- In equal degree the shift matrix has a single column. Taking its largest entry
bounds the whole coefficient height. -/
theorem homogeneous_no_auxiliary_coefficient_height
    (f : IntegerPolynomial (n+1)) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (z : Fin t → IntPoint (n+1)) (hz : ∀ i, eval (z i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B)
    (hrel : ∀ g : IntegerPolynomial (n+1), g.IsHomogeneous d → (∀ i, eval (z i) g = 0) → f ∣ g) :
    Real.log (integerCoefficientHeight f) ≤ formDim n d * Real.log (formDim n d) +
      formDim n d * d * Real.log B := by
  classical
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf0) (fun m => (f.coeff m).natAbs)
  obtain ⟨s,a,-,hs,-,hi,h⟩ := homogeneous_coefficient_minor_bound .degLex f hf hf0 le_rfl z hz hB hbox
    hrel m (mem_support_iff.mp hm) (.inr rfl)
  simp only [Nat.sub_self, formDim, add_zero, Nat.choose_zero_right, pow_one] at h
  have hD : (1:ℝ) ≤ Int.Matrix.minorGcd (evaluationMatrix (homogeneousMonomials n d) (z ∘ a)) := by exact_mod_cast Int.Matrix.one_le_minorGcd hi
  have h' := (le_mul_of_one_le_left (abs_nonneg _) hD).trans h
  have hpos : 0 < |(f.coeff m : ℝ)| := abs_pos.mpr (by exact_mod_cast mem_support_iff.mp hm)
  have hh := Real.log_le_log hpos h'
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hh
  have hN : (1:ℝ) ≤ formDim n d := by exact_mod_cast (show 1 ≤ formDim n d by omega)
  have hmono : (s:ℝ) ≤ formDim n d := by exact_mod_cast hs.le
  rw [integerCoefficientHeight, he, Nat.cast_natAbs, Int.cast_abs]
  calc
    _ ≤ s * Real.log (formDim n d) + s * (d * Real.log B) := by linarith [log_factorial_bound hs.le]
    _ ≤ _ := by rw [mul_assoc]; gcongr; exact mul_nonneg (by positivity) (Real.log_nonneg hB)

end
end CCDN
