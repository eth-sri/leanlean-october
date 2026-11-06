module
public import Mathlib.Tactic

public import Erdos821.P4Probe.Probability

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

lemma weighted_pair_le {β : Type*} [Fintype β]
    (w : β → ℝ) (hw : ∀ z, 0 ≤ w z) (f g multiplier : β → ℂ)
    (hm : ∀ z, ‖multiplier z‖ ≤ 1) :
    ‖∑ z, (w z : ℂ) * star (f z) * g z * multiplier z‖ ≤
      Real.sqrt (∑ z, w z * ‖f z‖ ^ 2) * Real.sqrt (∑ z, w z * ‖g z‖ ^ 2) := by
  have hcs := weighted_sqrt_cauchy w (fun z => ‖f z‖ ^ 2) (fun z => ‖g z‖ ^ 2)
    hw (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  have hc : (∑ z, w z * ‖f z‖ * ‖g z‖) ≤
      Real.sqrt (∑ z, w z * ‖f z‖ ^ 2) * Real.sqrt (∑ z, w z * ‖g z‖ ^ 2) := by
    simp_all
  calc
    _ ≤ ∑ z, ‖(w z : ℂ) * star (f z) * g z * multiplier z‖ := norm_sum_le _ _
    _ ≤ ∑ z, w z * ‖f z‖ * ‖g z‖ := by
      apply Finset.sum_le_sum
      intro z _
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hw z)]
      bound
    _ ≤ _ := hc

def finiteRestrict {β } (s : Finset β) (f : β → ℂ) (z : β)  :=
  if z ∈ s then f z else 0

section
variable {β : Type*} [Fintype β] (w : β → ℝ)
include β w

lemma finiteRestrict_sqNorm      
     s   f  :
    (∑ z, w z * ‖finiteRestrict s f z‖ ^ 2) = ∑ z ∈ s, w z * ‖f z‖ ^ 2 := by
  simp only [finiteRestrict, apply_ite, norm_zero]
  simp

lemma normBound_of_full_pair      
    (K : β → β → ℂ)  C 
    (hK : ∀ f g : β → ℂ,
      ‖∑ a, ∑ b, (w a : ℂ) * star (f a) * K a b * g b‖ ≤
        C * Real.sqrt (∑ a, w a * ‖f a‖ ^ 2) * Real.sqrt (∑ b, w b * ‖g b‖ ^ 2)) :
    NormBound w K C := by
  intro s t f g
  have h := hK (finiteRestrict s f) (finiteRestrict t g)
  rw [finiteRestrict_sqNorm, finiteRestrict_sqNorm] at h
  have hp : (∑ a, ∑ b, (w a : ℂ) * star (finiteRestrict s f a) * K a b * finiteRestrict t g b) =
      ∑ a ∈ s, ∑ b ∈ t, (w a : ℂ) * star (f a) * K a b * g b := by
    simp only [finiteRestrict, apply_ite, star_zero, ite_mul, mul_zero, zero_mul]
    simp
  rw [hp] at h
  exact h

end

end
end Erdos821.P4Probe
