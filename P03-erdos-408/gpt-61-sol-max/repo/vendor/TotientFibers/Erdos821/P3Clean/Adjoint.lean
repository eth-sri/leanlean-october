module
public import Mathlib.Tactic

public import Erdos821.P3Clean.Contractions

/-! The weighted adjoint has the same finite-support norm bound. -/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

def weightedAdjoint {α : Type*} (mass : α → ℝ) (K : α → α → ℂ) (a b : α)  :=
  ((mass b / mass a : ℝ) : ℂ) * star (K b a)

theorem normBound_weightedAdjoint {α : Type*} (mass : α → ℝ) (K : α → α → ℂ)
     C  (hm : ∀ a, mass a ≠ 0) (hK : NormBound mass K C) :
    NormBound mass (weightedAdjoint mass K) C := by
  intro s t f g
  have h := hK t s g f
  have hform : (∑ a ∈ s, ∑ b ∈ t,
      (mass a : ℂ) * star (f a) * weightedAdjoint mass K a b * g b) =
      star (∑ b ∈ t, ∑ a ∈ s, (mass b : ℂ) * star (g b) * K b a * f a) := by
    simp only [star_sum, star_mul, Complex.star_def, Complex.conj_ofReal,
      Complex.conj_conj]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    unfold weightedAdjoint
    have hma : (mass a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hm a)
    simp only [Complex.ofReal_div, Complex.star_def]
    simp only [starRingEnd_apply]
    field_simp [hma]
  rw [hform, norm_star]
  grind


end Erdos821.P3Clean
