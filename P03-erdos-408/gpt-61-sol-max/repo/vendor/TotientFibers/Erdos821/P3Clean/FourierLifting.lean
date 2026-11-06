module
public import Mathlib.Tactic

public import Erdos821.P3Clean.FiniteFourier

/-! A finite residue translation lift preserves a uniform Fourier-fibre norm. -/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {α G : Type*} [Fintype α] [AddCommGroup G] [Fintype G]

def fourierFibre (H : α → α → G → ℂ) (ψ : AddChar G ℂ) (a b : α)  :=
  ∑ d : G, H a b d * ψ d

def translationLift (H : α → α → G → ℂ) (a b : α × G)  :=
  H a.1 b.1 (b.2 - a.2)

section
variable (mass : α → ℝ) (H : α → α → G → ℂ) (f g : α × G → ℂ)


theorem weighted_fourier_parseval     :
    (∑ ψ : AddChar G ℂ, ∑ a : α,
      mass a * ‖finiteFourier (fun r => f (a, r)) ψ‖ ^ 2) =
      (Fintype.card G : ℝ) * ∑ a : α, ∑ r : G, mass a * ‖f (a, r)‖ ^ 2 := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum, finiteFourier_parseval, ← Finset.mul_sum]
  ring

theorem weighted_fourier_form    
      :
    (∑ ψ : AddChar G ℂ, ∑ a : α, ∑ b : α,
      (mass a : ℂ) * star (finiteFourier (fun r => f (a, r)) ψ) *
        fourierFibre H ψ a b * finiteFourier (fun r => g (b, r)) ψ) =
      (Fintype.card G : ℂ) * ∑ a : α, ∑ b : α, ∑ r : G, ∑ d : G,
        (mass a : ℂ) * star (f (a, r)) * H a b d * g (b, r + d) := by
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  calc
    _ = (mass a : ℂ) * ∑ ψ : AddChar G ℂ,
        star (finiteFourier (fun r => f (a, r)) ψ) *
          (∑ d : G, H a b d * ψ d) * finiteFourier (fun r => g (b, r)) ψ := by
      simp only [fourierFibre, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ = (mass a : ℂ) * ((Fintype.card G : ℂ) * ∑ r : G, ∑ d : G,
        star (f (a, r)) * H a b d * g (b, r + d)) := by
      rw [finiteFourier_convolution_form]
    _ = _ := by
      simp only [Finset.mul_sum]
      ring

theorem translationLift_form    
      :
    (∑ a : α × G, ∑ b : α × G,
      (mass a.1 : ℂ) * star (f a) * translationLift H a b * g b) =
      ∑ a : α, ∑ b : α, ∑ r : G, ∑ d : G,
        (mass a : ℂ) * star (f (a, r)) * H a b d * g (b, r + d) := by
  classical
  simp only [Fintype.sum_prod_type, translationLift]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro r _
  symm
  apply Fintype.sum_equiv (Equiv.addLeft r)
  intro d
  simp

theorem normBound_translationLift     (C : ℝ)
    (hm : ∀ a, 0 ≤ mass a) (hC : 0 ≤ C)
    (hH : ∀ ψ : AddChar G ℂ, NormBound mass (fourierFibre H ψ) C) :
    NormBound (fun a : α × G => mass a.1) (translationLift H) C := by
  classical
  apply (normBound_iff_univ _ _ _).mpr
  intro f g
  have h := sum_fibre_forms_bound mass (fourierFibre H) C hm hC hH
    (fun ψ a => finiteFourier (fun r => f (a, r)) ψ)
    (fun ψ a => finiteFourier (fun r => g (a, r)) ψ)
  rw [weighted_fourier_form, weighted_fourier_parseval, weighted_fourier_parseval] at h
  simp only [norm_mul, Complex.norm_natCast] at h
  have hn : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [Real.sqrt_mul hn.le, Real.sqrt_mul hn.le] at h
  have hr : (Real.sqrt (Fintype.card G : ℝ)) ^ 2 = (Fintype.card G : ℝ) :=
    Real.sq_sqrt hn.le
  have heq (U V : ℝ) : C * (Real.sqrt (Fintype.card G : ℝ) * Real.sqrt U) *
      (Real.sqrt (Fintype.card G : ℝ) * Real.sqrt V) =
      (Fintype.card G : ℝ) * (C * Real.sqrt U * Real.sqrt V) := by
    grind
  rw [heq] at h
  have hh := le_of_mul_le_mul_left h hn
  rw [translationLift_form]
  simpa only [Fintype.sum_prod_type] using hh

end


end Erdos821.P3Clean
