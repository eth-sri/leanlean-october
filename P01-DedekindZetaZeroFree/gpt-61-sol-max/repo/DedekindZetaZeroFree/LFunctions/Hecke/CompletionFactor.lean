module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section


namespace DedekindZetaZeroFree

noncomputable section
open scoped NumberField

def heckeCompletionFactor (F : Type*) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (s : ℂ)  :=
  (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm 𝔪 : ℂ)) ^ (s / 2) *
    Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces F

private lemma differentiableAt_Gammaℂ {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℂ s := by
  change DifferentiableAt ℂ (fun z => 2 * (2 * (Real.pi : ℂ)) ^ (-z) * Complex.Gamma z) s
  refine DifferentiableAt.mul (DifferentiableAt.mul (differentiableAt_const (2 : ℂ)) ?_)
    (Complex.differentiableAt_Gamma s ?_)
  · exact (differentiableAt_id.neg).const_cpow
      (Or.inl (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  · intro m h
    have hsre  := hs
    rw [h] at hsre
    simp at hsre
    
    linarith

private lemma Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Complex.Gammaℂ s ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hs)
  apply Complex.cpow_ne_zero_iff.mpr <;> aesop

section
variable (F : Type*) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
include F 𝔪 h𝔪
private lemma heckeCompletionFactor_base_ne_zero   :
    (((|NumberField.discr F| : ℤ) : ℂ) * (Ideal.absNorm 𝔪 : ℂ)) ≠ 0 := by
  apply mul_ne_zero
  · rw [Int.cast_ne_zero, abs_ne_zero]
    exact NumberField.discr_ne_zero F
  · rw [Nat.cast_ne_zero]
    exact Ideal.absNorm_eq_zero_iff.not.mpr h𝔪

theorem heckeCompletionFactor_ne_zero   (s : ℂ) (hs : 0 < s.re) :
    heckeCompletionFactor F 𝔪 s ≠ 0 := by
  unfold heckeCompletionFactor
  exact mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (heckeCompletionFactor_base_ne_zero F 𝔪 h𝔪)))
    (pow_ne_zero _ (Gammaℂ_ne_zero_of_re_pos hs))

theorem differentiableOn_heckeCompletionFactor   :
    DifferentiableOn ℂ (heckeCompletionFactor F 𝔪) {s : ℂ | 0 < s.re} := by
  intro s hs
  unfold heckeCompletionFactor
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.mul ?_ ?_
  · exact (differentiableAt_id (𝕜 := ℂ) (x := s)).div_const (2 : ℂ) |>.const_cpow
      (Or.inl (heckeCompletionFactor_base_ne_zero F 𝔪 h𝔪))
  · exact (differentiableAt_Gammaℂ hs).pow _

def differentiableOn_inv_heckeCompletionFactor    := (differentiableOn_heckeCompletionFactor F 𝔪 h𝔪).inv
    (fun s hs => heckeCompletionFactor_ne_zero F 𝔪 h𝔪 s hs)

theorem hasSum_div_heckeCompletionFactor   (s : ℂ) (hs : 0 < s.re)
    {ι : Type*} (a : ι → ℂ) (B : ℂ)
    (h : HasSum (fun I => heckeCompletionFactor F 𝔪 s * a I) B) :
    HasSum a (B / heckeCompletionFactor F 𝔪 s) := by
  have hA := heckeCompletionFactor_ne_zero F 𝔪 h𝔪 s hs
  have h' := h.mul_left (heckeCompletionFactor F 𝔪 s)⁻¹
  simpa [div_eq_mul_inv, ← mul_assoc, hA, mul_comm] using h'
end


end

end DedekindZetaZeroFree
