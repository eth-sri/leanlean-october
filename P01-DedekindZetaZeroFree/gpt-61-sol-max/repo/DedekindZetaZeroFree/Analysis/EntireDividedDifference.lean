module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section


namespace DedekindZetaZeroFree.AbelianQuotient

noncomputable section

section
variable (h : ℂ → ℂ)
include h
def entireDividedDifference   (a : ℂ)  :=
  dslope h a

theorem entireDividedDifference_apply   (a s : ℂ) :
    entireDividedDifference h a s =
      if s = a then deriv h a else (h s - h a) / (s - a) := by
  classical
  by_cases hs : s = a
  · subst s
    simp [entireDividedDifference]
  · simp [entireDividedDifference, dslope_of_ne h hs, slope_def_field, hs]





theorem entireDividedDifference_of_ne   (a s : ℂ) (hs : s ≠ a) :
    entireDividedDifference h a s = (h s - h a) / (s - a) := by
  rw [entireDividedDifference_apply, ite_eq_right hs]

theorem differentiable_entireDividedDifference  
    (hh : Differentiable ℂ h) (a : ℂ) :
    Differentiable ℂ (entireDividedDifference h a) := by
  rw [entireDividedDifference]
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (s := Set.univ) (c := a) (f := h)
    (by simp)).mpr (by rw [differentiableOn_univ]; exact hh)

theorem entireDividedDifference_of_zero   (a s : ℂ)
    (ha : h a = 0) (hs : s ≠ a) :
    entireDividedDifference h a s = h s / (s - a) := by
  rw [entireDividedDifference_of_ne h a s hs, ha, sub_zero]
end


end

end DedekindZetaZeroFree.AbelianQuotient
