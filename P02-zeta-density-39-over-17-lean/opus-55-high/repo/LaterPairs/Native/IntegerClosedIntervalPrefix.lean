module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.ContinuousPhaseWeyl

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                                 

noncomputable section
namespace TaoTrudgianYang2025

section
variable (w : ℤ → ℂ) (a b : ℤ)
include w a b
theorem sum_integer_Ico_eq_range :
    (∑ m ∈ Finset.Ico a b, w m) =
      ∑ n ∈ Finset.range (b-a).toNat, w (a+n) := by
  symm
  apply Finset.sum_bij (fun (n : ℕ) _ => a+n)
  grind
  grind
  · intro m hm
    have hmi := Finset.mem_Ico.mp hm
    refine ⟨(m-a).toNat,Finset.mem_range.mpr (by omega),?_⟩
    have he := Int.toNat_of_nonneg (show 0 ≤ m-a by omega)
    omega
  grind

theorem sum_integer_Icc_eq_range_add (hab : a ≤ b) :
    (∑ m ∈ Finset.Icc a b, w m) =
      (∑ n ∈ Finset.range (b-a).toNat, w (a+n))+w b := by
  have he : Finset.Icc a b = insert b (Finset.Ico a b) := by
    ext n
    simp only [Finset.mem_Icc,Finset.mem_insert,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_insert (by simp),sum_integer_Ico_eq_range]
  grind
end

end TaoTrudgianYang2025
