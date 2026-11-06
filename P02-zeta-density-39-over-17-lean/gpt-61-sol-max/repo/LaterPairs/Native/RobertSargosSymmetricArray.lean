module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosMixedCharacter
public import LaterPairs.Native.RobertSargosSourceATimesA

@[expose] public section
set_option maxHeartbeats 0


                                                             
                                                                 

noncomputable section
open GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025

section
variable (f : ℝ → ℝ) (M H : ℕ)
include f M H

def robertSargosSymmetricArray  (m h : ℤ) : ℂ :=
  if h ∈ Finset.Ico (H:ℤ) (2*H) then
    if m ∈ Finset.Icc (h+1) ((M:ℤ)-h) then
      fordAdditiveCharacter (robertSargosSymmetricDifference f m h)
    else 0
  else 0

def robertSargosSymmetricSum  : ℂ :=
  ∑ h ∈ Finset.Ico (H:ℤ) (2*H),
    ∑ m ∈ Finset.Icc (h+1) ((M:ℤ)-h),
      fordAdditiveCharacter (robertSargosSymmetricDifference f m h)

theorem robertSargos_symmetric_array_support 
    (m h : ℤ) (hout : m ∉ Finset.Icc (1:ℤ) M ∨ h ∉ Finset.Icc (1:ℤ) (2*H)) :
    robertSargosSymmetricArray f M H m h = 0 := by
  unfold robertSargosSymmetricArray
  grind

theorem robertSargos_symmetric_array_sum  :
    (∑ m ∈ Finset.Icc (1:ℤ) M, ∑ h ∈ Finset.Icc (1:ℤ) (2*H),
      robertSargosSymmetricArray f M H m h) = robertSargosSymmetricSum f M H := by
  classical
  rw [Finset.sum_comm]
  have hsub : Finset.Ico (H:ℤ) (2*H) ⊆ Finset.Icc (1:ℤ) (2*H) := by grind
  calc
    _ = ∑ h ∈ Finset.Ico (H:ℤ) (2*H), ∑ m ∈ Finset.Icc (1:ℤ) M,
        robertSargosSymmetricArray f M H m h := by
      symm
      apply Finset.sum_subset hsub
      intro h _ hh
      apply Finset.sum_eq_zero
      intro m _
      simp only [robertSargosSymmetricArray,ite_eq_right hh]
    _ = _ := by
      unfold robertSargosSymmetricSum
      apply Finset.sum_congr rfl
      intro h hh
      have ht := Finset.mem_Ico.mp hh
      simp only [robertSargosSymmetricArray,ite_eq_left hh]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext m
      grind
end



