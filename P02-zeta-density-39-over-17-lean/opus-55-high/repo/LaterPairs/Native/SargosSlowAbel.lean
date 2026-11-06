module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.AtkinsonMainPartialSummation
public import LaterPairs.Native.SargosSlowCharacter

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                           

noncomputable section

open GafniTao Set
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_sum_Ioc_eq_range {A : Type*} [AddCommMonoid A]
    (N H : ℕ) (f : ℤ → A) :
    (∑ n ∈ Finset.Ioc (N : ℤ) ((N : ℤ)+H), f n) =
      ∑ j ∈ Finset.range H, f ((N : ℤ)+j+1) := by
  symm
  refine Finset.sum_bij (fun j _ => (N : ℤ)+j+1) ?_ ?_ ?_ ?_
  grind
  grind
  · intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn0 : 0 ≤ n-(N : ℤ)-1 := by omega
    have hc := Int.toNat_of_nonneg hn0
    refine ⟨(n-(N : ℤ)-1).toNat,Finset.mem_range.mpr (by omega),?_⟩
    omega
  grind

end TaoTrudgianYang2025
