module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.ExponentPairFiniteCorrelation
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

 
                                                    

                                                                      
                                                                   
                                 


noncomputable section

open Finset RiemannZeta.GuthMaynard
open scoped BigOperators

namespace TaoTrudgianYang2025

section
variable (C : ℕ → ℝ)
include C
theorem sum_lower_shift_distances_le {H h : ℕ}
    (hh : h < H) (hC : ∀ r ∈ Icc 1 (H-1), 0 ≤ C r) :
    (∑ k ∈ range H, if k < h then C (h-k) else 0) ≤
      ∑ r ∈ Icc 1 (H-1), C r := by
  let s := (range H).filter (fun k => k < h)
  have hinj : Set.InjOn (fun k => h-k) (s : Set ℕ) := by
    intro x hx y hy he
    pm_547 hx' mem_filter.mp hx hy' hy
    dsimp at he
    omega
  have hsub : s.image (fun k => h-k) ⊆ Icc 1 (H-1) := by
    pm_67 r hr k hk mem_image.mp
    have hk' := (mem_filter.mp hk).2
    grind
  calc
    _ = ∑ k ∈ s, C (h-k) := by simp only [s,sum_filter]
    _ = ∑ r ∈ s.image (fun k => h-k), C r := (sum_image hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun r hr _ => hC r hr)

theorem sum_upper_shift_distances_le {H h : ℕ}
    (hC : ∀ r ∈ Icc 1 (H-1), 0 ≤ C r) :
    (∑ k ∈ range H, if h < k then C (k-h) else 0) ≤
      ∑ r ∈ Icc 1 (H-1), C r := by
  let s := (range H).filter (fun k => h < k)
  have hinj : Set.InjOn (fun k => k-h) (s : Set ℕ) := by
    intro x hx y hy he
    pm_547 hx' mem_filter.mp hx hy' hy
    dsimp at he
    omega
  have hsub : s.image (fun k => k-h) ⊆ Icc 1 (H-1) := by
    pm_67 r hr k hk mem_image.mp
    have hk' := mem_filter.mp hk
    have hkH := mem_range.mp hk'.1
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  calc
    _ = ∑ k ∈ s, C (k-h) := by simp only [s,sum_filter]
    _ = ∑ r ∈ s.image (fun k => k-h), C r := (sum_image hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun r hr _ => hC r hr)

theorem sum_shift_distance_row_le (D : ℝ) {H h : ℕ}
    (hh : h < H) (hC : ∀ r ∈ Icc 1 (H-1), 0 ≤ C r) :
    (∑ k ∈ range H, if h = k then D else C (shiftDistance h k)) ≤
      D+2*∑ r ∈ Icc 1 (H-1), C r := by
  have he (k : ℕ) :
      (if h = k then D else C (shiftDistance h k)) =
        (if k = h then D else 0)+
          (if k < h then C (h-k) else 0)+(if h < k then C (k-h) else 0) := by
    rcases lt_trichotomy h k with hk | hk | hk
    pm_6032
    · subst k
      simp
    pm_6032
  simp_rw [he]
  rw [sum_add_distrib,sum_add_distrib]
  have hdiag : (∑ k ∈ range H, if k = h then D else 0) = D := by
    simp [mem_range.mpr hh]
  rw [hdiag]
  linarith [sum_lower_shift_distances_le C hh hC,sum_upper_shift_distances_le (h := h) C hC]
end

end TaoTrudgianYang2025
