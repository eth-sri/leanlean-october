module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosDyadicSequence
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                 
                                                                                 

noncomputable section
open GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025

section
variable (f : ℝ → ℝ) (M H : ℕ) (hH : 2 ≤ H)
include f M H hH
theorem exists_robertSargos_weighted_dyadic :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      ‖robertSargosWeightedSymmetricPhase f M H‖ ≤
        (Nat.clog 2 H:ℝ)*((M:ℝ)+‖robertSargosSymmetricSum f M k‖) := by
  obtain ⟨k,hk,hkH,hs⟩ := exists_doubled_block_weighted
    (robertSargosPhaseSequence f M) H hH
    (by aesop)
    (M:ℝ) (Nat.cast_nonneg M) (fun n _ => robertSargos_phase_sequence_norm f M n)
  rw [robertSargos_phase_sequence_weighted,
    robertSargos_phase_sequence_block f M k hk] at hs
  grind

theorem exists_robertSargos_initial_dyadic (hHM : H ≤ M) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      ‖∑ m ∈ Finset.Icc (1:ℤ) M, fordAdditiveCharacter (f m)‖^2 ≤
        (3+6*(Nat.clog 2 H:ℝ))*(M:ℝ)^2/H+
          (6*(M:ℝ)*(Nat.clog 2 H:ℝ)/H)*‖robertSargosSymmetricSum f M k‖ := by
  pm_732 k hk hkH hs exists_robertSargos_weighted_dyadic f M H hH
  refine ⟨k,hk,hkH,?_⟩
  calc
    _ ≤ 3*(M:ℝ)^2/H+(6*(M:ℝ)/H)*‖robertSargosWeightedSymmetricPhase f M H‖ :=
      robertSargos_initial_source_a_process_range f M H (by omega) hHM
    _ ≤ 3*(M:ℝ)^2/H+(6*(M:ℝ)/H)*
        ((Nat.clog 2 H:ℝ)*((M:ℝ)+‖robertSargosSymmetricSum f M k‖)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hs (by positivity)) _
    _ = _ := by ring
end

end TaoTrudgianYang2025
