module

public import OAI.NumberTheory.DirichletL.Moments.DivisorSlots

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorBoundary
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem divisor_dyad_card (Ds : Finset (Ideal O)) (T : ℝ) (hT : 1 ≤ T)
    (hD : ∀ D ∈ Ds,D ≠ 0) (hN : ∀ D ∈ Ds,(Ideal.absNorm D:ℝ) < 2*T) :
    (Ds.card:ℝ) ≤ 256*T := by
  have h := DescentFiberCost.finite_ideal_count_real Ds (2*T) (by linarith) hD
    (fun D hD => (hN D hD).le)
  linarith

end SevenEighths.CenteredMomentDivisorBoundary

end

end OAI
