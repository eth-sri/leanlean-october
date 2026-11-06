module

public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalGates

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstChildLower
open HeckeFamily CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput
open CenteredMomentCommonExceptionalGates CenteredMomentCommonAllocationSum
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

theorem child_lower (s:Input ι)(C R:Ideal HeckeFamily.O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    let d:=child s C R B τ t
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.X₁ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.X₂ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.Y₁ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.Y₂:=by
  exact ⟨extracted_lower s C hC B (Sum.inr 0) Z r s.X₁ hZ hX₁,
    extracted_lower s C hC B (Sum.inr 1) Z r s.X₂ hZ hX₂,
    extracted_lower s C hC B (Sum.inr 0) Z r s.Y₁ hZ hY₁,
    extracted_lower s C hC B (Sum.inr 1) Z r s.Y₂ hZ hY₂⟩

end SevenEighths.CenteredMomentFirstChildLower

end

end OAI
