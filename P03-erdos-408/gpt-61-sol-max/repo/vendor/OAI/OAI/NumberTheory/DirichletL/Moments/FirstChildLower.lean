module

public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
public import OAI.NumberTheory.DirichletL.Moments.CommonExceptionalGates

@[expose] public section

namespace OAI

section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstChildLower
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonExceptionalGates CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile

variable {ι:Type*}[Fintype ι]


theorem child_lower (s:Input ι) C R (hC:C≠0)
     B  τ  t Z r (hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    let d:=child s C R B τ t
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.X₁ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.X₂ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.Y₁ ∧
    Z^(r-Real.logb Z (C.absNorm:ℝ))≤d.Y₂:=⟨extracted_lower s C hC B (Sum.inr 0) Z r s.X₁ hZ hX₁,
    extracted_lower s C hC B (Sum.inr 1) Z r s.X₂ hZ hX₂,
    extracted_lower s C hC B (Sum.inr 0) Z r s.Y₁ hZ hY₁,
    extracted_lower s C hC B (Sum.inr 1) Z r s.Y₂ hZ hY₂⟩

end SevenEighths.CenteredMomentFirstChildLower

end

end OAI
