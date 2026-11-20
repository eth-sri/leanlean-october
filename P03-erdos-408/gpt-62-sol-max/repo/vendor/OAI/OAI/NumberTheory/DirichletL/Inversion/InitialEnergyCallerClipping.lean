module

public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalFamily
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerUnits
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerBranch
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerMass

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical
open ActualEisensteinCubic CompletedGauss
namespace SevenEighths.InverseInitialEnergyCallerClipping
open InverseMoment InverseInitialClippedColumns InverseInitialProfile
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [OAI.PrincipalFamily.Maximal p]
  (hcop:OAI.PrincipalFamily.Coprime p)
  (hg:OAI.PrincipalFamily.Avoids p ConcretePrimeRowBridge.goodLambda)

omit [DecidableEq σ] in
theorem normalized_energy_clipping
    (pool:Finset ι)(Ψ:Eis→*ℂ)(m:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(labels:Finset (Ideal Eis))(rows:Finset Eis)
    (d:Ideal Eis→ℝ)(w:ℝ→ℂ){Z:ℝ}(hZ:0<Z)(N h F:ℝ) :
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows d
      (childLogTest w h) (Z^N) Z F =
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows d
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) Z F := by
  unfold normalizedColumnEnergy
  simp_rw [norm_mul, canonical_row_clipping_norm p hp hcop hg pool Ψ m _ _
    slots lists a w hZ N h]

end SevenEighths.InverseInitialEnergyCallerClipping

end

end OAI
