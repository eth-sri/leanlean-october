module

public import OAI.NumberTheory.DirichletL.Moments.WholeSlotDeletion
public import OAI.NumberTheory.DirichletL.Moments.RayNonprincipal

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentPrimeSlot
open HeckePrimeAnnular
local notation "O" => HeckeFamily.O

def primePool (M:Ideal HeckeFamily.O) (H:Subgroup (HeckeFamily.O⧸M)ˣ) (b D:ℝ) : Finset (Ideal HeckeFamily.O) :=
  (annulusSet b D).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H)

lemma sqrt_inverse_cpow (D:ℝ) (hD:0<D) :
    (Real.sqrt D:ℂ)⁻¹=(D:ℂ)^(-(1/2:ℂ)) := by
  rw [Complex.cpow_neg,Real.sqrt_eq_rpow]
  congr 1
  simpa using (Complex.ofReal_cpow hD.le (1/2:ℝ))

end SevenEighths.CenteredMomentPrimeSlot

end

end OAI
