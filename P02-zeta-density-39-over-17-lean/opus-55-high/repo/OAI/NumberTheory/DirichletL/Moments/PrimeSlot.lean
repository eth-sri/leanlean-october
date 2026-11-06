module
public import OAI.NumberTheory.DirichletL.Moments.WholeSlotDeletion
public import OAI.NumberTheory.DirichletL.Moments.RayNonprincipal
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPrimeSlot
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentTwist
local notation "O" => HeckeFamily.O

def primePool (M:Ideal O) (H:Subgroup (O⧸M)ˣ) (b D:ℝ) : Finset (Ideal O) :=
  (annulusSet b D).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H)

lemma sqrt_inverse_cpow (D:ℝ) (hD:0<D) :
    (Real.sqrt D:ℂ)⁻¹=(D:ℂ)^(-(1/2:ℂ)) := by
  pm_6401 hD.le

end SevenEighths.CenteredMomentPrimeSlot

end

end OAI
