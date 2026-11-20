module

public import OAI.NumberTheory.DirichletL.Arithmetic.PrincipalFamily
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAllSlots

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerUnits
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerBranch
local notation "Eis"=>ActualEisensteinCubic.O
local instance initialEnergyUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [OAI.PrincipalFamily.Maximal p]
  (hcop:OAI.PrincipalFamily.Coprime p)
  (hg:OAI.PrincipalFamily.Avoids p ConcretePrimeRowBridge.goodLambda)

def sourceSector (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(u:Eisˣ) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>unitSector p hp hpr (sourcePoint x ∅ ∅)=u)

omit [OAI.PrincipalFamily.Maximal p] in
theorem sourceSector_partition (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(f:Source (ι:=ι) 0→ℂ) :
    (∑x∈S,f x)=∑u:Eisˣ,∑x∈sourceSector p hp hpr S u,f x :=
  (Finset.sum_fiberwise S (fun x=>unitSector p hp hpr (sourcePoint x ∅ ∅)) f).symm

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem quotientSet_mono {J:ℕ}{S T:Finset (Source (ι:=ι) J)}(hst:S⊆T) :
    quotientSet p S⊆quotientSet p T := Finset.image_subset_image hst

theorem unit_sector_card : Fintype.card Eisˣ=6 := by
  simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six


end SevenEighths.InverseInitialEnergyCallerUnits

end

end OAI
