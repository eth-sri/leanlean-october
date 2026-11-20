module

public import OAI.NumberTheory.DirichletL.Moments.SecondHarmonicBudget
public import OAI.NumberTheory.DirichletL.Moments.SourceAbsoluteEnvelope
public import OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell
public import OAI.NumberTheory.DirichletL.Moments.SecondMaskedWindow
public import OAI.NumberTheory.DirichletL.Moments.SecondRadicalColumns
public import OAI.NumberTheory.DirichletL.Moments.SecondWindowBudget
public import OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope






@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondOriginalChildren
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentLogDyadic CenteredMomentSmooth
open CenteredMomentSupport CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open RayFourExpansion CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns
open CenteredMomentSecondWindowBudget CenteredMomentRestrictedSource CenteredMomentFirstSectors
open CenteredMomentSecondWindowSource CenteredMomentSecondIdealBlockBound
local notation "O" => ActualEisensteinCubic.O

open Filter CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData
open CenteredMomentCommonRadialPointwise CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def core (s:Input ι) (C:Ideal O) (C0 Z δ E:ℝ) : ℝ :=
  C0*Z^δ*(profileCost s*E)*(s.X₁*s.X₂*∏i,s.P i)/(Ideal.absNorm C:ℝ)

omit [DecidableEq ι] in
lemma envelope_eq_core (s:Input ι) (C L:Ideal O) (C0 Z δ E:ℝ) :
    envelope s C L C0 Z δ E=core s C C0 Z δ E/(Ideal.absNorm L:ℝ):=by
  unfold envelope core;ring

def sourceRadial (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (H:ℝ) (hH:0<H)
    (hΦ:∀z:O,0≤(Φ (normValue z/H)).re) : Radial :=
  ⟨keep,Φ,H,hH,fun z=>by simpa only [normValue_eq_embedding] using hΦ z⟩

end SevenEighths.CenteredMomentSecondOriginalChildren

end

end OAI
