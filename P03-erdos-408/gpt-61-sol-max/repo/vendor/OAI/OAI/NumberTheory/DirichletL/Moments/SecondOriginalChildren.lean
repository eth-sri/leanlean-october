module

public import OAI.NumberTheory.DirichletL.Moments.SecondSummedBlock
public import OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope
public import OAI.NumberTheory.DirichletL.Moments.SourceAbsoluteEnvelope
public import OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell
public import OAI.NumberTheory.DirichletL.Moments.SecondMaskedWindow
public import OAI.NumberTheory.DirichletL.Moments.SecondRadicalColumns
public import OAI.NumberTheory.DirichletL.Moments.SecondWindowBudget

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondOriginalChildren
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondRadicalColumns CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSecondIdealBlockBound


open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]


def core (s:Input ι) (C:Ideal ActualEisensteinCubic.O) (C0 Z δ E:ℝ)  :=
  C0*Z^δ*(profileCost s*E)*(s.X₁*s.X₂*∏i,s.P i)/(Ideal.absNorm C:ℝ)

omit [DecidableEq ι] in
lemma envelope_eq_core (s:Input ι)  C L   C0 Z δ E  :
    envelope s C L C0 Z δ E=core s C C0 Z δ E/(Ideal.absNorm L:ℝ):=by
  unfold envelope core;ring

def sourceRadial (keep:ActualEisensteinCubic.O→Prop) (Φ:𝓢(ℝ,ℂ)) (H) (hH:0<H)
    (hΦ:∀z:ActualEisensteinCubic.O,0≤(Φ (normValue z/H)).re) : Radial :=
  ⟨keep,Φ,H,hH,fun z=>by simpa only [normValue_eq_embedding] using hΦ z⟩

end SevenEighths.CenteredMomentSecondOriginalChildren

end

end OAI
