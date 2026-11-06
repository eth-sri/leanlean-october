module

public import OAI.NumberTheory.DirichletL.Moments.SecondSectorEnergy
public import OAI.NumberTheory.DirichletL.Moments.SecondFamilyTransport
public import OAI.NumberTheory.DirichletL.Moments.RestrictedWindow
public import OAI.NumberTheory.DirichletL.Moments.LogDyadic
public import OAI.NumberTheory.DirichletL.Moments.ConjugateWindow

@[expose] public section

namespace OAI

noncomputable section

open MeasureTheory

namespace SevenEighths.CenteredMomentSecondWindowSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily CenteredMomentRestrictedEnergy CenteredMomentRestrictedWindow CenteredMomentRestrictedSource CenteredMomentChildAssembly CenteredMomentSmooth CenteredMomentFirstSectors RayFourExpansion CenteredMomentLogDyadic CenteredMomentConjugateWindow
local notation "O" => ActualEisensteinCubic.O

theorem star_logAnnulus (x : ℝ) : star (logAnnulus x)=logAnnulus x := by
  simp only [logAnnulus,Complex.star_def,Complex.conj_ofReal]

theorem star_logAnnulus_column (u t : ℝ) :
    star (columnPhase logAnnulus u t)=columnPhase logAnnulus u (-t) := by
  rw [star_columnPhase]
  simp only [star_logAnnulus]

end SevenEighths.CenteredMomentSecondWindowSource

end

end OAI
