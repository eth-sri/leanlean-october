module

public import OAI.NumberTheory.DirichletL.Moments.SecondSectorEnergy
public import OAI.NumberTheory.DirichletL.Moments.SecondFamilyTransport
public import OAI.NumberTheory.DirichletL.Moments.RestrictedWindow
public import OAI.NumberTheory.DirichletL.Moments.LogDyadic
public import OAI.NumberTheory.DirichletL.Moments.ConjugateWindow

@[expose] public section

namespace OAI


open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondWindowSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSecondHeightFamily
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedWindow CenteredMomentRestrictedSource
open CenteredMomentChildAssembly CenteredMomentSmooth CenteredMomentFirstSectors RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentConjugateWindow


theorem star_logAnnulus  x  : star (logAnnulus x)=logAnnulus x := by
  simp only [logAnnulus,Complex.star_def,Complex.conj_ofReal]

theorem star_logAnnulus_column  u t  :
    star (columnPhase logAnnulus u t)=columnPhase logAnnulus u (-t) := by
  rw [star_columnPhase]
  simp only [star_logAnnulus]

end SevenEighths.CenteredMomentSecondWindowSource



end OAI
