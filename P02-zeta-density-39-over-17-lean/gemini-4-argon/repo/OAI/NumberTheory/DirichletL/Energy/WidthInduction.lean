module
public import OAI.NumberTheory.DirichletL.Energy.WidthRanges
public import OAI.NumberTheory.DirichletL.Energy.WidthFloor
public import OAI.NumberTheory.DirichletL.Energy.StageReserveSchedule
public import OAI.NumberTheory.DirichletL.Energy.BandMonotonicity

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyWidthInduction
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyWidthFloor CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource

def remaining (M ε:ℝ)(k:ℕ):ℕ:=count M ε-k
def lowerAt (a b M ε:ℝ)(k:ℕ):ℝ:=CenteredMomentEnergyProfiles.lower a b (remaining M ε k)
def lengthAt (M B L ε:ℝ)(k:ℕ):ℝ:=range M B L (remaining M ε k)

lemma lowerAt_pos (a b M ε:ℝ)(ha:0<a)(k:ℕ):0<lowerAt a b M ε k:=
  CenteredMomentEnergyProfiles.lower_pos a b ha _

lemma child_support (a b M ε:ℝ)(k:ℕ)(hk:k<count M ε):
    lowerAt a b M ε k=lowerAt a b M ε (k+1)/max 1 b:=by
  have he:remaining M ε k=remaining M ε (k+1)+1:=by unfold remaining;omega
  simp only [lowerAt,he,CenteredMomentEnergyProfiles.lower]

lemma child_length (M B L ε:ℝ)(k:ℕ)(hk:k<count M ε):
    lengthAt M B L ε k=step M B (lengthAt M B L ε (k+1)):=by
  have he:remaining M ε k=remaining M ε (k+1)+1:=by unfold remaining;omega
  simp only [lengthAt,he,range]
