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
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyWidthFloor CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O

def remaining (M ε:ℝ)(k:ℕ):=count M ε-k
def lowerAt (a b M ε:ℝ)(k:ℕ):=CenteredMomentEnergyProfiles.lower a b (remaining M ε k)
def lengthAt (M B L ε:ℝ)(k:ℕ):=range M B L (remaining M ε k)

lemma lowerAt_pos  a b M ε (ha:0<a) k :0<lowerAt a b M ε k:=
  CenteredMomentEnergyProfiles.lower_pos a b ha _

lemma child_support  a b M ε  k (hk:k<count M ε):
    lowerAt a b M ε k=lowerAt a b M ε (k+1)/max 1 b:=by
  have he:remaining M ε k=remaining M ε (k+1)+1:=by unfold remaining;omega
  simp only [lowerAt,he,CenteredMomentEnergyProfiles.lower]

lemma child_length  M B L ε  k (hk:k<count M ε):
    lengthAt M B L ε k=step M B (lengthAt M B L ε (k+1)):=by
  have he:remaining M ε k=remaining M ε (k+1)+1:=by unfold remaining;omega
  simp only [lengthAt,he,range]

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

end SevenEighths.CenteredMomentEnergyWidthInduction

end

end OAI
