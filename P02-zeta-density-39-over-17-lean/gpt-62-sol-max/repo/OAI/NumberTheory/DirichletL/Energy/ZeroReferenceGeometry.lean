module
public import OAI.NumberTheory.DirichletL.Energy.ReferenceDivisors
public import OAI.NumberTheory.DirichletL.Energy.ReferenceLowBands

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyZeroReferenceGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
local notation "O"=>HeckeFamily.O

lemma low_or_reflected (M short along xi:ℝ)(hM:0≤M)(hs:short≤M/4)(_hxi:0≤xi)
    (hxiM:xi≤M/6):
    max 0 short+max 0 along≤5*M/6 ∨
      (0<along ∧ max 0 (M-along+xi)+max 0 short≤5*M/6):=by
  have hs0:max 0 short≤M/4:=max_le (by linarith) hs
  by_cases hl:max 0 short+max 0 along≤5*M/6
  · exact Or.inl hl
  · right
    have halong:0<along:=by
      by_contra hn
      rw [max_eq_left (le_of_not_gt hn)] at hl
      linarith
    refine ⟨halong,?_⟩
    rw [max_eq_right halong.le] at hl
    rcases le_total 0 (M-along+xi) with hh|hh
    · rw [max_eq_right hh]
      linarith
    · rw [max_eq_left hh]
      linarith

end SevenEighths.CenteredMomentEnergyZeroReferenceGeometry

end

end OAI
