module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import OAI.NumberTheory.DirichletL.Energy.InputParentCapacity

public import OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionClipped

@[expose] public section

namespace OAI


open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceLowBranchGeometry
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDeletionBudget CenteredMomentEnergyReferenceDeletionCapacity


alias length_eq_max_log := _root_.OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity.length_eq_max_log

lemma slot_budgets (M total ell kappa:ℝ)(_hM:0≤M)(hell:0≤ell)(hk:3/4≤kappa)
    (hlarge:5*M/6≤total+ell)(hcap:total+ell+(6*kappa-1)*ell≤M):
    ell≤M/21 ∧ (6*kappa-1)*ell≤M/6:=by
  have hkell:7/2*ell≤(6*kappa-1)*ell:=mul_le_mul_of_nonneg_right (by linarith) hell
  constructor <;> nlinarith

theorem reflected_low (M short along ell z kappa xi reflected:ℝ)
    (hM:0≤M)(_hs:0≤short)(hsM:short≤M/4)(_hell:0≤ell)(_hz:0≤z)(hze:z≤ell)
    (hk:3/4≤kappa)(he:ell≤M/21)(hbudget:(6*kappa-1)*ell≤M/6)(hxi:0≤xi)
    (hhigh:5*M/6<short+max 0 along+z)
    (href:reflected≤max 0 (M-along+xi)):
    0<along ∧ reflected+short+z≤16*M/21+xi ∧
      reflected+short+6*kappa*z≤13*M/14+xi:=by
  have haz:0<along:=by
    grind
  rw [max_eq_right haz.le] at hhigh
  have hzbudget:(6*kappa-1)*z≤M/6:=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  grind

lemma reflected_low_admissible (M xi short reflected z kappa:ℝ)
    (hxi:xi≤M/14)(ht:reflected+short+z≤16*M/21+xi)
    (hc:reflected+short+6*kappa*z≤13*M/14+xi):
    reflected+short+z≤5*M/6 ∧ reflected+short+6*kappa*z≤M:=by
  constructor <;> linarith

end SevenEighths.CenteredMomentEnergyReferenceLowBranchGeometry



end OAI
