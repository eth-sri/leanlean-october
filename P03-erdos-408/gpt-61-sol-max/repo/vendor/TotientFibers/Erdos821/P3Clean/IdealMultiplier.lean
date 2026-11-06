module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos821.P3Edge.NormOsc

public import Erdos821.P3Clean.PatternAmplitude
public import Erdos821.P3Clean.ProbabilitySchur

/-! Absolute control of signed ideal choices with a bounded local factor. -/

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

def idealMultiplierRaw (A : Model F P J m) (theta : ℝ)
    (w : Fin A.patternCount → P.BigLabels (J + F.ell) → P.BigLabels (J + F.ell) → P.BigAux J → ℂ)
    (a b : P.BigLabels (J + F.ell))  :=
  ∑ v : Fin A.patternCount, ∑ u : P.BigAux J,
    if (A.pattern v).matchesBig a b then
      ((A.pattern v).bigAuxMass u * (A.pattern v).freshMass b : ℝ) *
        (A.pattern v).coefficient a b u * imaginaryPower ((A.pattern v).DBig a u) A.zeta *
        phase (theta * ((A.pattern v).DBig a u : ℝ)) * w v a b u else 0

theorem phase_norm  theta  : ‖phase theta‖ = 1 := by solve_by_elim [_root_.Erdos821.P3Edge.norm_phase]

section
variable (ν : Pattern P J F.ell m)

theorem freshMass_nonneg    b  :
    0 ≤ ν.freshMass b := by
  apply Finset.prod_nonneg
  intro g _
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact zero_le_one
  · exact (mu_pos g.val _).le

theorem bigAuxMass_nonneg    u  :
    0 ≤ ν.bigAuxMass u := by
  apply Finset.prod_nonneg
  intro g _
  apply Finset.prod_nonneg
  intro i _
  exact (mu_pos g.val _).le

end

theorem idealMultiplierRaw_sub_one (A : Model F P J m)  theta 
    (w : Fin A.patternCount → P.BigLabels (J + F.ell) → P.BigLabels (J + F.ell) → P.BigAux J → ℂ)
    (a b : P.BigLabels (J + F.ell)) :
    idealMultiplierRaw A theta w a b - A.idealRaw theta a b =
      idealMultiplierRaw A theta (fun v a b u => w v a b u - 1) a b := by
  simp only [idealMultiplierRaw, Model.idealRaw, ← Finset.sum_sub_distrib]
  grind

end Erdos821.P3Clean
