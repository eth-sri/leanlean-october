module

public import Erdos821.P3Clean.PatternAmplitude
public import Erdos821.P3Clean.ProbabilitySchur

/-! Absolute control of signed ideal choices with a bounded local factor. -/

@[expose] public section

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

def idealMultiplierRaw (A : Model F P J m) (theta : ℝ)
    (w : Fin A.patternCount → P.BigLabels (J + F.ell) → P.BigLabels (J + F.ell) → P.BigAux J → ℂ)
    (a b : P.BigLabels (J + F.ell)) : ℂ :=
  ∑ v : Fin A.patternCount, ∑ u : P.BigAux J,
    if (A.pattern v).matchesBig a b then
      ((A.pattern v).bigAuxMass u * (A.pattern v).freshMass b : ℝ) *
        (A.pattern v).coefficient a b u * imaginaryPower ((A.pattern v).DBig a u) A.zeta *
        phase (theta * ((A.pattern v).DBig a u : ℝ)) * w v a b u else 0

theorem phase_norm (theta : ℝ) : ‖phase theta‖ = 1 := by
  have h2 : Complex.im (2 : ℂ) = 0 := rfl
  simp only [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re, h2, mul_zero, zero_mul, add_zero, sub_zero, Real.exp_zero]

theorem freshMass_nonneg (ν : Pattern P J F.ell m) (b : P.BigLabels (J + F.ell)) :
    0 ≤ ν.freshMass b := by
  apply Finset.prod_nonneg
  intro g _
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · simp
  · exact (mu_pos g.val _).le

theorem bigAuxMass_nonneg (ν : Pattern P J F.ell m) (u : P.BigAux J) :
    0 ≤ ν.bigAuxMass u := by
  apply Finset.prod_nonneg
  intro g _
  apply Finset.prod_nonneg
  intro i _
  exact (mu_pos g.val _).le

theorem idealMultiplierRaw_sub_one (A : Model F P J m) (theta : ℝ)
    (w : Fin A.patternCount → P.BigLabels (J + F.ell) → P.BigLabels (J + F.ell) → P.BigAux J → ℂ)
    (a b : P.BigLabels (J + F.ell)) :
    idealMultiplierRaw A theta w a b - A.idealRaw theta a b =
      idealMultiplierRaw A theta (fun v a b u => w v a b u - 1) a b := by
  simp only [idealMultiplierRaw, Model.idealRaw, ← Finset.sum_sub_distrib]
  grind

end Erdos821.P3Clean
