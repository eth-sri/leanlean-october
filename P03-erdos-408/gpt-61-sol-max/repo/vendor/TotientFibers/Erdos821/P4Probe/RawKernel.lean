module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos821.P3Edge.NormOsc

public import Erdos821.P4Probe.RawLabels
public import Erdos821.P4Probe.FiniteSchur

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

def rawTransition (P : PrimeGroups) (J ell )
    (a b : P.BigLabels (J + ell))  :=
  if (splitBigLabels P J ell a).1 = (splitBigLabels P J ell b).1
    then P.idealMass ((splitBigLabels P J ell b).2) else 0

section
variable (P : PrimeGroups) (J ell : ℕ) (hV : ∀ g, 0 < P.V g)
include P J ell hV

lemma rawTransition_nonneg      
     a b  : 0 ≤ rawTransition P J ell a b := by
  unfold rawTransition
  split_ifs
  · exact (idealMass_pos P ell hV _).le
  · exact le_rfl

lemma rawTransition_row      
     a  : ∑ b, rawTransition P J ell a b = 1 := by
  trans ∑ z : P.BigLabels J × P.BigLabels ell,
    if (splitBigLabels P J ell a).1 = z.1 then P.idealMass z.2 else 0
  · apply Fintype.sum_equiv (splitBigLabels P J ell)
    intro b
    rfl
  · rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp
    exact idealMass_sum P ell hV

lemma rawTransition_column      
     b  :
    (∑ a, P.idealMass a * rawTransition P J ell a b) = P.idealMass b := by
  trans ∑ z : P.BigLabels J × P.BigLabels ell,
    P.idealMass z.1 * P.idealMass z.2 *
      (if z.1 = (splitBigLabels P J ell b).1 then P.idealMass ((splitBigLabels P J ell b).2) else 0)
  · apply Fintype.sum_equiv (splitBigLabels P J ell)
    intro a
    rw [idealMass_split P J ell a]
    rfl
  · rw [Fintype.sum_prod_type]
    simp_rw [mul_ite, mul_zero]
    simp
    rw [← Finset.sum_mul, ← Finset.mul_sum, idealMass_sum P ell hV, mul_one]
    exact (idealMass_split P J ell b).symm

end

alias imaginaryPower_norm := _root_.Erdos821.P3Edge.norm_imaginaryPower

alias phase_norm := _root_.Erdos821.P3Edge.norm_phase

def rawPrefixKernel (P : PrimeGroups) (J ell ) (θ ζ : ℝ)
    (a b : P.BigLabels (J + ell))  :=
  (rawTransition P J ell a b : ℂ) *
    imaginaryPower (prefixProduct ((splitBigLabels P J ell a).1)) ζ *
    phase (θ * prefixProduct ((splitBigLabels P J ell a).1))

section
variable (P : PrimeGroups) (J ell : ℕ) (hV : ∀ g, 0 < P.V g) (θ ζ : ℝ)
include P J ell hV θ ζ

lemma rawPrefixKernel_norm      
       a b  :
    ‖rawPrefixKernel P J ell θ ζ a b‖ = rawTransition P J ell a b := by
  simp_all [rawPrefixKernel, imaginaryPower_norm, phase_norm, rawTransition_nonneg]

lemma rawPrefixKernel_normBound      
      :
    NormBound (P.idealMass (M := J + ell)) (rawPrefixKernel P J ell θ ζ) 1 := by
  apply finite_schur _ _ 1 (fun a => (idealMass_pos P (J + ell) hV a).le) (by norm_num)
  · intro a
    simp only [rawPrefixKernel_norm P J ell hV θ ζ]
    exact (rawTransition_row P J ell hV a).le
  grind [rawPrefixKernel_norm, rawTransition_column]

end

end
end Erdos821.P4Probe
