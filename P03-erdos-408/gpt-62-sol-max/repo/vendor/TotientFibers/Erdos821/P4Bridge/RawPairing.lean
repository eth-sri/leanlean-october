module

public import Erdos821.P4Bridge.AveragedTests
public import Erdos821.P4Probe.RawModel

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Erdos821.P4Bridge
open Blueprint.Graph P4Probe
noncomputable section
variable {P : PrimeGroups} {J ell m : ℕ}

lemma rawPrefixKernel_join (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s s' : SharedRows ν) (a a' : SideTuple ν block false) (b b' : SideTuple ν block true)
    (t t' : P.BigLabels ell) (θ ζ : ℝ) :
    rawPrefixKernel P J ell θ ζ (labelJoin ν block s a b t) (labelJoin ν block s' a' b' t') =
      if (s, a, b) = (s', a', b') then
        (P.idealMass t' : ℂ) * imaginaryPower
          (rowProduct (sharedRows ν) s *
            Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block false) a *
            Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block true) b) ζ *
          phase (θ * (rowProduct (sharedRows ν) s *
            Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block false) a *
            Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block true) b))
      else 0 := by
  unfold rawPrefixKernel rawTransition
  rw [splitBigLabels_labelJoin, splitBigLabels_labelJoin]
  have hp : (prefixSplit ν block).symm (s, a, b) = (prefixSplit ν block).symm (s', a', b') ↔
      (s, a, b) = (s', a', b') := (prefixSplit ν block).symm.injective.eq_iff
  simp only [hp]
  have hprod := prefixProduct_labelJoin ν block s a b t
  rw [splitBigLabels_labelJoin] at hprod
  simp only at hprod
  rw [hprod]
  split_ifs <;> simp

lemma rawFullPair_states (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (θ ζ : ℝ) (f g : P.BigLabels (J + ell) → ℂ) :
    idealFullPair (rawPrefixKernel P J ell θ ζ) f g =
      ∑ s : SharedRows ν, ∑ a : SideTuple ν block false, ∑ b : SideTuple ν block true,
        ∑ t : P.BigLabels ell, ∑ t' : P.BigLabels ell,
          ((rowWeight (sharedRows ν) s *
            Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block false) a *
            Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block true) b *
            P.idealMass t * P.idealMass t' : ℝ) : ℂ) *
          star (f (labelJoin ν block s a b t)) * g (labelJoin ν block s a b t') *
          (imaginaryPower (rowProduct (sharedRows ν) s *
            Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block false) a *
            Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block true) b) ζ *
          phase (θ * (rowProduct (sharedRows ν) s *
            Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block false) a *
            Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block true) b))) := by
  unfold idealFullPair
  rw [sum_labels ν block]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro t _
  rw [sum_labels ν block]
  simp only [rawPrefixKernel_join, idealMass_labelJoin, Prod.mk.injEq, ite_and,
    mul_ite, ite_mul, mul_zero, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  apply Finset.sum_congr rfl
  intro t' _
  simp only [Complex.ofReal_mul]
  ring

def rawConditional (ν : Pattern P J ell m) (block : P.BigGroup → Bool) (C : ℕ) (θ ζ : ℝ)
    (f : SideTuple ν block true → ℂ) (g : SideTuple ν block false → ℂ) : ℂ :=
  Blueprint.Analytic.expect (analyticGroups P) (sideCounts ν block true) fun b =>
    Blueprint.Analytic.expect (analyticGroups P) (sideCounts ν block false) fun a =>
      star (f b) * g a *
      (Blueprint.Analytic.mellin
        ((Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block false) a : ℝ) *
          Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block true) b) ζ *
      Blueprint.Analytic.e ((θ * C) *
        Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block false) a *
        Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block true) b))

lemma rawFullPair_conditional (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (hV : ∀ g, 0 < P.V g) (θ ζ : ℝ) (f g : P.BigLabels (J + ell) → ℂ)
    (hf : ∀ s a a' b t, f (labelJoin ν block s a b t) = f (labelJoin ν block s a' b t))
    (hg : ∀ s a b b' t, g (labelJoin ν block s a b t) = g (labelJoin ν block s a b' t)) :
    idealFullPair (rawPrefixKernel P J ell θ ζ) f g =
      ∑ s : SharedRows ν, (rowWeight (sharedRows ν) s : ℂ) *
        Blueprint.Analytic.mellin (rowProduct (sharedRows ν) s) ζ *
        rawConditional ν block (rowProduct (sharedRows ν) s) θ ζ
          (conditionalF ν block f s) (conditionalG ν block g s) := by
  rw [rawFullPair_states]
  apply Finset.sum_congr rfl
  intro s _
  unfold rawConditional Blueprint.Analytic.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  have hF : conditionalF ν block f s b = ∑ t, (P.idealMass t : ℂ) * f (labelJoin ν block s a b t) :=
    conditional_eq_tail ν block false hV f s a b (fun a' t => hf s a' a b t)
  have hG : conditionalG ν block g s a = ∑ t, (P.idealMass t : ℂ) * g (labelJoin ν block s a b t) :=
    conditional_eq_tail ν block true hV g s b a (fun b' t => hg s a b' b t)
  rw [hF,hG]
  dsimp only [sideCounts]
  rw [multiplier_factor _ _ _ (rowProduct_pos _ s)
    (sideProduct_pos _ a) (sideProduct_pos _ b) θ ζ]
  simp only [star_sum, star_mul, Complex.star_def, Complex.conj_ofReal,
    Finset.mul_sum, Finset.sum_mul, Complex.ofReal_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t' _
  apply Finset.sum_congr rfl
  intro t _
  ring

end
end Erdos821.P4Bridge
