module

public import Erdos821.P4Bridge.Properties
public import Erdos821.P4Bridge.FiniteComparison

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Erdos821.P4Bridge
open Blueprint.Graph P4Probe
noncomputable section
variable {P : PrimeGroups} {J ell m : ℕ}

lemma sum_labels {R : Type*} [AddCommMonoid R] (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (H : P.BigLabels (J + ell) → R) :
    (∑ a, H a) = ∑ s : SharedRows ν, ∑ x : SideTuple ν block false,
      ∑ y : SideTuple ν block true, ∑ t : P.BigLabels ell, H (labelJoin ν block s x y t) := by
  calc
    _ = ∑ z, H ((labelSplit ν block).symm z) := by
      apply Fintype.sum_equiv (labelSplit ν block)
      intro a
      simp only [Equiv.symm_apply_apply]
    _ = _ := by simp only [Fintype.sum_prod_type]; rfl

abbrev sideWeight (ν : Pattern P J ell m) (block : P.BigGroup → Bool) (b : Bool) :=
  Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block b)

def orientedJoin (ν : Pattern P J ell m) (block : P.BigGroup → Bool) :
    (b : Bool) → SharedRows ν → SideTuple ν block b → SideTuple ν block (!b) →
      P.BigLabels ell → P.BigLabels (J + ell)
  | false => labelJoin ν block
  | true => fun s y x t => labelJoin ν block s x y t

/-- Average over the chosen side and the tail, fixing the shared rows and the other side. -/
def conditional (ν : Pattern P J ell m) (block : P.BigGroup → Bool) (b : Bool)
    (f : P.BigLabels (J + ell) → ℂ) (s : SharedRows ν) (y : SideTuple ν block (!b)) : ℂ :=
  ∑ x, ∑ t, (↑(sideWeight ν block b x * P.idealMass t) : ℂ) * f (orientedJoin ν block b s x y t)

abbrev conditionalF (ν : Pattern P J ell m) (block : P.BigGroup → Bool) := conditional ν block false
abbrev conditionalG (ν : Pattern P J ell m) (block : P.BigGroup → Bool) := conditional ν block true

lemma conditional_energy_le (ν : Pattern P J ell m) (block : P.BigGroup → Bool) (b : Bool)
    (hV : ∀ g, 0 < P.V g) (f : P.BigLabels (J + ell) → ℂ) :
    (∑ s, rowWeight (sharedRows ν) s * ∑ y, sideWeight ν block (!b) y *
        ‖conditional ν block b f s y‖ ^ 2) ≤ ∑ a, P.idealMass a * ‖f a‖ ^ 2 := by
  have hmean (s : SharedRows ν) y := mean_product_sq_le (sideWeight ν block b) P.idealMass
    (fun x => (sideWeight_pos hV _ x).le) (fun t => (idealMass_pos P ell hV t).le)
    (sideWeight_sum hV _) (idealMass_sum P ell hV) (fun x t => f (orientedJoin ν block b s x y t))
  refine (Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hmean s y) (sideWeight_pos hV _ y).le)
    (rowWeight_pos hV _ s).le)).trans_eq ?_
  rw [sum_labels ν block]
  apply Finset.sum_congr rfl
  intro s _
  cases b <;> simp only [orientedJoin,
    idealMass_labelJoin, sideWeight, Finset.mul_sum]
  · rw [Finset.sum_comm]
    repeat' (apply Finset.sum_congr rfl; intro i _)
    dsimp only [sideCounts, Bool.not]
    ring
  · repeat' (apply Finset.sum_congr rfl; intro i _)
    dsimp only [sideCounts, Bool.not]
    ring

lemma conditional_eq_tail (ν : Pattern P J ell m) (block : P.BigGroup → Bool) (b : Bool)
    (hV : ∀ g, 0 < P.V g) (f : P.BigLabels (J + ell) → ℂ)
    (s : SharedRows ν) (x : SideTuple ν block b) (y : SideTuple ν block (!b))
    (hf : ∀ x' t, f (orientedJoin ν block b s x' y t) = f (orientedJoin ν block b s x y t)) :
    conditional ν block b f s y = ∑ t, (P.idealMass t : ℂ) * f (orientedJoin ν block b s x y t) := by
  have hsum : (∑ x' : SideTuple ν block b, (sideWeight ν block b x' : ℂ)) = 1 := by
    exact_mod_cast sideWeight_sum hV (patternAuxCoordinates ν block b)
  unfold conditional
  simp_rw [hf, Complex.ofReal_mul, mul_assoc, ← Finset.mul_sum]
  rw [← Finset.sum_mul, hsum, one_mul]


end
end Erdos821.P4Bridge
