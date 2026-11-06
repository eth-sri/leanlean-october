module
public import Mathlib.Tactic

public import Erdos821.P4Probe.RawLabels

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

variable {P : PrimeGroups} {J ell m : ℕ}

def sharedPrefixProduct (ν : Pattern P J ell m) (a : P.BigLabels (J + ell))  :=
  ∏ g, ∏ i : Fin J, if i ∈ ν.changed g.val then 1 else (a g (ν.slot i)).val

section
variable (ν : Pattern P J ell m) (block : P.BigGroup → Bool) (a : P.BigLabels (J + ell)) (side : Bool) (u : P.BigAux J)


lemma DBig_split    
        :
    ν.DBig a u = sharedPrefixProduct ν a *
      selectedProduct ν block false u * selectedProduct ν block true u := by
  unfold Pattern.DBig sharedPrefixProduct selectedProduct
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  grind

lemma prefixProduct_split    
      :
    prefixProduct ((splitBigLabels P J ell a).1) = sharedPrefixProduct ν a *
      selectedEndpoint ν block false a * selectedEndpoint ν block true a := by
  unfold prefixProduct sharedPrefixProduct selectedEndpoint
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hs : ν.slot i = Fin.castAdd ell i := by apply Fin.ext; rfl
  grind [splitBigLabels]

lemma selectedProduct_pos    
        : 0 < selectedProduct ν block side u := by
  apply Finset.prod_pos
  intro g _
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact (P.prime g.val _ (u g i).property).pos
  · exact Nat.zero_lt_one

end

end
end Erdos821.P4Probe
