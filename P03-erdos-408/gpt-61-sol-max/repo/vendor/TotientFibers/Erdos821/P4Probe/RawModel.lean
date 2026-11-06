module
public import Mathlib.Tactic

public import Erdos821.P4Probe.RawKernel

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

def rawFamily (F : FixedData) (P : PrimeGroups) (J m : ℕ) : Family F P J m where
  count := 1
  pattern := fun _ => rawPattern P J F.ell m

lemma rawModel_idealRaw_eq  F   P   J m 
    (hV : ∀ g, 0 < P.V g)  θ ζ   a b  :
    ((rawFamily F P J m).model 1 ζ).idealRaw θ a b = rawPrefixKernel P J F.ell θ ζ a b := by
  have hcoef (u : P.BigAux J) : (rawPattern P J F.ell m).coefficient a b u = 1 := rfl
  have hs : (∑ u : P.BigAux J, ((rawPattern P J F.ell m).bigAuxMass u : ℂ)) = 1 := by
    exact_mod_cast bigAuxMass_sum (rawPattern P J F.ell m) hV
  dsimp only [rawFamily, Family.model, Model.idealRaw]
  simp only [Fin.sum_univ_one, raw_matches_prefix, raw_freshMass_tail, raw_DBig_prefix, hcoef, mul_one]
  unfold rawPrefixKernel rawTransition
  by_cases hp : (splitBigLabels P J F.ell a).1 = (splitBigLabels P J F.ell b).1
  · simp only [hp, ite_true, Complex.ofReal_mul]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, hs, one_mul]
  · simp [hp]

lemma rawModel_normBound  F   P   J m 
    (hV : ∀ g, 0 < P.V g)  θ ζ  :
    NormBound (P.idealMass (M := J + F.ell))
      (((rawFamily F P J m).model 1 ζ).idealRaw θ) 1 := Eq.mpr (congrArg (fun _a => Erdos821.Blueprint.Graph.NormBound P.idealMass _a 1) (funext fun a => funext (Erdos821.P4Probe.rawModel_idealRaw_eq F P J m hV θ ζ a))) (Erdos821.P4Probe.rawPrefixKernel_normBound P J F.ell hV θ ζ)

end
end Erdos821.P4Probe
