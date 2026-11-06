import RequestProject.BlockFamilyFactorComparison
import RequestProject.GenusMarkedSpineFamily
import RequestProject.Tac


/-!
# The actual spine factors embed in the simultaneous substituted group

This specializes the wide-amalgam comparison to the constructed finite spines.
The single-factor fillings and injectivity are supplied by the established
geometric spine construction, rather than required as new hypotheses.

-/

bwd

namespace FiniteChains.Davis.Genus

open RACG Mirror Comb PresModel BlockFamily

noncomputable section

variable {α Jr Sx : Type} (ρ : Jr ⊕ Sx → FreeGroup α)
  (q : Sx → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup α)
  (hrho : ∀ s, ρ (Sum.inr s) = commWord (u s) (finitePairs (q s)))

include hrho in
/-- The genuine fillings in each individual substitution. -/
theorem finiteSpineIndividualFillings :
    ∀ s, FilledF (oneRel ρ s)
      (fun _ : PUnit.{1} => familyFiniteSpineWordBlock q u s) :=
  fun s => finiteSpineWordBlock_filled _ _ _ (hrho s)

/-- The concrete map of an individual spine substitution into the simultaneous one. -/
def finiteSpineFactorToFamily (s : Sx) :
    IndividualGroup ρ (familyFiniteSpineWordBlock q u) s →*
      PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)) :=
  factorToFamily ρ _
    (familyFiniteSpineWordBlock_filled ρ q u hrho) s


/-- Every actual individual spine factor embeds, for an arbitrary family of genera. -/
theorem finiteSpineFactorToFamily_injective s :
    Function.Injective (finiteSpineFactorToFamily ρ q u hrho s) :=
  factorToFamily_injective ρ (familyFiniteSpineWordBlock q u)
    _
    _
    (fun t => finiteSpineWordBlock_injective _ _ _ (hrho t)) s

/-- The coefficient inclusion of an actual individual spine factor. -/
def finiteSpineFactorRingHom (s : Sx) :=
  MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFactorToFamily ρ q u hrho s)
