module

public import RequestProject.BlockFamilyFactorComparison
public import RequestProject.GenusMarkedSpineFamily

@[expose] public section

/-!
# The actual spine factors embed in the simultaneous substituted group

This specializes the wide-amalgam comparison to the constructed finite spines.
The single-factor fillings and injectivity are supplied by the established
geometric spine construction, rather than required as new hypotheses.

-/

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

variable (s : Sx)

/-- The concrete map of an individual spine substitution into the simultaneous one. -/
def finiteSpineFactorToFamily :=
  factorToFamily ρ _
    (familyFiniteSpineWordBlock_filled ρ q u hrho) s

@[simp] theorem finiteSpineFactorToFamily_mk
    (w : FreeGroup _) :
    finiteSpineFactorToFamily ρ q u hrho s (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map
        (individualGenEmb (Zt := fun t => SpinePresentationGen (q t)) s) w) := rfl

/-- Every actual individual spine factor embeds, for an arbitrary family of genera. -/
theorem finiteSpineFactorToFamily_injective :
    Function.Injective (finiteSpineFactorToFamily ρ q u hrho s) :=
  factorToFamily_injective ρ _
    _
    (finiteSpineIndividualFillings ρ q u hrho)
    (fun t => finiteSpineWordBlock_injective (oneRel ρ t) (q t) (u t) (hrho t)) s

/-- The coefficient inclusion of an actual individual spine factor. -/
def finiteSpineFactorRingHom :=
  MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFactorToFamily ρ q u hrho s)

end

end FiniteChains.Davis.Genus
