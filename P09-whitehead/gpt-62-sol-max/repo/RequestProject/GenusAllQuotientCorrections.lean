module

public import RequestProject.GenusQuotientMarkingCoefficients
public import RequestProject.FinsuppBasis

@[expose] public section

/-! Old-chain corrections with coefficients in the entire quotient deck
group. This keeps the polygon scalar in its original ring until every
spine and marking coordinate has been recovered. Awaiting Lean verification. -/
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)

abbrev QuotientMarkingGroup :=
  NamedQuotientGroup ρ q u

def allQuotientMarkingCorrection (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :
    (namedQuotientCover ρ q u).F →₀ ℤ :=
  (namedQuotientDeck ρ q u).faceChains g
    (chain2 (oldCoverToNamedQuotient q ρ u) (spineOldMarkingCorrection q i))

def allQuotientMarkingCorrections :
    ((QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((namedQuotientCover ρ q u).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => allQuotientMarkingCorrection q ρ u x.1 x.2)

theorem allQuotientMarkingCorrections_translate (g : QuotientMarkingGroup q ρ u)
    (c : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ) :
    allQuotientMarkingCorrections q ρ u (ReceivedTree.translateCellChain g c) =
      (namedQuotientDeck ρ q u).faceChains g
        (allQuotientMarkingCorrections q ρ u c) := by
  finsupp_basis c [ ReceivedTree.translateCellChain ]
  simp_all [ReceivedTree.translateCellChain, allQuotientMarkingCorrections, Finsupp.linearCombination_single, allQuotientMarkingCorrection, DeckAction.faceChains_mul]

theorem allQuotientMarkingCorrections_multiply
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (c : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ) :
    allQuotientMarkingCorrections q ρ u (ReceivedTree.multiplyCellChain c w) =
      Finsupp.linearCombination ℤ (fun g =>
        (namedQuotientDeck ρ q u).faceChains g
          (allQuotientMarkingCorrections q ρ u c)) w.coeff :=
  ReceivedTree.map_multiplyCellChain _ c _ (fun g => allQuotientMarkingCorrections_translate q ρ u g c) w

/-- The marked boundary detects the exact correction chain even when the
scalar has support outside the substituted subgroup. -/
theorem allQuotientMarkingCorrections_eq_of_boundary_multiple
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (c d : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ)
    (h : allQuotientSurfaceMarkingChains q ρ u c =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((namedQuotientDeck ρ q u).cellHom g)
        (allQuotientSurfaceMarkingChains q ρ u d)) w.coeff) :
    allQuotientMarkingCorrections q ρ u c =
      Finsupp.linearCombination ℤ (fun g =>
        (namedQuotientDeck ρ q u).faceChains g
          (allQuotientMarkingCorrections q ρ u d)) w.coeff := by
  erw [← allQuotientSurfaceMarkingChains_multiply] at h
  erw [allQuotientSurfaceMarkingChains_injective q ρ u h,
    allQuotientMarkingCorrections_multiply]

/-- Consequently the correction cancels from the relative difference as an
equality of actual two-chains, before applying old-cover faithfulness. -/
theorem allQuotientCorrection_cancel_difference
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (c d : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ)
    (x y : (namedQuotientCover ρ q u).F →₀ ℤ)
    (h : allQuotientSurfaceMarkingChains q ρ u c =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((namedQuotientDeck ρ q u).cellHom g)
        (allQuotientSurfaceMarkingChains q ρ u d)) w.coeff) :
    (x - allQuotientMarkingCorrections q ρ u c) -
      Finsupp.linearCombination ℤ (fun g =>
        (namedQuotientDeck ρ q u).faceChains g
          (y - allQuotientMarkingCorrections q ρ u d)) w.coeff =
    x - Finsupp.linearCombination ℤ (fun g =>
      (namedQuotientDeck ρ q u).faceChains g y) w.coeff := by
  have hs : Finsupp.linearCombination ℤ (fun g =>
        (namedQuotientDeck ρ q u).faceChains g
          (y - allQuotientMarkingCorrections q ρ u d)) w.coeff =
      Finsupp.linearCombination ℤ (fun g =>
        (namedQuotientDeck ρ q u).faceChains g y) w.coeff -
      Finsupp.linearCombination ℤ (fun g =>
        (namedQuotientDeck ρ q u).faceChains g
          (allQuotientMarkingCorrections q ρ u d)) w.coeff := by
    simp [Finsupp.linearCombination_apply, Finsupp.sum, map_sub, smul_sub, Finset.sum_sub_distrib]
  erw [hs, ← allQuotientMarkingCorrections_eq_of_boundary_multiple q ρ u w c d h]
  abel

variable (hrho : IsSpineRelator ρ q u)

theorem quotientMarkingCorrections_factor
    (c : (SpineReplacementGroup ρ q u × (Fin q × Bool)) →₀ ℤ) :
    quotientMarkingCorrections q ρ u hrho c =
      allQuotientMarkingCorrections q ρ u
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2)) c) := by
  simp_all [quotientMarkingCorrections, allQuotientMarkingCorrections, quotientMarkingCorrection, allQuotientMarkingCorrection] <;> abel

/-- Reflect the same polygon scalar on both parts of the named relation
vector at once. This avoids choosing unrelated scalars for faces and markings. -/
theorem quotientNamedCoefficients_reflect_multiple
    (β γ : SpineCoefficients ρ q u)
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (hf : Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2))
        ((ReceivedTree.cellCoordinates (SpinePresentationRel q)).symm (fun j => β (Sum.inl j))) =
      ReceivedTree.multiplyCellChain
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2))
          ((ReceivedTree.cellCoordinates (SpinePresentationRel q)).symm (fun j => γ (Sum.inl j)))) w)
    (hm : Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2))
        (singleReceivedSpineMarkingChain q ρ u β) =
      ReceivedTree.multiplyCellChain
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2))
          (singleReceivedSpineMarkingChain q ρ u γ)) w) :
    ∃ a : MonoidAlgebra ℤ (SpineReplacementGroup ρ q u),
      ∀ m, β m = a * γ m := by
  apply finiteSpineCoefficientMap_reflect_multiple ρ q u hrho β γ w
  intro m
  cases m with
  | inl j =>
      have h := congrArg (ReceivedTree.cellCoefficient j) hf
      simpa only [ReceivedTree.cellCoefficient_map_group,
        ReceivedTree.cellCoefficient_multiply, ReceivedTree.cellCoefficient_coordinates_symm,
        finiteSpineCoefficientMap] using h
  | inr i =>
      have h := congrArg (ReceivedTree.cellCoefficient i) hm
      simpa only [ReceivedTree.cellCoefficient_map_group,
        ReceivedTree.cellCoefficient_multiply, ReceivedTree.cellCoefficient_coordinates_symm,
        finiteSpineCoefficientMap] using h

end FiniteChains.Davis.Genus
