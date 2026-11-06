module

public import RequestProject.GenusQuotientMarkingCoefficients

@[expose] public section

/-! Old-chain corrections with coefficients in the entire quotient deck
group. This keeps the polygon scalar in its original ring until every
spine and marking coordinate has been recovered. Awaiting Lean verification. -/
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)

abbrev QuotientMarkingGroup :=
  Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)

def allQuotientMarkingCorrection (g : QuotientMarkingGroup q ρ u) (i : Fin q × Bool) :
    (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).F →₀ ℤ :=
  (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
    (chain2 (oldCoverToNamedQuotient q ρ u) (spineOldMarkingCorrection q i))

def allQuotientMarkingCorrections :
    ((QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ) →ₗ[ℤ]
      ((uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => allQuotientMarkingCorrection q ρ u x.1 x.2)

theorem allQuotientMarkingCorrections_translate (g : QuotientMarkingGroup q ρ u)
    (c : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ) :
    allQuotientMarkingCorrections q ρ u (ReceivedTree.translateCellChain g c) =
      (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
        (allQuotientMarkingCorrections q ρ u c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp [ReceivedTree.translateCellChain]
  | add c d hc hd =>
      simp only [ReceivedTree.translateCellChain, Finsupp.mapDomain_add, map_add] at hc hd ⊢
      erw [hc, hd]
  | single x n =>
      erw [ReceivedTree.translateCellChain, Finsupp.mapDomain_single]
      simp only [allQuotientMarkingCorrections, Finsupp.linearCombination_single,
        map_smul, allQuotientMarkingCorrection, DeckAction.faceChains_mul]

theorem allQuotientMarkingCorrections_multiply
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (c : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ) :
    allQuotientMarkingCorrections q ρ u (ReceivedTree.multiplyCellChain c w) =
      Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
          (allQuotientMarkingCorrections q ρ u c)) w.coeff := by
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w z hw hz => simp only [map_add, MonoidAlgebra.coeff_add, hw, hz]
  | single g n =>
      simp only [ReceivedTree.multiplyCellChain, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, MonoidAlgebra.coeffLinearEquiv_apply,
        MonoidAlgebra.coeff_single, Finsupp.linearCombination_single]
      erw [map_smul,
        allQuotientMarkingCorrections_translate]

/-- The marked boundary detects the exact correction chain even when the
scalar has support outside the substituted subgroup. -/
theorem allQuotientMarkingCorrections_eq_of_boundary_multiple
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (c d : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ)
    (h : allQuotientSurfaceMarkingChains q ρ u c =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).cellHom g)
        (allQuotientSurfaceMarkingChains q ρ u d)) w.coeff) :
    allQuotientMarkingCorrections q ρ u c =
      Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
          (allQuotientMarkingCorrections q ρ u d)) w.coeff := by
  erw [← allQuotientSurfaceMarkingChains_multiply] at h
  erw [allQuotientSurfaceMarkingChains_injective q ρ u h,
    allQuotientMarkingCorrections_multiply]

/-- Consequently the correction cancels from the relative difference as an
equality of actual two-chains, before applying old-cover faithfulness. -/
theorem allQuotientCorrection_cancel_difference
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (c d : (QuotientMarkingGroup q ρ u × (Fin q × Bool)) →₀ ℤ)
    (x y : (uCover (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).F →₀ ℤ)
    (h : allQuotientSurfaceMarkingChains q ρ u c =
      Finsupp.linearCombination ℤ (fun g => chain1
        ((univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).cellHom g)
        (allQuotientSurfaceMarkingChains q ρ u d)) w.coeff) :
    (x - allQuotientMarkingCorrections q ρ u c) -
      Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
          (y - allQuotientMarkingCorrections q ρ u d)) w.coeff =
    x - Finsupp.linearCombination ℤ (fun g =>
      (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g y) w.coeff := by
  have hs : Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
          (y - allQuotientMarkingCorrections q ρ u d)) w.coeff =
      Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g y) w.coeff -
      Finsupp.linearCombination ℤ (fun g =>
        (univDeck (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u)).faceChains g
          (allQuotientMarkingCorrections q ρ u d)) w.coeff := by
    clear h
    induction w using MonoidAlgebra.induction_linear with
    | zero => simp
    | add w z hw hz => erw [MonoidAlgebra.coeff_add, map_add, map_add, map_add, hw, hz]; abel
    | single g n => simp only [MonoidAlgebra.coeff_single, Finsupp.linearCombination_single, map_sub, smul_sub]
  erw [hs, ← allQuotientMarkingCorrections_eq_of_boundary_multiple q ρ u w c d h]
  abel

variable (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

theorem quotientMarkingCorrections_factor
    (c : (PresGroup (substPresF ρ (finiteSpineWordBlock q u)) × (Fin q × Bool)) →₀ ℤ) :
    quotientMarkingCorrections q ρ u hrho c =
      allQuotientMarkingCorrections q ρ u
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2)) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.mapDomain_add, hc, hd]
  | single x n =>
      simp only [Finsupp.mapDomain_single, quotientMarkingCorrections,
        allQuotientMarkingCorrections, Finsupp.linearCombination_single,
        quotientMarkingCorrection, allQuotientMarkingCorrection]

/-- Reflect the same polygon scalar on both parts of the named relation
vector at once. This avoids choosing unrelated scalars for faces and markings. -/
theorem quotientNamedCoefficients_reflect_multiple
    (β γ : NamedSpineRel q → MonoidAlgebra ℤ
      (PresGroup (substPresF ρ (finiteSpineWordBlock q u))))
    (w : MonoidAlgebra ℤ (QuotientMarkingGroup q ρ u))
    (hf : Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2))
        ((ReceivedTree.cellCoordinates (SpinePresentationRel q)).symm (fun j => β (Sum.inl j))) =
      ReceivedTree.multiplyCellChain
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2))
          ((ReceivedTree.cellCoordinates (SpinePresentationRel q)).symm (fun j => γ (Sum.inl j)))) w)
    (hm : Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2))
        ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => β (Sum.inr i))) =
      ReceivedTree.multiplyCellChain
        (Finsupp.mapDomain (fun x => (finiteSpineToQuotient ρ q u hrho x.1, x.2))
          ((ReceivedTree.cellCoordinates (Fin q × Bool)).symm (fun i => γ (Sum.inr i)))) w) :
    ∃ a : MonoidAlgebra ℤ (PresGroup (substPresF ρ (finiteSpineWordBlock q u))),
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
