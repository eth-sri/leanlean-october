import Mathlib


/-!
# Group rings of torsion-free abelian groups are integral domains

Lemma 2.1 of the paper is applied with `H ◁ Q` torsion-free abelian; its proof
uses that the coefficient ring `k[H]` is an integral domain.  This file proves
that statement in Lean, with no finiteness assumption on `H`:

* a torsion-free abelian group has the `UniqueSums` (resp. `UniqueProds`)
  property, because every pair of finite subsets lives in a finitely generated
  subgroup, which is free abelian of finite rank, hence orderable
  (`FiniteChains.uniqueSums_of_isAddTorsionFree`,
  `FiniteChains.uniqueProds_of_isMulTorsionFree`);
* consequently `k[H]` has no zero divisors and is an integral domain for any
  integral domain `k` (`FiniteChains.monoidAlgebra_isDomain`), in particular for
  `k = ℤ` and `k = 𝔽ₚ`, the two cases used in the paper.
-/

namespace FiniteChains

open scoped Classical in
/-- **A torsion-free abelian group has unique sums.**  Two nonempty finite subsets always
contain a pair whose sum is achieved only once. -/
theorem uniqueSums_of_isAddTorsionFree (A : Type*) [AddCommGroup A] [IsAddTorsionFree A] :
    UniqueSums A := by
  constructor
  intro S T hS hT
  -- the finitely generated subgroup containing both finite sets
  set G : AddSubgroup A := AddSubgroup.closure ((S ∪ T : Finset A) : Set A) with hG
  have hSG : ∀ a ∈ S, a ∈ G := by aesop
  have hTG : ∀ b ∈ T, b ∈ G := by aesop
  set S' : Finset G := S.subtype (· ∈ G) with hS'
  set T' : Finset G := T.subtype (· ∈ G) with hT'
  have hS'ne : S'.Nonempty := by
    cases' hS with a ha
    exact ⟨⟨a, hSG a ha⟩, by simp_all⟩
  have hT'ne : T'.Nonempty := by
    cases' hT with b hb
    exact ⟨⟨b, hTG b hb⟩, by simp_all⟩
  obtain ⟨a0, ha0, b0, hb0, huniq⟩ := UniqueSums.uniqueAdd_of_nonempty hS'ne hT'ne
  refine ⟨(a0 : A), by simp_all,
    (b0 : A), by simp_all, ?_⟩
  intro a b ha hb hab
  have ha' : (⟨a, hSG a ha⟩ : G) ∈ S' := by simp_all
  have hb' : (⟨b, hTG b hb⟩ : G) ∈ T' := by simp_all
  have : ((⟨a, hSG a ha⟩ : G) + ⟨b, hTG b hb⟩) = a0 + b0 := by aesop
  cases' huniq ha' hb' this with h1 h2
  grind

/-- **A torsion-free abelian group has unique products** (multiplicative form). -/
theorem uniqueProds_of_isMulTorsionFree H [CommGroup H] [IsMulTorsionFree H] :
    UniqueProds H := by
  haveI : UniqueSums (Additive H) := uniqueSums_of_isAddTorsionFree _
  haveI : UniqueProds (Multiplicative (Additive H)) := inferInstance
  tauto

/-- **The group ring of a torsion-free abelian group over an integral domain is an integral
domain.**  This is the hypothesis on the coefficient ring `k[H]` used in Lemma 2.1, for
`k = ℤ` and `k = 𝔽ₚ`. -/
theorem monoidAlgebra_isDomain k [CommRing k] [IsDomain k]
    H [CommGroup H] [IsMulTorsionFree H] :
    IsDomain (MonoidAlgebra k H) := by
  haveI : UniqueProds H := uniqueProds_of_isMulTorsionFree H
  infer_instance
