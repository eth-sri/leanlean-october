/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Descriptive.BFSeparation

@[expose] public section

universe u v

namespace FirstOrder.Language

open Cardinal Set MeasureTheory

variable {L : Language.{u, v}} [L.IsRelational]

/-- `K` is **back-and-forth scattered**: for every level `η < ω₁`, the restriction of
`CodeBFEquiv η` to `K` has countably many classes.  The count is of classes of the restricted
relation, not of codes; the relation is this library's `CodeBFEquiv η` (single-element
back-and-forth steps from the empty tuples), and no comparison with other hierarchies of
infinitary equivalence is made. -/
def BFScattered (K : Set (StructureSpace L)) : Prop :=
  ∀ η : Ordinal.{0}, η < Ordinal.omega 1 →
    Countable (Quotient ((codeBFEquivSetoid L η).comap (Subtype.val : K → StructureSpace L)))

/-- **The off-diagonal of a pairwise non-isomorphic set of codes has no isomorphic pair.**  The
hypothesis is the antichain clause of `HasPerfectAntichainOn`. -/
theorem not_structureIso_of_mem_offDiag {P : Set (StructureSpace L)}
    (hP : ∀ x ∈ P, ∀ y ∈ P, (structureIsoSetoid L).r x y → x = y) :
    ∀ p ∈ P.offDiag, ¬ (structureIsoSetoid L).r p.1 p.2 :=
  by grind

omit [L.IsRelational] in
/-- The space of codes is Hausdorff for every language (a product of discrete spaces); with
countably many relation symbols this also follows from the Polish instance. -/
private theorem t2Space_structureSpace : T2Space (StructureSpace L) :=
  inferInstanceAs (T2Space (StructureSpaceOn L ℕ))

attribute [local instance] t2Space_structureSpace

/-- **One back-and-forth level separates an analytic antichain**: for an analytic set `P` of
pairwise non-isomorphic codes there is `η < ω₁` at which no two distinct points of `P` are
back-and-forth equivalent.  This is `exists_uniform_bfSeparation` for the off-diagonal of `P`,
and the level is the one it returns.  No countability of the relation symbols is assumed. -/
theorem exists_forall_not_codeBFEquiv_of_analyticSet {P : Set (StructureSpace L)}
    (hP : AnalyticSet P) (hanti : ∀ x ∈ P, ∀ y ∈ P, (structureIsoSetoid L).r x y → x = y) :
    ∃ η : Ordinal.{0}, η < Ordinal.omega 1 ∧
      ∀ x ∈ P, ∀ y ∈ P, x ≠ y → ¬ CodeBFEquiv η x y := by
  obtain ⟨η, hη, hsep⟩ :=
    exists_uniform_bfSeparation hP.offDiag (not_structureIso_of_mem_offDiag hanti)
  exact ⟨η, hη, by simp_all⟩

/-- Cantor space is uncountable. -/
private theorem not_countable_natBool : ¬ Countable (ℕ → Bool) := by
  rw [← Cardinal.mk_le_aleph0_iff, not_le]
  simp [Cardinal.aleph0_lt_continuum]

/-- **No Cantor antichain on a back-and-forth scattered set**, for every relational language:
the range of a Cantor antichain is analytic, so one level `η < ω₁` separates its points
(`exists_forall_not_codeBFEquiv_of_analyticSet`), and the class map at that level injects Cantor
space into the countable quotient of the restriction to `K`.  No countability of the relation
symbols and no definability of `K` is assumed. -/
theorem not_hasCantorAntichainOn_of_bfScattered {K : Set (StructureSpace L)}
    (hK : BFScattered K) : ¬ HasCantorAntichainOn (structureIsoSetoid L) K := by
  rintro ⟨f, hcont, hmem, hineq⟩
  -- `PolishSpace (ℕ → Bool)` does not synthesize; both parents do
  have : PolishSpace (ℕ → Bool) := PolishSpace.mk
  have hanti : ∀ x ∈ range f, ∀ y ∈ range f, (structureIsoSetoid L).r x y → x = y := by
    grind
  obtain ⟨η, hη, hsep⟩ :=
    exists_forall_not_codeBFEquiv_of_analyticSet (analyticSet_range_of_polishSpace hcont) hanti
  -- the class map at level `η` is injective on the Cantor copy
  have := hK η hη
  refine not_countable_natBool (Function.Injective.countable
    (f := fun x ↦ (⟦⟨f x, hmem x⟩⟧ :
      Quotient ((codeBFEquivSetoid L η).comap (Subtype.val : K → StructureSpace L)))) ?_)
  intro x y hxy
  by_contra hne
  have hfne : f x ≠ f y := fun h ↦ hineq x y hne (h ▸ (structureIsoSetoid L).refl _)
  exact hsep _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hfne (Quotient.exact hxy)

/-- **Thinness from countably many back-and-forth classes at every level**: with countably many
relation symbols, a back-and-forth scattered set of codes contains no nonempty perfect set of
pairwise non-isomorphic codes.  Countability is used only to give the space of codes a complete
metric, in which a perfect antichain yields a Cantor antichain. -/
theorem isThinOn_of_bfScattered [Countable (Σ l, L.Relations l)] {K : Set (StructureSpace L)}
    (hK : BFScattered K) : IsThinOn (structureIsoSetoid L) K := by
  -- a complete metric compatible with the topology; the statement is unaffected
  let := TopologicalSpace.upgradeIsCompletelyMetrizable (StructureSpace L)
  exact IsThinOn.of_no_cantorAntichain (not_hasCantorAntichainOn_of_bfScattered hK)

end FirstOrder.Language
