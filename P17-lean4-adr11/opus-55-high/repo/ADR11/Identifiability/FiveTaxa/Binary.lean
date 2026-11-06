module

public import ADR11.Identifiability.FiveTaxa.Classes
public import ADR11.Trees.Classify
public import ADR11.FiveTaxa.Balanced
public import ADR11.FiveTaxa.Caterpillar
public import ADR11.FiveTaxa.Pseudocaterpillar

/-!
# The binary rootings of `ab|cde, abc|de` and their classes of gene trees

The proof of Proposition 7 (`prop:cases`) names the taxa so that the unrooted species tree `ψ⁻`
has the splits `ab|cde` and `abc|de` (`U5 2`). The rooted tree `ψ⁺` is then one of the seven
binary rootings of `U5 2` (`binaryRootings5`): the four caterpillars `((((a,b),c),d),e)`,
`((((a,b),c),e),d)`, `((((d,e),c),b),a)`, `((((d,e),c),a),b)`, the two balanced trees
`(((a,b),c),(d,e))`, `((a,b),(c,(d,e)))`, and the pseudocaterpillar `(((a,b),(d,e)),c)`. This
module computes, for each of them, the classes of gene trees that the proof reads off the
distribution. The classes of the representatives of Section 4.2 come from the inequalities
(4)–(6) (`caterpillar_extremeClasses`, `balanced_extremeClasses`, `pseudocaterpillar_minClass`);
those of the other labellings by permuting labels (`cls_classes_of`).

* `p78_swap`, `p78_flip`: the relabellings `d ↔ e` and `a ↔ e, b ↔ d`.
* `p78_classes_cat1`, …, `p78_classes_cat3`, `p78_classes_bal1`: the least probable class and the
  class of the second smallest probability of the other labellings.
* `p78_exists_relabel_rep`: every binary 5-taxon species tree is, after relabelling, the balanced
  tree, the caterpillar or the pseudocaterpillar of Section 4.2 (the reduction in the proof of
  Proposition 8).
-/

@[expose] public section

namespace ADR11

open Finset

/-! ### Two relabellings of the taxa -/

/-- The relabelling `d ↔ e` of the taxa. -/
def p78_swap : Fin 5 ≃ Fin 5 := Equiv.swap 3 4

/-- The relabelling `a ↔ e`, `b ↔ d` of the taxa (`c` is fixed). -/
def p78_flip : Fin 5 ≃ Fin 5 := (Equiv.swap 0 4).trans (Equiv.swap 1 3)

/-! ### The classes of the seven rootings -/

variable {τ : SpeciesTree (Fin 5)}

/-- The classes of `((((a,b),c),e),d)`, by permuting the labels `d ↔ e` in
`caterpillar_extremeClasses`. -/
theorem p78_classes_cat1 (hτ : τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}, {0, 1, 2, 4}}) :
    cls_leastClass τ = {7, 8, 10, 11, 14, 15} ∧ cls_secondClass τ = {6, 9} :=
  cls_classes_of p78_swap caterpillar_extremeClasses hτ

/-- The classes of `((((d,e),c),b),a)`, by permuting the labels `a ↔ e, b ↔ d` in
`caterpillar_extremeClasses`. -/
theorem p78_classes_cat2 (hτ : τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}, {1, 2, 3, 4}}) :
    cls_leastClass τ = {5, 6, 8, 9, 11, 12} ∧ cls_secondClass τ = {7, 10} :=
  cls_classes_of p78_flip caterpillar_extremeClasses hτ

/-- The classes of `((((d,e),c),a),b)`, by permuting the labels `a ↔ e, b ↔ d` in
`p78_classes_cat1`. -/
theorem p78_classes_cat3 (hτ : τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}, {0, 2, 3, 4}}) :
    cls_leastClass τ = {5, 6, 8, 9, 11, 12} ∧ cls_secondClass τ = {14, 15} :=
  cls_classes_of p78_flip p78_classes_cat1 hτ

/-- The classes of `((a,b),(c,(d,e)))`, by permuting the labels `a ↔ e, b ↔ d` in
`balanced_extremeClasses`. -/
theorem p78_classes_bal1 (hτ : τ.clusters = hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}}) :
    cls_leastClass τ = {5, 6, 8, 9, 11, 12} ∧ cls_secondClass τ = {7, 10, 14, 15} :=
  cls_classes_of p78_flip balanced_extremeClasses hτ

/-! ### The reduction to the representatives (proof of Proposition 8) -/

/-- Every binary species tree on five taxa is, after relabelling, the balanced tree
`(((a,b),c),(d,e))`, the caterpillar `((((a,b),c),d),e)` or the pseudocaterpillar
`(((a,b),(d,e)),c)`. -/
theorem p78_exists_relabel_rep {X : Type*} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 5)
    (σ : SpeciesTree X) (hσ : σ.IsBinary) :
    ∃ e : X ≃ Fin 5, (σ.relabel e).clusters = balanced5 ∨ (σ.relabel e).clusters = caterpillar5 ∨
      (σ.relabel e).clusters = pseudocaterpillar5 := by
  obtain ⟨e, he⟩ := exists_equiv_unroot_eq_U5_two_of_isBinary hX σ hσ
  have hR := mem_binaryRootings5 _ ((σ.isBinary_relabel_iff e.symm).2 hσ) he
  suffices ∃ π : Fin 5 ≃ Fin 5, relabelFamily π (σ.relabel e.symm).clusters ∈
      ({balanced5, caterpillar5, pseudocaterpillar5} : Finset _) by
    obtain ⟨π, hπ⟩ := this
    refine ⟨e.symm.trans π, ?_⟩
    rwa [SpeciesTree.relabel_clusters, classify_relabelFamily_trans,
      ← SpeciesTree.relabel_clusters, mem_insert, mem_insert, mem_singleton] at hπ
  generalize (σ.relabel e.symm).clusters = R at hR ⊢
  simp [binaryRootings5, mem_insert, mem_singleton] at hR
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact ⟨1, by decide +kernel⟩
    | exact ⟨p78_swap, by decide +kernel⟩
    | exact ⟨p78_flip, by decide +kernel⟩
    | exact ⟨p78_swap * p78_flip, by decide +kernel⟩

end ADR11
