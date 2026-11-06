module

public import ADR11.Nonbinary.FourTaxa

/-!
# Proposition 3: four taxa

## Main results

* `proposition3`: for `|X| = 4`, `σ⁺` is not identifiable from `ℙ_σ` (that `σ⁻` is identifiable is
  `unrootedDist_eq_iff_four`).
* `f1_exists_sameUnrootedDist_not_sameRooted_four`: two of the rooted species trees of
  Section 4.1 with the same unrooted gene tree distribution, `(((a,b),c),d)` and `(((a,b),d),c)`.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Section 4.1: the binary trees `(((a,b),c),d)` and `(((a,b),d),c)` (with all internal edge
lengths `1`) have the same unrooted gene tree distribution (computed by `msc`) but different rooted
topologies. -/
theorem f1_exists_sameUnrootedDist_not_sameRooted_four :
    ∃ σ σ' : SpeciesTree (Fin 4), σ.IsBinary ∧ σ'.IsBinary ∧
      σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := by
  let σ₁ := SpeciesTree.ofLengths (X := Fin 4) (hierarchyOf {{0, 1}, {0, 1, 2}}) (fun _ => 1)
    (by decide) (by decide) (by decide) (by decide) (fun _ _ _ _ => one_pos)
  let σ₂ := SpeciesTree.ofLengths (X := Fin 4) (hierarchyOf {{0, 1}, {0, 1, 3}}) (fun _ => 1)
    (by decide) (by decide) (by decide) (by decide) (fun _ _ _ _ => one_pos)
  have h₁ : σ₁.clusters = hierarchyOf {{0, 1}, {0, 1, 2}} := rfl
  have h₂ : σ₂.clusters = hierarchyOf {{0, 1}, {0, 1, 3}} := rfl
  have hx : σ₂.length {0, 1} = σ₁.length {0, 1} := rfl
  exact ⟨σ₁, σ₂, by simp [SpeciesTree.IsBinary, h₁]; decide,
    by simp [SpeciesTree.IsBinary, h₂]; decide, four_ext (E := exp (-σ₁.length {0, 1})) (by msc h₁) (by msc h₂ with hx),
    fun hs => absurd (h₁.symm.trans (hs.1.trans h₂)) (by decide)⟩

/-- **Proposition 3** (`prop:4taxa`), second half. For `|X| = 4` taxa, `σ⁺` is not identifiable
from `ℙ_{σ⁺}`: two of the rooted trees of Section 4.1 with the same distribution have different
rooted topologies (`f1_exists_sameUnrootedDist_not_sameRooted_four`, relabelled to `X`). -/
theorem proposition3 (hX : Fintype.card X = 4) :
    ∃ σ σ' : SpeciesTree X, σ.IsBinary ∧ σ'.IsBinary ∧
      σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := by
  obtain ⟨τ, τ', hb, hb', hd, hn⟩ := f1_exists_sameUnrootedDist_not_sameRooted_four
  let e : Fin 4 ≃ X := (Fintype.equivFinOfCardEq hX).symm
  exact ⟨τ.relabel e, τ'.relabel e, (τ.isBinary_relabel_iff e).2 hb,
    (τ'.isBinary_relabel_iff e).2 hb', (SpeciesTree.unrootedDist_relabel_eq_iff τ τ' e).2 hd,
    fun hs => hn ((SpeciesTree.sameRootedMetricTree_relabel_iff τ τ' e).1 hs)⟩

end ADR11
