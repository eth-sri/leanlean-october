module

public import ADR11.SmallTrees
public import ADR11.Rootings.Proofs
public import ADR11.Trees.Classify

/-!
# Five taxa: common helpers

Helpers for the five-taxon arguments (Proposition 8, `ADR11.Identifiability.Proposition8`, and
Appendix C, `ADR11.Nonbinary.FiveTaxa`):

* `five_exp_bounds`: `0 < exp (-ℓ) < 1` for the length `ℓ` of an edge of a species tree;
* `five_unrootedLength_mem`, `five_unrootedLength_compl_mem`, `five_unrootedLength_both`: the
  length of a split `S | T` of the unrooted tree, when exactly one of `S`, `T`, or both, are
  clusters of the rooted tree;
* `five_length_eq`: a length is recovered from an affine relation in a power of `exp (-ℓ)`;
* `five_sameRootedMetricTree_of_lengths`: two species trees with the same hierarchy
  `hierarchyOf C` and the same lengths above the clusters of `C` have the same rooted metric
  tree.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `exp (-ℓ)` lies in `(0, 1)` for the length `ℓ` of an edge of a species tree. -/
theorem five_exp_bounds {H : Finset (Finset X)} {τ : SpeciesTree X} (h : τ.clusters = H)
    (A : Finset X) (hA : A ∈ H := by decide) (hAu : A ≠ univ := by decide) :
    0 < exp (-τ.length A) ∧ exp (-τ.length A) < 1 :=
  ⟨exp_pos _, Real.exp_lt_one_iff.2 (neg_lt_zero.2 (τ.length_pos A (h ▸ hA) hAu))⟩

/-- The length of the split `S | T` (`T = Sᶜ`) when `S` is a cluster and `T` is not. -/
theorem five_unrootedLength_mem (τ : SpeciesTree X) {S T : Finset X} (hST : Sᶜ = T)
    (hS : S ∈ τ.clusters) (hSu : S ≠ univ) (hT : T ∉ τ.clusters) :
    τ.unrootedLength S = τ.length S := by
  unfold SpeciesTree.unrootedLength
  rw [Finset.sum_eq_single_of_mem S (mem_filter.2 ⟨hS, hSu, Or.inl rfl⟩)]
  intro C hCf hCS
  obtain ⟨hC, -, hC'⟩ := mem_filter.1 hCf
  rcases hC' with rfl | rfl <;> grind

/-- The length of the split `S | T` (`T = Sᶜ`) when both `S` and `T` are clusters (the root lies
on the edge of the split). -/
theorem five_unrootedLength_both (τ : SpeciesTree X) {S T : Finset X} (hST : Sᶜ = T)
    (hS : S ∈ τ.clusters) (hSu : S ≠ univ) (hT : T ∈ τ.clusters) (hTu : T ≠ univ) :
    τ.unrootedLength S = τ.length S + τ.length T := by
  have hne : S ≠ T := by
    intro hST'
    obtain ⟨x, hx⟩ := τ.nonempty_of_mem S hS
    have hx' := hST' ▸ hx
    rw [← hST, mem_compl] at hx'
    grind
  rw [← Finset.sum_pair hne]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext C
  constructor <;> grind

/-- A length is determined by `A * exp (-ℓ) ^ n` with `A > 0`, `n ≠ 0`. -/
theorem five_length_eq {x y A : ℝ} (n : ℕ) (hn : n ≠ 0) (hA : 0 < A)
    (h : A * exp (-x) ^ n = A * exp (-y) ^ n) : x = y := by
  have := Real.exp_injective
    ((pow_left_inj₀ (exp_pos _).le (exp_pos _).le hn).1 (mul_left_cancel₀ hA.ne' h))
  linarith

/-- A member of `hierarchyOf C` with at least two elements, other than `univ`, lies in `C`. -/
theorem five_mem_of_mem_hierarchyOf {C : Finset (Finset X)} {A : Finset X}
    (hA : A ∈ hierarchyOf C) (h2 : 2 ≤ #A) (hu : A ≠ univ) : A ∈ C := by
  rcases mem_insert.1 hA with rfl | hA
  · grind
  rcases mem_union.1 hA with hA | hA
  · grind
  obtain ⟨x, -, rfl⟩ := mem_image.1 hA
  simp at h2

/-- Two species trees with the same hierarchy `hierarchyOf C` and the same lengths above the
clusters of `C` have the same rooted metric tree. -/
theorem five_sameRootedMetricTree_of_lengths {τ τ' : SpeciesTree X} {C : Finset (Finset X)}
    (h : τ.clusters = hierarchyOf C) (h' : τ'.clusters = hierarchyOf C)
    (hl : ∀ A ∈ C, τ.length A = τ'.length A) : τ.SameRootedMetricTree τ' :=
  ⟨h.trans h'.symm, fun A hA h2 hu => hl A (five_mem_of_mem_hierarchyOf (h ▸ hA) h2 hu)⟩

end ADR11
