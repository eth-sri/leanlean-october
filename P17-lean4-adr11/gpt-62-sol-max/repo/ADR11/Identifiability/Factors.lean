module

public import ADR11.Trees.Hierarchy

@[expose] public section

namespace ADR11

open Finset Real
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Exponential of a rooted edge length, taking a missing edge to have length zero. -/
noncomputable def edgeFactor (σ : SpeciesTree X) (A : Finset X) : ℝ :=
  exp (-(if A ∈ σ.clusters then σ.length A else 0))

theorem edgeFactor_lt_one_iff (σ : SpeciesTree X) {A : Finset X} (hAu : A ≠ univ) :
    edgeFactor σ A < 1 ↔ A ∈ σ.clusters := by
  rw [edgeFactor, exp_lt_one_iff, neg_lt_zero]
  split_ifs <;> simp [*, σ.length_pos]

theorem edgeFactor_le_one (σ : SpeciesTree X) {A : Finset X} (hAu : A ≠ univ) :
    edgeFactor σ A ≤ 1 := by
  by_cases h : A ∈ σ.clusters
  · exact ((edgeFactor_lt_one_iff σ hAu).2 h).le
  · simp [edgeFactor, h]

theorem edgeFactor_eq_one_iff (σ : SpeciesTree X) {A : Finset X} (hAu : A ≠ univ) :
    edgeFactor σ A = 1 ↔ A ∉ σ.clusters := by
  rw [← edgeFactor_lt_one_iff σ hAu, not_lt]
  exact ⟨Eq.ge, (edgeFactor_le_one σ hAu).antisymm⟩

theorem unrooted_factor (σ : SpeciesTree X) {A : Finset X} (hAu : A ≠ univ)
    (hAc : Aᶜ ≠ univ) (hne : A ≠ Aᶜ) :
    exp (-σ.unrootedLength A) = edgeFactor σ A * edgeFactor σ Aᶜ := by
  rw [SpeciesTree.unrootedLength, show σ.clusters.filter (fun B => B ≠ univ ∧ (B = A ∨ B = Aᶜ)) =
      ({A, Aᶜ} : ClusterFamily X).filter (fun B => B ∈ σ.clusters ∧ B ≠ univ) from by
    grind,
    sum_filter, sum_pair hne, neg_add, exp_add]
  simp [edgeFactor, hAu, hAc]

theorem SpeciesTree.unrootedLength_eq_zero_iff (σ : SpeciesTree X) (A : Finset X) :
    σ.unrootedLength A = 0 ↔ A ∉ unroot σ.clusters := by
  rw [unrootedLength, sum_eq_zero_iff_of_nonneg (fun C h =>
    (σ.length_pos C (mem_filter.1 h).1 (mem_filter.1 h).2.1).le), mem_unroot]
  have := σ.length_pos
  grind

theorem SpeciesTree.SameUnrootedMetricTree.length_eq {σ τ : SpeciesTree X}
    (h : σ.SameUnrootedMetricTree τ) {A : Finset X} (hA : 2 ≤ #A) (hc : 2 ≤ #Aᶜ) :
    σ.unrootedLength A = τ.unrootedLength A := by
  have := h.1
  have := h.2
  grind [SpeciesTree.unrootedLength_eq_zero_iff]

end ADR11
