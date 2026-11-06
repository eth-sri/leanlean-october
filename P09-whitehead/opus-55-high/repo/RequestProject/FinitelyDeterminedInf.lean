import RequestProject.SubgroupCompactness


/-!
# Finitely determined requirements pass to intersections of chains

The minimality step of Section 2 needs that, at the intersection of a decreasing chain of
normal subgroups all of which satisfy the requirements, no requirement can fail: "any
finite list of membership answers agrees with some member".

This file proves that for an arbitrary finitely determined family of requirements
(`FinitelyDetermined`, see `RequestProject/SubgroupCompactness.lean`), so that the
hypothesis `sat_sInf_chain` of `FiniteChains.NecessityInputs` is a theorem for the Fox
requirements of Section 2.
-/

namespace FiniteChains

variable {G : Type*} [Group G]

/-- A finite subset of a nonempty chain has a lower bound inside the chain. -/
theorem exists_lower_bound_of_chain {C : Set (Subgroup G)} (hC : IsChain (· ≤ ·) C)
    (hne : C.Nonempty) (T : Finset (Subgroup G)) (hT : ↑T ⊆ C) :
    ∃ N ∈ C, ∀ x ∈ T, N ≤ x := by
  classical
  induction T using Finset.induction with
  | empty => aesop
  | insert a T _ ih =>
      have hTsub : ↑T ⊆ C := by grind
      have haC : a ∈ C := by grind
      obtain ⟨N, hNC, hN⟩ := ih hTsub
      rcases eq_or_ne N a with rfl | hne'
      · grind
      · rcases hC hNC haC hne' with hle | hle
        · grind
        grind

/-- **The requirements pass to intersections of decreasing chains.**  If every requirement
depends on finitely many membership decisions, and if every member of a nonempty chain of
subgroups satisfies all requirements, then so does the intersection of the chain. -/
theorem sat_sInf_of_finitelyDetermined {ι : Type*} (Sat : Subgroup G → ι → Prop)
    (det : FinitelyDetermined Sat) {C : Set (Subgroup G)} (hC : IsChain (· ≤ ·) C)
    (hne : C.Nonempty) (hsat : ∀ N ∈ C, ∀ v, Sat N v) v : Sat (sInf C) v := by
  classical
  cases' det v with F hF
  -- for each element of `F` missing from the intersection, a member of the chain missing it
  have hchoice : ∀ g, ∃ N : Subgroup G, N ∈ C ∧ (g ∉ sInf C → g ∉ N) := by
    intro g
    by_cases hg : g ∈ sInf C
    · aesop
    simp_all
  choose wit hwitC hwit using hchoice
  obtain ⟨N, hNC, hNle⟩ :=
    exists_lower_bound_of_chain hC hne (F.image wit)
      (by
        grind)
  have hagree : ∀ g ∈ F, (g ∈ sInf C ↔ g ∈ N) := by
    intro g hg
    refine ⟨by simp_all, fun hmem => ?_⟩
    by_contra hcon
    exact hwit g hcon (by aesop)
  exact (hF _ N hagree).2 (hsat N hNC v)
