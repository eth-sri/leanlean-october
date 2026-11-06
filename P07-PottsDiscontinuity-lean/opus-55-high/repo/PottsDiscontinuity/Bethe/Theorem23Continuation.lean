module

public import Mathlib

/-! # Compact continuation of locally unique roots

This topological lemma isolates the compactness step in continuation. Its
hypotheses are local sections and local uniqueness, not global existence.
-/

public section

open Set Filter
open scoped Topology

namespace PottsDiscontinuity.Bethe

/-- On a connected parameter space, a closed relation with compact state space
and local unique sections has a unique root in every fiber if one fiber does.
This is the compact continuation principle used after the quantitative gap
bounds have made the admissible Bethe state region compact. -/
theorem unique_roots_of_compact_local_sections
    {T X : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (R : T → X → Prop) (hclosed : IsClosed {z : T × X | R z.1 z.2})
    (hlocal : ∀ t x, R t x → ∃ φ : T → X,
      ContinuousAt φ t ∧ φ t = x ∧ (∀ᶠ u in 𝓝 t, R u (φ u)) ∧
      ∃ W : Set (T × X), IsOpen W ∧ (t, x) ∈ W ∧
        ∀ u y, (u, y) ∈ W → R u y → y = φ u)
    (t₀ : T) (hbase : ∃! x, R t₀ x) : ∀ t, ∃! x, R t x := by
  let U := {t | ∃! x, R t x}
  have hprojection :=
    isClosedMap_fst_of_compactSpace _ hclosed
  have hopen : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨x, hx, huniq⟩ := ht
    obtain ⟨φ, hφcont, hφbase, hφroot, W, hWopen, hWbase, hWuniq⟩ := hlocal t x hx
    let B := Prod.fst '' ({z : T × X | R z.1 z.2} ∩ Wᶜ)
    have hBclosed :=
      isClosedMap_fst_of_compactSpace _ (hclosed.inter hWopen.isClosed_compl)
    have htB : t ∉ B := by
      grind
    filter_upwards [(hBclosed.isOpen_compl.mem_nhds htB), hφroot] with u hu hroot
    refine ⟨φ u, hroot, fun y hy => ?_⟩
    apply hWuniq u y _ hy
    by_contra hnot
    exact hu ⟨(u, y), ⟨hy, hnot⟩, rfl⟩
  have hopenCompl : IsOpen Uᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    by_cases hex : ∃ x, R t x
    · obtain ⟨x, hx⟩ := hex
      have hnotunique : ¬ ∀ y, R t y → y = x := by
        intro h
        exact ht ⟨x, hx, h⟩
      push Not at hnotunique
      obtain ⟨y, hy, hyx⟩ := hnotunique
      obtain ⟨φ, hφcont, hφbase, hφroot, _⟩ := hlocal t x hx
      obtain ⟨ψ, hψcont, hψbase, hψroot, _⟩ := hlocal t y hy
      have hne :=
        (hφcont.ne_iff_eventually_ne hψcont).mp (by grind)
      filter_upwards [hφroot, hψroot, hne] with u hφ hψ hne
      intro huniq
      obtain ⟨z, _, hz⟩ := huniq
      grind
    · have hnotproj : t ∉ Prod.fst '' {z : T × X | R z.1 z.2} := by
        grind
      filter_upwards [hprojection.isOpen_compl.mem_nhds hnotproj] with u hu
      rintro ⟨x, hx, _⟩
      exact hu ⟨(u, x), hx, rfl⟩
  have hUclosed : IsClosed U := by tauto
  intro t
  exact show t ∈ U from (IsClopen.eq_univ ⟨hUclosed, hopen⟩ ⟨t₀, hbase⟩) ▸ mem_univ t

end PottsDiscontinuity.Bethe
