module

public import Mathlib

/-! # Compact continuation of locally unique roots

This topological lemma isolates the compactness step in continuation. Its
hypotheses are local sections and local uniqueness, not global existence.
-/

@[expose] public section

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
  
  let U  := {t | ∃! x, R t x}
  
  have hopen : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨x, hx, huniq⟩ := ht
    obtain ⟨φ, hφcont, hφbase, hφroot, W, hWopen, hWbase, hWuniq⟩ := hlocal t x hx
    let B := Prod.fst '' ({z : T × X | R z.1 z.2} ∩ Wᶜ)
    
    have htB : t ∉ B := by
      grind
    have hnear  := (isClosedMap_fst_of_compactSpace _ (hclosed.inter hWopen.isClosed_compl)).isOpen_compl.mem_nhds htB
    filter_upwards [hnear, hφroot] with u hu hroot
    refine ⟨φ u, hroot, fun y hy => ?_⟩
    apply hWuniq u y _ hy
    by_contra hnot
    exact hu ⟨(u, y), ⟨hy, hnot⟩, rfl⟩
  
  
  have hU  := IsClopen.eq_univ ⟨ { isOpen_compl := (by
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
                                                        have hne  :=
                                                          (hφcont.ne_iff_eventually_ne hψcont).mp (by rw [hφbase, hψbase]; exact hyx.symm)
                                                        filter_upwards [hφroot, hψroot, hne] with u hφ hψ hne
                                                        intro huniq
                                                        obtain ⟨z, _, hz⟩ := huniq
                                                        exact hne ((hz _ hφ).trans (hz _ hψ).symm)
                                                      · 
                                                        filter_upwards [(isClosedMap_fst_of_compactSpace _ hclosed).isOpen_compl.mem_nhds (by
                                                                                                             grind)] with u hu
                                                        rintro ⟨x, hx, _⟩
                                                        exact hu ⟨(u, x), hx, rfl⟩) } , hopen⟩ ⟨t₀, hbase⟩
  intro t
  exact show t ∈ U from hU ▸ mem_univ t

end PottsDiscontinuity.Bethe
