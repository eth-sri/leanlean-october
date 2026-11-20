module

public import RequestProject.TopologicalSingular.RelativeSingularMaps
public import RequestProject.TopologicalSingular.SingularChainH0
public import RequestProject.TopologicalSingular.ContractibleSingularChains

@[expose] public section

namespace FiniteChains.TopologicalSingular
universe u
variable {X : Type u} [TopologicalSpace X]

variable (A : Set X)

/-- Exactness in a contractible subspace gives a filling that stays in it. -/
theorem contractible_supported_cycle_bounds [ContractibleSpace A]
    (n : ℕ) (c : Chain X _) (hc : c ∈ subChains A _)
    (hz : boundary n c = 0) :
    ∃ b : Chain X _, b ∈ subChains A _ ∧ boundary _ b = c := by
  obtain ⟨a, rfl⟩ := hc
  have ha : boundary n a = 0 := by
    apply map_inclusion_injective A n
    rw [map_boundary, hz, map_zero]
  obtain ⟨b, hb⟩ := contractible_cycle_bounds n a ha
  refine ⟨map _ _ b, ⟨b, rfl⟩, ?_⟩
  rw [← map_boundary, hb]

/-- The same support control holds in augmented degree zero. -/
theorem connected_supported_zero_bounds [PathConnectedSpace A]
    (c : Chain X 0) (hc : c ∈ subChains A 0) (hz : augmentation c = 0) :
    ∃ b : Chain X 1, b ∈ subChains A 1 ∧ boundary 0 b = c := by
  obtain ⟨a, rfl⟩ := hc
  have ha : a ∈ LinearMap.ker augmentation := by
    simp_all [augmentation_map]
  rw [ker_augmentation_eq_range_boundary] at ha
  obtain ⟨b, hb⟩ := ha
  refine ⟨map _ 1 b, ⟨b, rfl⟩, ?_⟩
  rw [← map_boundary, hb]

end FiniteChains.TopologicalSingular
