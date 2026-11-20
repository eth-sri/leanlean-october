module

public import RequestProject.OrderNerveRealizationPaths
public import Mathlib.Topology.CWComplex.Classical.Subcomplex

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- Points of the actual realization whose barycentric coordinates vanish outside a vertex subset. -/
def orderNerveRealizationSupported (P : Type) [PartialOrder P] (A : Set P) :
    Set (orderNerveRealization P) :=
  {x | ∀ p, p ∉ A → orderNerveRealizationCoordinates P x p = 0}

/-- A simplex supported on a vertex subset has its entire closed image supported there. -/
theorem orderNerveRealizationSimplex_supported {P : Type} [PartialOrder P] (A : Set P)
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (hs : ∀ i, s.obj i ∈ A) :
    Set.range (orderNerveRealizationSimplex P s) ⊆ orderNerveRealizationSupported P A := by
  rintro x ⟨z, rfl⟩ p hp
  rw [orderNerveRealizationCoordinates_simplex]
  have hn : ∀ i, s.obj i ≠ p := fun i he => hp (he ▸ hs i)
  simp [orderNerveAffineSimplex, hn]

/-- The supported carrier is exactly the union of the open cells whose vertices are selected. -/
theorem orderNerveRealizationSupported_union (P : Type) [PartialOrder P] (A : Set P) :
    (⋃ (n : ℕ) (s : {s : (nerve P).nonDegenerate n // ∀ i, s.val.obj i ∈ A}),
      orderNerveCharacteristicMap s.val '' Metric.ball 0 1) = orderNerveRealizationSupported P A := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    obtain ⟨s, hx⟩ := Set.mem_iUnion.mp hn
    apply orderNerveRealizationSimplex_supported A s.val.val s.property
    exact (orderNerveCharacteristicMap_closedCell s.val ▸
      Set.image_mono Metric.ball_subset_closedBall hx)
  · intro x hx
    obtain ⟨n, s, z, hz, he⟩ := orderNerveRealization_interior_cover P x
    have hs : ∀ i, s.val.obj i ∈ A := by
      intro i
      by_contra hi
      have hc := hx (s.val.obj i) hi
      rw [← he, orderNerveRealizationCoordinates_simplex] at hc
      have hp := (orderNerveAffineSimplex_indicator_pos_iff s.val z hz (s.val.obj i)).mpr ⟨i, rfl⟩
      exact (ne_of_gt hp) hc
    apply Set.mem_iUnion.mpr
    refine ⟨n, Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ?_⟩⟩
    rw [orderNerveCharacteristicMap_openCell]
    tauto

/-- A genuine Mathlib CW subcomplex selecting all simplices supported on a vertex subset. -/
noncomputable def orderNerveRealizationSubcomplex (P : Type) [PartialOrder P] (A : Set P) :
    CWComplex.Subcomplex (Set.univ : Set (orderNerveRealization P)) :=
  CWComplex.Subcomplex.mk' Set.univ (orderNerveRealizationSupported P A)
    (fun n => (setOf fun s  => ∀ i, s.val.obj i ∈ A))
    (by
      intro n s
      change orderNerveCharacteristicMap s.val '' Metric.closedBall 0 1 ⊆ _
      rw [orderNerveCharacteristicMap_closedCell]
      exact orderNerveRealizationSimplex_supported A s.val.val s.property)
    (by
      solve_by_elim [orderNerveRealizationSupported_union])

/-- Selecting more vertices enlarges the actual supported subcomplex. -/
theorem orderNerveRealizationSubcomplex_mono {P : Type} [PartialOrder P]
    {A B : Set P} (h : A ⊆ B) :
    (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) ⊆
      orderNerveRealizationSubcomplex P B := by
  tauto

/-- The actual realization vertices have the expected indicator barycentric coordinates. -/
theorem orderNerveRealizationCoordinates_vertex {P : Type} [PartialOrder P] (p q : P) :
    orderNerveRealizationCoordinates P (orderNerveRealizationVertex p) q =
      if p = q then 1 else 0 :=
  orderNerveAffineRealization_vertex _ p

/-- A realization vertex belongs to the supported subcomplex exactly when it is selected. -/
theorem orderNerveRealizationVertex_mem_subcomplex {P : Type} [PartialOrder P]
    (A : Set P) (p : P) :
    orderNerveRealizationVertex p ∈ orderNerveRealizationSubcomplex P A ↔ p ∈ A := by
  constructor
  · intro hx
    by_contra hp
    have h := hx p hp
    simp_all [orderNerveRealizationCoordinates_vertex]
  · intro hp q hq
    have hne : p ≠ q := fun he => hq (he ▸ hp)
    rw [orderNerveRealizationCoordinates_vertex, if_neg hne]

end FiniteChains.Comb
