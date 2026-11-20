module

public import RequestProject.OrderNerveRealizationPaths
public import Mathlib.Topology.CWComplex.Classical.Subcomplex

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- Points of the actual realization whose barycentric coordinates vanish outside a vertex subset. -/
def orderNerveRealizationSupported (P : Type) [PartialOrder P] (A : Set P) :=
  {x | ∀ p, p ∉ A → orderNerveRealizationCoordinates P x p = 0}

/-- A simplex supported on a vertex subset has its entire closed image supported there. -/
theorem orderNerveRealizationSimplex_supported {P : Type} [PartialOrder P] (A : Set P)
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (hs : ∀ i, s.obj i ∈ A) :
    Set.range (orderNerveRealizationSimplex P s) ⊆ orderNerveRealizationSupported P A := by
  rintro x ⟨z, rfl⟩ p hp
  have h := congrArg (fun k => k z)
    (orderNerveAffineRealization_simplex (fun q => if q = p then 1 else 0) s)
  change orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) p =
    orderNerveAffineSimplex (fun q => if q = p then 1 else 0) s z at h
  rw [h]
  have hn : ∀ i, s.obj i ≠ p := fun i he => hp (he ▸ hs i)
  simp [orderNerveAffineSimplex, hn]

section

variable (P : Type) [PartialOrder P] (A : Set P)

/-- The supported carrier is exactly the union of the open cells whose vertices are selected. -/
theorem orderNerveRealizationSupported_union :
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
      have hc := hx _ hi
      have hf := congrArg (fun k => k z)
        (orderNerveAffineRealization_simplex (fun q => if q = s.val.obj i then 1 else 0) s.val)
      change orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s.val z)
        _ =
        orderNerveAffineSimplex (fun q => if q = s.val.obj i then 1 else 0) s.val z at hf
      have hp := (orderNerveAffineSimplex_indicator_pos_iff s.val z hz _).mpr ⟨i, rfl⟩
      grind
    apply Set.mem_iUnion.mpr
    refine ⟨n, Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ?_⟩⟩
    rw [orderNerveCharacteristicMap_openCell]
    solve_by_elim

/-- A genuine Mathlib CW subcomplex selecting all simplices supported on a vertex subset. -/
noncomputable def orderNerveRealizationSubcomplex :=
  CWComplex.Subcomplex.mk' Set.univ (orderNerveRealizationSupported P A)
    (fun n => (setOf fun s : (nerve P).nonDegenerate n => ∀ i, s.val.obj i ∈ A))
    (by
      intro n s
      change orderNerveCharacteristicMap s.val '' Metric.closedBall 0 1 ⊆ _
      rw [orderNerveCharacteristicMap_closedCell]
      exact orderNerveRealizationSimplex_supported A s.val.val s.property)
    (by
      apply orderNerveRealizationSupported_union)

end

variable {P : Type} [PartialOrder P]

/-- Selecting more vertices enlarges the actual supported subcomplex. -/
theorem orderNerveRealizationSubcomplex_mono
    {A B : Set P} (h : A ⊆ B) :
    (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) ⊆
      orderNerveRealizationSubcomplex P B := by
  intro x hx p hp
  solve_by_elim

/-- The actual realization vertices have the expected indicator barycentric coordinates. -/
theorem orderNerveRealizationCoordinates_vertex (p q : P) :
    orderNerveRealizationCoordinates P (orderNerveRealizationVertex p) q =
      if p = q then 1 else 0 := by
  have h := congrArg (fun k => k default)
    (orderNerveAffineRealization_simplex (fun r => if r = q then 1 else 0) (ComposableArrows.mk₀ p))
  change orderNerveRealizationCoordinates P (orderNerveRealizationVertex p) q =
    orderNerveAffineSimplex.{0} (fun r => if r = q then 1 else 0) (ComposableArrows.mk₀ p) default at h
  simp [h, SimplexCategory.len_mk, orderNerveAffineSimplex, ContinuousMap.coe_mk, ComposableArrows.mk₀, Fintype.sum_unique, Functor.const_obj_obj, mul_ite, mul_one, mul_zero]

/-- A realization vertex belongs to the supported subcomplex exactly when it is selected. -/
theorem orderNerveRealizationVertex_mem_subcomplex
    (A : Set P) (p : P) :
    orderNerveRealizationVertex p ∈ orderNerveRealizationSubcomplex P A ↔ p ∈ A := by
  constructor
  · intro hx
    by_contra hp
    have h := hx p hp
    simp_all [orderNerveRealizationCoordinates_vertex]
  · intro hp q hq
    grind [orderNerveRealizationCoordinates_vertex]

end FiniteChains.Comb
