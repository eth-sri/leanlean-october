import RequestProject.OrderNerveRealizationPaths
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- Points of the actual realization whose barycentric coordinates vanish outside a vertex subset. -/
def orderNerveRealizationSupported P [PartialOrder P] (A : Set P) :=
  {x | ∀ p, p ∉ A → orderNerveRealizationCoordinates P x p = 0}

/-- A simplex supported on a vertex subset has its entire closed image supported there. -/
theorem orderNerveRealizationSimplex_supported {P} [PartialOrder P] A
    {n} (s : (nerve P).obj (Opposite.op n))
    (hs : ∀ i, s.obj i ∈ A) :
    Set.range (orderNerveRealizationSimplex P s) ⊆ orderNerveRealizationSupported P A := by
  rintro x ⟨z, rfl⟩ p hp
  have h := congrArg (· z)
    (orderNerveAffineRealization_simplex (if · = p then 1 else 0) s)
  change orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) p =
    orderNerveAffineSimplex (if · = p then 1 else 0) s z at h
  rw [h]
  have hn : ∀ i, s.obj i ≠ p := by grind
  simp [orderNerveAffineSimplex, hn]

/-- The supported carrier is exactly the union of the open cells whose vertices are selected. -/
theorem orderNerveRealizationSupported_union P [PartialOrder P] A :
    (⋃ (n) (s : {s : (nerve P).nonDegenerate n // ∀ i, s.val.obj i ∈ A}),
      orderNerveCharacteristicMap s.val '' Metric.ball 0 1) = orderNerveRealizationSupported P A := by
  apply Set.Subset.antisymm
  · intro x hx
    cases' Set.mem_iUnion.mp hx with n hn
    cases' Set.mem_iUnion.mp hn with s hx
    apply orderNerveRealizationSimplex_supported A s.val.val s.property
    exact (orderNerveCharacteristicMap_closedCell s.val ▸
      Set.image_mono Metric.ball_subset_closedBall hx)
  · intro x hx
    obtain ⟨n, s, z, hz, he⟩ := orderNerveRealization_interior_cover P x
    have hs : ∀ i, s.val.obj i ∈ A := by
      intro i
      by_contra hi
      have hc := hx _ hi
      have hf := congrArg (· z)
        (orderNerveAffineRealization_simplex (if · = s.val.obj i then 1 else 0) s.val)
      change orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s.val z)
        (s.val.obj i) =
        orderNerveAffineSimplex (if · = s.val.obj i then 1 else 0) s.val z at hf
      have hp := (orderNerveAffineSimplex_indicator_pos_iff s.val z hz _).mpr ⟨i, rfl⟩
      grind
    apply Set.mem_iUnion.mpr
    refine ⟨n, Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ?_⟩⟩
    rw [orderNerveCharacteristicMap_openCell]
    tauto

/-- A genuine Mathlib CW subcomplex selecting all simplices supported on a vertex subset. -/
noncomputable def orderNerveRealizationSubcomplex P [PartialOrder P] (A : Set P) :=
  CWComplex.Subcomplex.mk' Set.univ (orderNerveRealizationSupported P A)
    (fun n => (setOf fun s : (nerve P).nonDegenerate n => ∀ i, s.val.obj i ∈ A))
    (by
      intro n s
      change orderNerveCharacteristicMap s.val '' Metric.closedBall 0 1 ⊆ _
      rw [orderNerveCharacteristicMap_closedCell]
      exact orderNerveRealizationSimplex_supported A s.val.val s.property)
    (orderNerveRealizationSupported_union P A)

/-- Selecting more vertices enlarges the actual supported subcomplex. -/
theorem orderNerveRealizationSubcomplex_mono {P} [PartialOrder P]
    {A B} (h : A ⊆ B) :
    (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) ⊆
      orderNerveRealizationSubcomplex P B := by
  tauto

/-- The actual realization vertices have the expected indicator barycentric coordinates. -/
theorem orderNerveRealizationCoordinates_vertex {P} [PartialOrder P] p q :
    orderNerveRealizationCoordinates P (orderNerveRealizationVertex p) q =
      if p = q then 1 else 0 := by
  have h := congrArg (· default)
    (orderNerveAffineRealization_simplex (if · = q then 1 else 0)
      (n := ⦋0⦌) (ComposableArrows.mk₀ p))
  change orderNerveRealizationCoordinates P (orderNerveRealizationVertex p) q =
    orderNerveAffineSimplex.{0} (if · = q then 1 else 0)
      (n := ⦋0⦌) (ComposableArrows.mk₀ p) default at h
  simp [h, orderNerveAffineSimplex, ContinuousMap.coe_mk, ComposableArrows.mk₀]

/-- A realization vertex belongs to the supported subcomplex exactly when it is selected. -/
theorem orderNerveRealizationVertex_mem_subcomplex {P} [PartialOrder P]
    A p :
    orderNerveRealizationVertex p ∈ orderNerveRealizationSubcomplex P A ↔ p ∈ A := by
  constructor
  · intro hx
    by_contra hp
    have h := hx p hp
    simp_all [orderNerveRealizationCoordinates_vertex]
  · intro hp q hq
    have hne : p ≠ q := by grind
    rw [orderNerveRealizationCoordinates_vertex, if_neg hne]
