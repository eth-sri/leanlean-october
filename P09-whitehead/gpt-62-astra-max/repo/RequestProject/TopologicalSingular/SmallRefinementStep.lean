module

public import RequestProject.TopologicalSingular.SubdivisionSupport

@[expose] public section

namespace FiniteChains.SingularSubdivision
open TopologicalSingular
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

variable (U : ι → Set X)

structure SmallRefinementStage (n : ℕ) where
  smallMap : Chain X n →ₗ[ℤ] Chain X n
  homotopyMap : Chain X n →ₗ[ℤ] Chain X _
  small : ∀ c, smallMap c ∈ smallChains U n
  small_support : ∀ σ : Simplex X n,
    smallMap (Finsupp.single σ 1) ∈ subChains (Set.range σ) n
  homotopy_support : ∀ σ : Simplex X n,
    homotopyMap (Finsupp.single σ 1) ∈ subChains (Set.range σ) _
  on_boundary : ∀ c : Chain X _,
    boundary n (homotopyMap (boundary n c)) = boundary n c - smallMap (boundary n c)

section

variable (hcover : ∀ x, ∃ i, x ∈ U i)
include hcover

theorem all_zero_chains_small
    (c : Chain X 0) : c ∈ smallChains U 0 := by
  induction c using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add c d hc hd => aesop
  | single σ r =>
    obtain ⟨i, hi⟩ := hcover _
    apply single_mem_small U 0 σ r
    refine ⟨i, fun z => ?_⟩
    letI : Subsingleton (Domain 0) := inferInstanceAs (Subsingleton (stdSimplex ℝ (Fin 1)))
    rwa [show z = stdSimplex.vertex 0 from Subsingleton.elim _ _]

noncomputable def smallRefinementStageZero :
    SmallRefinementStage U 0 where
  smallMap := LinearMap.id
  homotopyMap := 0
  small := all_zero_chains_small U hcover
  small_support σ := single_mem_range_subChains σ 1
  homotopy_support _ := Submodule.zero_mem _
  on_boundary _ := by simp

end

/-- Correct the boundary first, then subdivide. The correction and homotopy stay
inside the image of the original simplex. -/
theorem smallRefinementStep_exists (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) {n : ℕ} (s : SmallRefinementStage U n)
    (σ : Simplex X _) :
    ∃ d : Chain X _, ∃ h : Chain X _,
      d ∈ smallChains U _ ∧ d ∈ subChains (Set.range σ) _ ∧
      h ∈ subChains (Set.range σ) _ ∧
      boundary _ h = Finsupp.single σ 1 - d - s.homotopyMap (boundary n (Finsupp.single σ 1)) := by
  let c := Finsupp.single σ 1 - s.homotopyMap (boundary n (Finsupp.single σ 1))
  have hc :=
    Submodule.sub_mem _ (single_mem_range_subChains σ 1)
      (carried_linearMap_mem_subChains s.homotopyMap s.homotopy_support _
        (boundary_mem_subChains _ n (single_mem_range_subChains σ 1)))
  have hbc : boundary n c = s.smallMap (boundary n (Finsupp.single σ 1)) := by
    dsimp only [c]
    simp [map_sub, s.on_boundary]
  have hsmallbc : boundary n c ∈ smallChains U n := by
    rw [hbc]
    exact s.small _
  obtain ⟨k, hk⟩ := exists_subdivision_small U hU hcover _ c
  simp only [← smallChains_const] at hc ⊢
  refine ⟨((subdivide (n + 1))^[k]) c - iteratedHomotopy n k (boundary n c),
    -iteratedHomotopy _ k c,
    Submodule.sub_mem _ hk (iteratedHomotopy_mem_small U k n hsmallbc),
    Submodule.sub_mem _ (iterated_subdivide_mem_small _ k (n + 1) hc)
      (iteratedHomotopy_mem_small _ k n (boundary_mem_small _ n hc)),
    Submodule.neg_mem _ (iteratedHomotopy_mem_small _ k (n + 1) hc), ?_⟩
  rw [map_neg, (eq_sub_of_add_eq (iteratedHomotopy_identity_succ k n c))]
  grind

end FiniteChains.SingularSubdivision
