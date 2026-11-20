module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SubdivisionRealization
public import RequestProject.TopologicalSingular.BarycentricMesh
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Module.LinearMap.End

@[expose] public section

/-! # Sufficient subdivision makes every singular chain small

Small means that every simplex in the support is contained in one member
of the given cover. Compactness of the standard simplex and the proved
mesh estimate supply a finite subdivision exponent. No excision premise
is introduced.
-/

namespace FiniteChains.SingularSubdivision

open Set Topology TopologicalSingular AffineVertexChains

universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

variable (U : ι → Set X)

variable (n : ℕ)

noncomputable def smallChains : Submodule ℤ (Chain X n) :=
  Finsupp.supported ℤ ℤ {σ | ∃ i, ∀ z, σ z ∈ U i}

theorem single_mem_small (σ : Simplex X n) (r : ℤ)
    (hσ : ∃ i, ∀ z, σ z ∈ U i) : Finsupp.single σ r ∈ smallChains U n :=
  Finsupp.single_mem_supported ℤ r hσ

theorem boundary_mem_small {c : Chain X _}
    (hc : c ∈ smallChains U _) : boundary n c ∈ smallChains U n := by
  apply VertexChains.map_mem_of_supported _ _ (boundary n) ?_ hc
  rintro σ ⟨j, hj⟩
  rw [boundary_single]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  solve_by_elim [single_mem_small]

theorem push_mem_small {k : ℕ} (σ : Simplex X k)
    (hσ : ∃ i, ∀ z, σ z ∈ U i) (l : ℕ) (c : Chain (Domain k) l) :
    TopologicalSingular.map σ l c ∈ smallChains U l := by
  obtain ⟨j, hj⟩ := hσ
  induction c using Finsupp.induction with
  | zero => simp
  | single_add τ r c _ _ ih =>
    rw [map_add, map_single]
    exact Submodule.add_mem _ (single_mem_small U l _ r ⟨j, fun z => hj (τ z)⟩) ih

theorem fromModel_mem_small {k l : ℕ} (m : Chain (Domain k) l)
    {c : Chain X k} (hc : c ∈ smallChains U k) : fromModel m c ∈ smallChains U l := by
  apply VertexChains.map_mem_of_supported _ _ (fromModel m) ?_ hc
  simp_all [fromModel_single, push_mem_small]

section

variable (n : ℕ) {c : Chain X n} (hc : c ∈ smallChains U n)
include hc

theorem subdivide_mem_small : subdivide n c ∈ smallChains U n :=
  by solve_by_elim [fromModel_mem_small]

theorem homotopy_mem_small : homotopy n c ∈ smallChains U _ :=
  by solve_by_elim [fromModel_mem_small]

end

theorem iterated_subdivide_mem_small (k n : ℕ) {c : Chain X n}
    (hc : c ∈ smallChains U n) : ((subdivide n)^[k]) c ∈ smallChains U n := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    apply subdivide_mem_small <;> assumption

theorem iterated_subdivide_small_of_le {k l : ℕ} (hkl : k ≤ l)
    (n : ℕ) {c : Chain X n} (hc : ((subdivide n)^[k]) c ∈ smallChains U n) :
    ((subdivide n)^[l]) c ∈ smallChains U n := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [Nat.add_comm k a, Function.iterate_add_apply]
  apply iterated_subdivide_mem_small <;> assumption

theorem standardVertices_mesh (n : ℕ) : MeshBound (standardVertices n) 1 := by
  intro i j
  exact (Metric.dist_le_diam_of_mem (bounded_stdSimplex (Fin (n + 1)))
    (standardVertices n i).property (standardVertices n j).property).trans diam_stdSimplex_le

variable (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
include hU

theorem exists_subdivision_small_single
    (n : ℕ) (σ : Simplex X n) (hcover : ∀ z, ∃ i, σ z ∈ U i) :
    ∃ k, ((subdivide n)^[k]) (Finsupp.single σ 1) ∈ smallChains U n := by
  classical
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    isCompact_univ
    (fun i => (hU i).preimage σ.continuous)
    (by
      intro z _ <;> simp_all)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ (shrink_lt_one n)
  refine ⟨k, ?_⟩
  rw [iterated_subdivide_single_model]
  apply VertexChains.map_mem_of_supported {v | MeshBound v ((shrink n) ^ k * 1)} _
    ((TopologicalSingular.map σ n).comp (realize _ n)) ?_ ?_
  · intro v hv
    rw [LinearMap.comp_apply, realize_single, map_single]
    obtain ⟨i, hi⟩ := hball _
      (Set.mem_univ _)
    apply single_mem_small
    refine ⟨i, fun z => hi ?_⟩
    exact (affineEval_dist_le _ v _ hv z (stdSimplex.vertex 0)).trans_lt (by simpa using hk)
  · exact iterated_subdivide_mem_mesh _ k n 1 zero_le_one
      (Finsupp.single_mem_supported ℤ 1 (standardVertices_mesh n))

theorem exists_subdivision_small
    (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) (c : Chain X n) :
    ∃ k, ((subdivide n)^[k]) c ∈ smallChains U n := by
  classical
  choose K hK using fun σ : Simplex X n => exists_subdivision_small_single U hU n σ (fun z => hcover (σ z))
  let N := c.support.sup K
  refine ⟨N, ?_⟩
  rw [← Module.End.pow_apply]
  apply VertexChains.map_mem_of_supported c.support (smallChains U n)
    ((subdivide n) ^ N) ?_ (fun _ h => h)
  intro σ hσ
  rw [Module.End.pow_apply]
  exact iterated_subdivide_small_of_le U (Finset.le_sup hσ) n (hK σ)

end FiniteChains.SingularSubdivision
