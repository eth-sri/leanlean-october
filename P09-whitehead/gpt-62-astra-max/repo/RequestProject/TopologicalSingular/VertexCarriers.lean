module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.VertexSubdivisionHomotopy
public import Mathlib.LinearAlgebra.Finsupp.Supported

@[expose] public section

/-! # Carrier control for subdivision and its homotopy -/

namespace FiniteChains.VertexChains

universe u
variable {V : Type u}

theorem map_mem_of_supported {ι M : Type*} [AddCommGroup M] [Module ℤ M]
    (S : Set ι) (T : Submodule ℤ M) (L : (ι →₀ ℤ) →ₗ[ℤ] M)
    (hL : ∀ v ∈ S, L (Finsupp.single v 1) ∈ T)
    {c : ι →₀ ℤ} (hc : c ∈ Finsupp.supported ℤ ℤ S) : L c ∈ T := by
  have he : Finsupp.supported ℤ ℤ S ≤ T.comap L := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr <;> aesop
  exact he hc

variable (S : Set V)

noncomputable def carried (n : ℕ) : Submodule ℤ (Chain V n) :=
  Finsupp.supported ℤ ℤ {v | ∀ i, v i ∈ S}

theorem single_mem_carried {n : ℕ} (v : Vertices V n) (r : ℤ) (hv : ∀ i, v i ∈ S) :
    Finsupp.single v r ∈ carried S n := Finsupp.single_mem_supported ℤ r hv

theorem boundary_mem_carried (n : ℕ) {c : Chain V _}
    (hc : c ∈ carried S _) : boundary n c ∈ carried S n := by
  apply map_mem_of_supported _ _ (boundary n) ?_ hc
  intro v hv
  rw [boundary_single]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  solve_by_elim [single_mem_carried]

theorem cone_mem_carried (p : V) (hp : p ∈ S) (n : ℕ) {c : Chain V n}
    (hc : c ∈ carried S n) : cone p n c ∈ carried S _ := by
  apply map_mem_of_supported _ _ (cone p n) ?_ hc
  intro v hv
  rw [cone_single]
  apply single_mem_carried
  apply Fin.cases <;> assumption

variable (center : ∀ n, Vertices V n → V) (S : Set V)
variable (hcenter : ∀ n v, (∀ i, v i ∈ S) → center n v ∈ S)

include hcenter in
theorem subdivide_mem_carried (n : ℕ) {c : Chain V n} (hc : c ∈ carried S n) :
    subdivide center n c ∈ carried S n := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    apply map_mem_of_supported _ _ (subdivide center _) ?_ hc
    intro v hv
    rw [subdivide_succ_single, one_smul]
    grind [cone_mem_carried, boundary_mem_carried, single_mem_carried]

end FiniteChains.VertexChains
