/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.VertexSubdivisionHomotopy
import Mathlib.LinearAlgebra.Finsupp.Supported


/-! # Carrier control for subdivision and its homotopy -/

namespace FiniteChains.VertexChains

universe u
variable {V : Type u}

theorem map_mem_of_supported {ι M : Type*} [AddCommGroup M] [Module ℤ M]
    S (T : Submodule ℤ M) (L : (ι →₀ ℤ) →ₗ[ℤ] M)
    (hL : ∀ v ∈ S, L (Finsupp.single v 1) ∈ T)
    {c : ι →₀ ℤ} (hc : c ∈ Finsupp.supported ℤ ℤ S) : L c ∈ T := by
  have he : Finsupp.supported ℤ ℤ S ≤ T.comap L := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    aesop
  exact he hc

noncomputable def carried (S : Set V) n : Submodule ℤ (Chain V n) :=
  Finsupp.supported ℤ ℤ {v | ∀ i, v i ∈ S}

theorem single_mem_carried S {n} (v : Vertices V n) r (hv : ∀ i, v i ∈ S) :
    Finsupp.single v r ∈ carried S n := Finsupp.single_mem_supported ℤ r hv

theorem boundary_mem_carried S n {c : Chain V (n + 1)}
    (hc : c ∈ carried S (n + 1)) : boundary n c ∈ carried S n := by
  apply map_mem_of_supported _ _ (boundary n) ?_ hc
  intro v hv
  rw [boundary_single]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact single_mem_carried S _ 1 (by tauto)

theorem cone_mem_carried S p (hp : p ∈ S) n {c : Chain V n}
    (hc : c ∈ carried S n) : cone p n c ∈ carried S (n + 1) := by
  apply map_mem_of_supported _ _ (cone p n) ?_ hc
  intro v hv
  rw [cone_single]
  apply single_mem_carried
  intro i
  exact Fin.cases hp hv i

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
    apply cone_mem_carried S _ (hcenter _ _ hv)
    apply ih
    exact boundary_mem_carried S n (single_mem_carried S v 1 hv)
