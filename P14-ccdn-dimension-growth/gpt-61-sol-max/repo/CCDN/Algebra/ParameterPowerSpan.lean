/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! Finite power blocks for a linear parameter. Their dimension grows with
slope at most the number of field-basis vectors, giving the upper Hilbert
growth bound needed to recognize a parameter of full degree. -/

@[expose] public section
namespace CCDN

/-- Powers through N of a parameter, multiplied by a fixed finite family. -/
noncomputable def parameterPowerSpan (K : Type*) {F ι : Type*} [Field K] [Field F] [Algebra K F]
    (u : F) (v : ι → F) (N : ℕ)  :=
  Submodule.span K (Set.range (fun t : ι × Fin (N + 1) => u ^ t.2.val * v t.1))

noncomputable instance parameterPowerSpan_finite {K F ι : Type*} [Field K] [Field F] [Algebra K F]
    [Fintype ι] (u : F) (v : ι → F) (N : ℕ) : Module.Finite K (parameterPowerSpan K u v N) :=
  Module.Finite.span_of_finite K (Set.finite_range _)

variable {K F ι : Type*} [Field K] [Field F] [Algebra K F]

/-- The span of the products `u ^ j * v i` with `j ≤ N` has dimension at most
`Fintype.card ι * (N + 1)`. -/
lemma parameterPowerSpan_finrank_le 
    [Fintype ι] (u : F) (v : ι → F) (N : ℕ) :
    Module.finrank K (parameterPowerSpan K u v N) ≤ Fintype.card ι * (N + 1) := by
  have h := finrank_range_le_card (R := K) (fun t : ι × Fin (N + 1) => u ^ t.2.val * v t.1)
  change Module.finrank K (Submodule.span K (Set.range
    (fun t : ι × Fin (N + 1) => u ^ t.2.val * v t.1))) ≤ Fintype.card (ι × Fin (N + 1)) at h
  rw [Fintype.card_prod, Fintype.card_fin] at h
  exact h

variable (u : F) (v : ι → F)

/-- The parameter power spans increase with the power bound. -/
lemma parameterPowerSpan_mono 
     {M N : ℕ} (hMN : M ≤ N) :
    parameterPowerSpan K u v M ≤ parameterPowerSpan K u v N := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨i,j⟩, rfl⟩
  exact Submodule.subset_span ⟨(i, ⟨j.val, by omega⟩), rfl⟩

/-- Multiplication by the parameter `u` maps the span of powers up to `N` into the span of
powers up to `N + 1`. -/
lemma parameterPowerSpan_mul_mem 
     (N : ℕ) {x : F} (hx : x ∈ parameterPowerSpan K u v N) :
    u * x ∈ parameterPowerSpan K u v (N + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨i,j⟩, rfl⟩ := hx
    have he : u * (u ^ j.val * v i) = u ^ (j.val + 1) * v i := by ring
    rw [he]
    exact Submodule.subset_span ⟨(i, ⟨j.val + 1, by omega⟩), rfl⟩
  | zero => simp_all
  | add x y hx hy hxi hyi =>
    simp_all [mul_add, add_mem]
  | smul c x hx hxi =>
    aesop

/-- Polynomial parameter coefficients of degree at most N lie in the power block. -/
lemma polynomial_parameter_mul_mem 
     (i : ι) (p : Polynomial K) (N : ℕ) (hp : p.natDegree ≤ N) :
    Polynomial.aeval u p * v i ∈ parameterPowerSpan K u v N := by
  classical
  rw [p.as_sum_support, map_sum, Finset.sum_mul]
  apply (parameterPowerSpan K u v N).sum_mem
  intro j hj
  rw [Polynomial.aeval_monomial]
  have hjN :=
    (Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hj)).trans hp
  have hm : u ^ j * v i ∈ parameterPowerSpan K u v N :=
    Submodule.subset_span ⟨(i, ⟨j, by omega⟩), rfl⟩
  simpa only [Algebra.smul_def, mul_assoc] using
    (parameterPowerSpan K u v N).smul_mem (p.coeff j) hm

end CCDN
