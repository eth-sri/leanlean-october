/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hilbert.HomogeneousHilbert
import Mathlib.RingTheory.MvPolynomial.Ideal
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hilbert.FilteredIntersection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! Origin-adic layers of a nonhomogeneous hypersurface. The first
nonzero homogeneous part supplies the singular multiplicity bound directly. -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable {K σ : Type*} [CommRing K] {f : MvPolynomial σ K} {k : ℕ}

/-- A homogeneous polynomial of degree `k` lies in the `k`-th power of the ideal of the origin. -/
lemma homogeneous_mem_origin_power
    (hf : f.IsHomogeneous k) :
    f ∈ idealOfVars σ K ^ k := by
  rw [mem_pow_idealOfVars_iff]
  intro e he
  exact (hf.degree_eq_sum_deg_support he).le

/-- Taking the first permitted homogeneous part changes a polynomial only by
one higher power of the origin ideal. -/
lemma sub_homogeneousComponent_mem_origin_power
    (hf : f ∈ idealOfVars σ K ^ k) :
    f - homogeneousComponent k f ∈ idealOfVars σ K ^ (k + 1) := by
  rw [mem_pow_idealOfVars_iff'] at hf ⊢
  intro e he
  rw [coeff_sub, coeff_homogeneousComponent]
  by_cases hk : e.degree = k
  · grind
  · grind

end

section
variable {K σ : Type*} [Field K] (f : MvPolynomial σ K) (k : ℕ)

/-- The ideal `(f) + 𝔪₀ ^ (k + 1)`, where `𝔪₀` is the ideal of the origin; the quotient by it is the
coordinate ring of `f = 0` truncated at the origin. -/
def originTruncationIdeal :
    Ideal (MvPolynomial σ K) := Ideal.span {f} ⊔ idealOfVars σ K ^ (k + 1)

/-- The degree-`k` layer of the ideal of the origin on the hypersurface `f = 0`: the image of
the `k`-th power of the ideal of the origin in the quotient by `(f)` and the `(k + 1)`-th power.
This is the image of the ideal power, not a tangent-cone model. -/
def originLayer :
    Submodule K (MvPolynomial σ K ⧸ originTruncationIdeal f k) :=
  ((idealOfVars σ K ^ k).restrictScalars K).map
    (Ideal.Quotient.mkₐ K (originTruncationIdeal f k)).toLinearMap

/-- Homogeneous degree-k polynomials generate the degree-k layer. -/
theorem originLayer_eq_homogeneousCoordinateSpace
    :
    originLayer f k = homogeneousCoordinateSpace (originTruncationIdeal f k) k := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨homogeneousComponent k u,
      homogeneousComponent_isHomogeneous k u, ?_⟩
    apply (sub_eq_zero.mp ?_)
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (show idealOfVars σ K ^ (k + 1) ≤ originTruncationIdeal f k from le_sup_right)
    simpa using (idealOfVars σ K ^ (k + 1)).neg_mem
      (sub_homogeneousComponent_mem_origin_power hu)
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    exact Submodule.mem_map.mpr ⟨u, homogeneous_mem_origin_power hu, rfl⟩

end

/-- The initial homogeneous equation vanishes in each origin-adic layer
after multiplying by an allowed homogeneous polynomial. -/
lemma initial_form_multiple_mem_truncation {K σ : Type*} [Field K]
    {f : MvPolynomial σ K} {μ k : ℕ} (hf : f ∈ idealOfVars σ K ^ μ) (hk : μ ≤ k)
    {u : MvPolynomial σ K} (hu : u.IsHomogeneous (k - μ)) :
    homogeneousComponent μ f * u ∈ originTruncationIdeal f k := by
  have hr := Ideal.mul_mem_mul (sub_homogeneousComponent_mem_origin_power hf)
    (homogeneous_mem_origin_power hu)
  rw [← pow_add, show μ + 1 + (k - μ) = k + 1 by omega] at hr
  have hfu :=
    (show Ideal.span {f} ≤ originTruncationIdeal f k from le_sup_left)
      (Ideal.mem_span_singleton.mpr (dvd_mul_right f u))
  have hru :=
    (show idealOfVars σ K ^ (k + 1) ≤ originTruncationIdeal f k from le_sup_right) hr
  convert (originTruncationIdeal f k).sub_mem hfu hru using 1
  ring

/-- The first nonzero homogeneous part gives the expected binomial upper bound
for the local layer. -/
theorem originLayer_hilbert_bound {K : Type*} [Field K] {n μ k : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K)
    (hf : f ∈ idealOfVars (Fin (n + 1)) K ^ μ)
    (hμ : homogeneousComponent μ f ≠ 0) (hk : μ ≤ k) :
    Module.finrank K (originLayer f k) + (n + (k - μ)).choose (k - μ) ≤
      (n + k).choose k := by
  let g := homogeneousComponent μ f
  let V := homogeneousSubmodule (Fin (n + 1)) K k
  let U := homogeneousMultiples g μ k
  let φ := (Ideal.Quotient.mkₐ K (originTruncationIdeal f k)).toLinearMap
  let _ : Module.Finite K V := Module.Finite.of_fg (homogeneousSubmodule_fg _ _ _)
  have hker : U ≤ φ.ker := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (initial_form_multiple_mem_truncation hf hk hu)
  have h := finrank_map_add_kernel_subspace_le φ V U (by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    change (g * u).IsHomogeneous k
    simpa [Nat.add_sub_of_le hk] using (homogeneousComponent_isHomogeneous μ f).mul hu) hker
  rw [homogeneousMultiples_finrank _ hμ, finrank_homogeneousSubmodule_fin,
    finrank_homogeneousSubmodule_fin] at h
  rwa [originLayer_eq_homogeneousCoordinateSpace]

instance originLayer_finite {K σ : Type*} [Field K] [Finite σ]
    (f : MvPolynomial σ K) (k : ℕ) : Module.Finite K (originLayer f k) := by
  rw [originLayer_eq_homogeneousCoordinateSpace]
  let _ : Module.Finite K (homogeneousSubmodule σ K k) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg _ _ _)
  unfold homogeneousCoordinateSpace
  infer_instance

variable {K : Type*} [Field K]

