/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Hilbert.HomogeneousHilbert
public import Mathlib.RingTheory.MvPolynomial.Ideal
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hilbert.FilteredIntersection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! Origin-adic layers of a nonhomogeneous hypersurface. The first
nonzero homogeneous part supplies the singular multiplicity bound directly. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {K σ : Type*}

/-- A homogeneous polynomial of degree `k` lies in the `k`-th power of the ideal of the origin. -/
lemma homogeneous_mem_origin_power  [CommRing K]
    {f : MvPolynomial σ K} {k : ℕ} (hf : f.IsHomogeneous k) :
    f ∈ idealOfVars σ K ^ k := by
  rw [mem_pow_idealOfVars_iff]
  intro e he
  exact (hf.degree_eq_sum_deg_support he).le

/-- Taking the first permitted homogeneous part changes a polynomial only by
one higher power of the origin ideal. -/
lemma sub_homogeneousComponent_mem_origin_power  [CommRing K]
    {f : MvPolynomial σ K} {k : ℕ} (hf : f ∈ idealOfVars σ K ^ k) :
    f - homogeneousComponent k f ∈ idealOfVars σ K ^ (k + 1) := by
  grind [mem_pow_idealOfVars_iff', coeff_homogeneousComponent]

/-- The ideal `(f) + 𝔪₀ ^ (k + 1)`, where `𝔪₀` is the ideal of the origin; the quotient by it is the
coordinate ring of `f = 0` truncated at the origin. -/
def originTruncationIdeal  [Field K] (f : MvPolynomial σ K) (k : ℕ)  := Ideal.span {f} ⊔ idealOfVars σ K ^ (k + 1)

/-- The degree-`k` layer of the ideal of the origin on the hypersurface `f = 0`: the image of
the `k`-th power of the ideal of the origin in the quotient by `(f)` and the `(k + 1)`-th power.
This is the image of the ideal power, not a tangent-cone model. -/
def originLayer  [Field K] (f : MvPolynomial σ K) (k : ℕ)  :=
  ((idealOfVars σ K ^ k).restrictScalars K).map
    (Ideal.Quotient.mkₐ K (originTruncationIdeal f k)).toLinearMap

/-- Homogeneous degree-k polynomials generate the degree-k layer. -/
theorem originLayer_eq_homogeneousCoordinateSpace  [Field K]
    (f : MvPolynomial σ K) (k : ℕ) :
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
    simpa only [neg_sub] using (idealOfVars σ K ^ (k + 1)).neg_mem
      (sub_homogeneousComponent_mem_origin_power hu)
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    exact Submodule.mem_map.mpr ⟨u, homogeneous_mem_origin_power hu, rfl⟩


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
  have hUV : U ≤ V := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    change (g * u).IsHomogeneous k
    simpa only [Nat.add_sub_of_le hk] using (homogeneousComponent_isHomogeneous μ f).mul hu
  have hker : U ≤ φ.ker := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((show (homogeneousComponent μ) f * u ∈ originTruncationIdeal f k from (by
                                                let inline_σ := Fin (n + (1 : ℕ))
                                                have hr := Ideal.mul_mem_mul (sub_homogeneousComponent_mem_origin_power hf)
                                                  (homogeneous_mem_origin_power hu)
                                                rw [← pow_add, show μ + 1 + (k - μ) = k + 1 by omega] at hr
                                                have hfu :=
                                                  (show Ideal.span {f} ≤ originTruncationIdeal f k from le_sup_left)
                                                    (Ideal.mem_span_singleton.mpr (dvd_mul_right f u))
                                                have hru :=
                                                  (show idealOfVars inline_σ K ^ (k + 1) ≤ originTruncationIdeal f k from le_sup_right) hr
                                                convert (originTruncationIdeal f k).sub_mem hfu hru using 1
                                                ring)))
  have h := finrank_map_add_kernel_subspace_le φ V U hUV hker
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

/-- The degree-`k` origin layer of a hypersurface in `n + 1` variables has dimension at most the
number `(n + k).choose k` of monomials of degree `k`. -/
lemma originLayer_finrank_le {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (k : ℕ) :
    Module.finrank K (originLayer f k) ≤ (n + k).choose k := by
  rw [originLayer_eq_homogeneousCoordinateSpace]
  let _ : Module.Finite K (homogeneousSubmodule (Fin (n + 1)) K k) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg _ _ _)
  exact (Submodule.finrank_map_le _ _).trans_eq (finrank_homogeneousSubmodule_fin n k)


end
end CCDN
