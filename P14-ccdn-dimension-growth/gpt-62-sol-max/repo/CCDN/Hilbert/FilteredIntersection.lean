/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import CCDN.ForMathlib.LinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Filtered multiples in a two-equation ideal

The filtered Hilbert function of a section is bounded by the rank lost
under multiplication by its equation in the original coordinate ring.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A subspace known to lie in a linear map's kernel subtracts from the image dimension. -/
lemma finrank_map_add_kernel_subspace_le {K M W : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup W] [Module K W]
    (φ : M →ₗ[K] W) (V U : Submodule K M) [Module.Finite K V]
    (hUV : U ≤ V) (hUker : U ≤ φ.ker) :
    Module.finrank K (V.map φ) + Module.finrank K U ≤ Module.finrank K V := by
  have h := φ.finrank_map_add_finrank_inf_ker V
  have hle := Submodule.finrank_mono (le_inf hUV hUker)
  omega

/-- Injective multiplication by a section killed in the target accounts for a
subspace lost on mapping the larger filtered piece. -/
lemma finrank_map_add_le_of_mul_mem {K A B : Type*} [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (V W : Submodule K A) [Module.Finite K V]
    {a : A} (ha : a ≠ 0) (hz : φ a = 0) (hmem : ∀ w ∈ W, a * w ∈ V) :
    Module.finrank K (V.map φ.toLinearMap) + Module.finrank K W ≤ Module.finrank K V := by
  let L := LinearMap.mulLeft K a
  have h := finrank_map_add_kernel_subspace_le φ.toLinearMap V (W.map L)
    (Submodule.map_le_iff_le_comap.mpr hmem) (by
      rintro _ ⟨w, _, rfl⟩
      change φ (a * w) = 0
      rw [map_mul, hz, zero_mul])
  rwa [← (Submodule.equivMapOfInjective L (fun _ _ => mul_left_cancel₀ ha) W).finrank_eq] at h

/-- Bounded-degree polynomials in the quotient coordinate ring: the image in `K[X] ⧸ I` of the
polynomials of total degree at most `N`. For `K = ℚ` its dimension is
`CCDN.affineHilbertFunction I N`. -/
def filteredCoordinateSpace {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (N : ℕ) : Submodule K (MvPolynomial σ K ⧸ I) :=
  (restrictTotalDegree σ K N).map (Ideal.Quotient.mkₐ K I).toLinearMap

lemma mem_filteredCoordinateSpace {K σ : Type*} [Field K]
    {I : Ideal (MvPolynomial σ K)} {N : ℕ} {x : MvPolynomial σ K ⧸ I} :
    x ∈ filteredCoordinateSpace I N ↔ ∃ f, f.totalDegree ≤ N ∧ Ideal.Quotient.mk I f = x := by
  change (∃ f ∈ restrictTotalDegree σ K N, Ideal.Quotient.mk I f = x) ↔ _
  simp only [mem_restrictTotalDegree]

instance filteredCoordinateSpace_finite {K σ : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (N : ℕ) : Module.Finite K (filteredCoordinateSpace I N) := by
  unfold filteredCoordinateSpace
  infer_instance


section

variable {K σ : Type*} [Field K]
  (I : Ideal (MvPolynomial σ K)) {m n : ℕ}
include K σ I m n

/-- The degree filtration of the coordinate ring `MvPolynomial σ K ⧸ I` is increasing. -/
lemma filteredCoordinateSpace_mono (hmn : m ≤ n) :
    filteredCoordinateSpace I m ≤ filteredCoordinateSpace I n := by
  apply Submodule.map_mono
  intro f hf
  exact (mem_restrictTotalDegree _ _ _).mpr (((mem_restrictTotalDegree _ _ _).mp hf).trans hmn)

/-- The degree filtration of the coordinate ring is multiplicative: a product of classes of
degree at most `m` and `n` has degree at most `m + n`. -/
lemma filteredCoordinateSpace_mul_mem {x y : MvPolynomial σ K ⧸ I}
    (hx : x ∈ filteredCoordinateSpace I m) (hy : y ∈ filteredCoordinateSpace I n) :
    x * y ∈ filteredCoordinateSpace I (m + n) := by
  obtain ⟨f, hf, rfl⟩ := mem_filteredCoordinateSpace.mp hx
  obtain ⟨g, hg, rfl⟩ := mem_filteredCoordinateSpace.mp hy
  exact mem_filteredCoordinateSpace.mpr ⟨f * g, (totalDegree_mul _ _).trans (Nat.add_le_add hf hg), by simp⟩

end

/-- A map that kills a proper section of degree at most `m` loses at least
an entire filtered piece shifted by `m`. -/
lemma filtered_section_image_finrank_add_le {K σ B : Type*} [Field K] [Finite σ]
    [CommRing B] [Algebra K B] (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (φ : (MvPolynomial σ K ⧸ I) →ₐ[K] B)
    {f : MvPolynomial σ K} (hf : f ∉ I) {m : ℕ} (hfm : f.totalDegree ≤ m)
    (hz : φ (Ideal.Quotient.mk I f) = 0) (N : ℕ) :
    Module.finrank K ((filteredCoordinateSpace I (m + N)).map φ.toLinearMap) +
      Module.finrank K (filteredCoordinateSpace I N) ≤
      Module.finrank K (filteredCoordinateSpace I (m + N)) :=
  finrank_map_add_le_of_mul_mem φ _ _ (Ideal.Quotient.eq_zero_iff_mem.not.mpr hf) hz
    (fun _ hw => filteredCoordinateSpace_mul_mem I
      (mem_filteredCoordinateSpace.mpr ⟨f, hfm, rfl⟩) hw)

/-- Curve degree via the filtered Hilbert function: the dimension of the bounded-degree part
of the coordinate ring is eventually `d * M + c`. Over `ℚ` with `σ = Fin n` this is
`CCDN.HasAffineCurveDegree`. -/
def HasFilteredCurveDegree {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K)) (d : ℕ) :
    Prop :=
  ∃ N : ℕ, ∃ c : ℤ, ∀ M ≥ N,
    (Module.finrank K (filteredCoordinateSpace I M) : ℤ) = (d : ℤ) * M + c

section

variable {K σ : Type*} [Field K]
include K σ


/-- For `f ≠ 0` and `deg f ≤ N`, the affine Hilbert function of `(f)` at `N` plus the dimension of
the polynomials of degree at most `N - deg f` equals the dimension of the polynomials of degree at
most `N`. -/
theorem principal_filtered_finrank [Finite σ]
    (f : MvPolynomial σ K) (hf : f ≠ 0) {N : ℕ} (hN : f.totalDegree ≤ N) :
    Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) N) +
      Module.finrank K (restrictTotalDegree σ K (N - f.totalDegree)) =
      Module.finrank K (restrictTotalDegree σ K N) := by
  let φ := (Ideal.Quotient.mkₐ K (Ideal.span {f})).toLinearMap
  let V := restrictTotalDegree σ K N
  let W := restrictTotalDegree σ K (N - f.totalDegree)
  let L := LinearMap.mulLeft K f
  have hk : V ⊓ φ.ker = W.map L := by
    ext x
    change x ∈ V ∧ x ∈ φ.ker ↔ x ∈ W.map L
    rw [Submodule.mem_map, LinearMap.mem_ker]
    change x ∈ V ∧ Ideal.Quotient.mk (Ideal.span {f}) x = 0 ↔ ∃ u ∈ W, f * u = x
    simp only [V, W, mem_restrictTotalDegree, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨hx, u, rfl⟩
      refine ⟨u, ?_, rfl⟩
      by_cases hu : u = 0
      · simp [hu]
      rw [totalDegree_mul_of_isDomain hf hu] at hx
      omega
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(totalDegree_mul _ _).trans (by omega), dvd_mul_right _ _⟩
  have he := φ.finrank_map_add_finrank_inf_ker V
  rwa [hk, ← (Submodule.equivMapOfInjective L (fun _ _ => mul_left_cancel₀ hf) W).finrank_eq] at he

def filteredQuotientMap (I J : Ideal (MvPolynomial σ K)) (hIJ : I ≤ J) :
    (MvPolynomial σ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J) :=
  Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ K J)
    (fun _ hf => Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hf))

lemma filteredCoordinateSpace_map_quotient
    (I J : Ideal (MvPolynomial σ K)) (hIJ : I ≤ J) (N : ℕ) :
    (filteredCoordinateSpace I N).map (filteredQuotientMap I J hIJ).toLinearMap =
      filteredCoordinateSpace J N := by
  rw [filteredCoordinateSpace, ← Submodule.map_comp]
  rfl

/-- The filtered rank bound for a section of a prime hypersurface. -/
theorem filteredCoordinateSpace_finrank_bound [Finite σ]
    {f g : MvPolynomial σ K} (hf : Prime f) (hfg : ¬ f ∣ g)
    (I : Ideal (MvPolynomial σ K)) (hIf : f ∈ I) (hIg : g ∈ I)
    {N : ℕ} (hN : f.totalDegree + g.totalDegree ≤ N) :
    Module.finrank K (filteredCoordinateSpace I N) +
      Module.finrank K (restrictTotalDegree σ K (N - f.totalDegree)) +
      Module.finrank K (restrictTotalDegree σ K (N - g.totalDegree)) ≤
      Module.finrank K (restrictTotalDegree σ K N) +
      Module.finrank K (restrictTotalDegree σ K (N - (f.totalDegree + g.totalDegree))) := by
  let J : Ideal (MvPolynomial σ K) := Ideal.span {f}
  let : J.IsPrime := (Ideal.span_singleton_prime hf.ne_zero).mpr hf
  have hJI : J ≤ I := I.span_singleton_le_iff_mem.mpr hIf
  have hg : g ∉ J := fun h => hfg (Ideal.mem_span_singleton.mp h)
  have h := filtered_section_image_finrank_add_le J (filteredQuotientMap J I hJI) hg le_rfl
    (Ideal.Quotient.eq_zero_iff_mem.mpr hIg) (N - g.totalDegree)
  rw [filteredCoordinateSpace_map_quotient, show g.totalDegree + (N - g.totalDegree) = N by omega] at h
  have h₁ := principal_filtered_finrank f hf.ne_zero (N := N) (by omega)
  have h₂ := principal_filtered_finrank f hf.ne_zero (N := N - g.totalDegree) (by omega)
  rw [Nat.sub_sub, add_comm g.totalDegree] at h₂
  change Module.finrank K (filteredCoordinateSpace I N) +
    Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) (N - g.totalDegree)) ≤
    Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) N) at h
  omega

/-- Lift a basis of the filtered coordinate ring to bounded-degree polynomials. -/
theorem exists_filtered_polynomial_basis [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (D : ℕ) :
    ∃ h : Fin (Module.finrank K (filteredCoordinateSpace I D)) → MvPolynomial σ K,
      (∀ i, (h i).totalDegree ≤ D) ∧
      LinearIndependent K (fun i => (Ideal.Quotient.mkₐ K I) (h i)) := by
  classical
  let b := Module.finBasis K (filteredCoordinateSpace I D)
  choose h hd he using fun i => mem_filteredCoordinateSpace.mp (b i).property
  refine ⟨h, hd, ?_⟩
  change LinearIndependent K (fun i => Ideal.Quotient.mk I (h i))
  simp only [he]
  exact b.linearIndependent.map' (filteredCoordinateSpace I D).subtype (Submodule.ker_subtype _)

/-- Enlarging the ideal can only shrink the filtered pieces of the coordinate ring. -/
lemma filteredCoordinateSpace_finrank_antitone_ideal [Fintype σ]
    (I J : Ideal (MvPolynomial σ K)) (hIJ : I ≤ J) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace J N) ≤
      Module.finrank K (filteredCoordinateSpace I N) := by
  rw [← filteredCoordinateSpace_map_quotient I J hIJ N]
  exact Submodule.finrank_map_le _ _

end

end
end CCDN
