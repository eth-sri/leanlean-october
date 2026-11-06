/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Hilbert.LinearProjectionFiltration
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hilbert.PolynomialComparison
import CCDN.Hilbert.PrincipalHilbertPolynomial
import CCDN.Projection.HilbertProjectionKernel

/-! Degree bounds for hypersurface equations of linear projections.
The degree is bounded by the factorial-normalized leading coefficient of
the original quotient's filtered Hilbert polynomial. -/

namespace CCDN
section
open MvPolynomial

variable {K τ : Type*} [Field K] [Fintype τ] [LinearOrder τ] {n : ℕ} (I : Ideal (MvPolynomial τ K))

theorem hypersurface_projection_equation_degree_le
    (hI : I ≠ ⊤)
    (a : Fin (n + 1) → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (d : ℕ) (hdimdeg : HasAffineDimensionDegree I n d)
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f ≠ 0) (hfdeg : 0 < f.totalDegree)
    (hker : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f}) :
    f.totalDegree ≤ d := by
  have hp : Ideal.span {f} ≠ ⊤ := by
    rw [← hker]
    let : Nontrivial (MvPolynomial τ K ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
    exact RingHom.ker_ne_top _
  have hh := filteredHilbertPolynomial_leadingCoeff_le (Ideal.span {f}) I hp hI
    ((principal_filteredHilbertPolynomial_natDegree f hf hfdeg).trans hdimdeg.natDegree_eq.symm)
    (fun N => by
      rw [← hker]
      exact linear_projection_filtered_finrank_le I a ha N)
  rw [principal_filteredHilbertPolynomial_leadingCoeff f hf hfdeg, hdimdeg.leadingCoeff_eq] at hh
  exact_mod_cast (div_le_div_iff_of_pos_right (by positivity)).mp hh

/-- The equation and its degree bound are constructed from the projection. -/
theorem exists_hypersurface_projection_equation_degree_le
    [I.IsPrime]
    (a : Fin (n + 2) → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I n d)
    (b : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hb : ∀ i, (b i).totalDegree ≤ 1)
    (hi : AlgebraicIndependent K (fun i => projectionCoordinateMap I a (b i))) :
    ∃ f : MvPolynomial (Fin (n + 2)) K, Irreducible f ∧
      0 < f.totalDegree ∧ f.totalDegree ≤ d ∧
      RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f} := by
  let ψ := projectionCoordinateMap I a
  obtain ⟨f, hfmem, hf⟩ := (RingHom.ker_isPrime ψ.toRingHom).exists_mem_prime_of_ne_bot fun he =>
    linear_projection_not_injective_of_hilbert_dimension_lt I a ha
      (by simp [hdimdeg.natDegree_eq]) ((RingHom.injective_iff_ker_eq_bot ψ.toRingHom).mpr he)
  have hker : RingHom.ker ψ = Ideal.span {f} := by
    ext g
    rw [Ideal.mem_span_singleton]
    constructor
    · intro hg
      by_contra hnd
      have hlo := independent_linear_card_le_hilbert_dimension _ b hb
        (AlgebraicIndependent.of_comp (Ideal.kerLiftAlg ψ) hi)
      have hhi := proper_intersection_hilbert_dimension_le hf hnd _ (RingHom.ker_ne_top ψ) hfmem hg
      simp at hlo
      omega
    · rintro ⟨u, rfl⟩
      exact Ideal.mul_mem_right _ _ hfmem
  replace hf := hf.irreducible
  have hfdeg :=
    totalDegree_pos_of_ne_zero_of_not_isUnit hf.ne_zero hf.not_isUnit
  exact ⟨f, hf, hfdeg, hypersurface_projection_equation_degree_le I
    (Ideal.IsPrime.ne_top ‹I.IsPrime›) a ha d hdimdeg f hf.ne_zero hfdeg hker, hker⟩

