/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Hilbert.LinearProjectionFiltration
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import CCDN.Hilbert.PolynomialComparison
import CCDN.Hilbert.TranscendenceBasis
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Integral linear projections preserve Hilbert dimension and
do not increase its multiplicity. -/

namespace CCDN
section
open MvPolynomial

variable {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ] [LinearOrder σ] [LinearOrder τ] (I : Ideal (MvPolynomial τ K)) [I.IsPrime]

/-- An integral map `ψ` from a polynomial ring to the quotient by a prime `I` preserves Hilbert
dimension: the filtered Hilbert polynomials of `ker ψ` and of `I` have the same degree. -/
theorem integral_projection_hilbert_dimension_eq
    (ψ : MvPolynomial σ K →ₐ[K] (MvPolynomial τ K ⧸ I))
    (hint : ψ.IsIntegral) :
    (filteredHilbertPolynomial (RingHom.ker ψ)).natDegree =
      (filteredHilbertPolynomial I).natDegree := by
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ.toRingHom
  classical
  let A := MvPolynomial σ K ⧸ (RingHom.ker ψ)
  let B := MvPolynomial τ K ⧸ I
  let : Algebra A B := (Ideal.kerLiftAlg ψ).toRingHom.toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algHom (Ideal.kerLiftAlg ψ)
  let : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr (Ideal.kerLiftAlg_injective ψ)
  let : Algebra.IsIntegral A B := ⟨hint.kerLift⟩
  let : Algebra.IsAlgebraic A B :=
    ⟨fun x => (show IsIntegral A x from hint.kerLift x).isAlgebraic⟩
  obtain ⟨U, hU, hBU⟩ := exists_hilbert_coordinate_transcendence_basis (RingHom.ker ψ)
  have hb := hBU.algebraMap_comp (A := B)
  have hJ := hilbert_dimension_eq_transcendence_basis_card I _ hb
  rw [Nat.card_eq_fintype_card] at hU
  exact hU.symm.trans hJ.symm

theorem integral_linear_projection_multiplicity
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (hint : (projectionCoordinateMap I a).IsIntegral) (d : ℕ)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial) :
    (filteredHilbertPolynomial (RingHom.ker (projectionCoordinateMap I a))).natDegree =
        (filteredHilbertPolynomial I).natDegree ∧
      ∃ e : ℕ, 0 < e ∧ e ≤ d ∧
        (filteredHilbertPolynomial (RingHom.ker (projectionCoordinateMap I a))).leadingCoeff =
          (e : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial := by
  let J := RingHom.ker (projectionCoordinateMap I a)
  have hJ : J ≠ ⊤ := RingHom.ker_ne_top _
  have hI := Ideal.IsPrime.ne_top ‹I.IsPrime›
  have hdim := integral_projection_hilbert_dimension_eq I _ hint
  obtain ⟨e, he, _, hlc⟩ := filteredHilbertPolynomial_positive_multiplicity J hJ
  have hle := filteredHilbertPolynomial_leadingCoeff_le J I hJ hI hdim
    (fun N => linear_projection_filtered_finrank_le I a ha N)
  rw [hdim] at hlc
  refine ⟨hdim, e, he, ?_, hlc⟩
  rw [hlc, hdegree] at hle
  exact_mod_cast (div_le_div_iff_of_pos_right
    (by positivity)).mp hle

/-- An integral linear projection of a prime of dimension `m` and degree `d` has dimension `m`
and a positive degree at most `d`. -/
theorem integral_linear_projection_dimension_degree
    (a : σ → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (hint : (projectionCoordinateMap I a).IsIntegral) {m d : ℕ}
    (hdimdeg : HasAffineDimensionDegree I m d) :
    ∃ e : ℕ, 0 < e ∧ e ≤ d ∧
      HasAffineDimensionDegree (RingHom.ker (projectionCoordinateMap I a)) m e := by
  obtain ⟨hdim, e, he, hed, hlc⟩ := integral_linear_projection_multiplicity I a ha hint d
    (by rw [hdimdeg.natDegree_eq]; exact hdimdeg.leadingCoeff_eq)
  rw [hdimdeg.natDegree_eq] at hdim hlc
  exact ⟨e, he, hed, hdim, hlc⟩

