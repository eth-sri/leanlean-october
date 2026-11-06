/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Hilbert.LinearProjectionFiltration
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import CCDN.Algebra.BinomialSectionBound
import CCDN.Hilbert.LinearCoordinates
import CCDN.Hilbert.PolynomialComparison
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.SimpleModule.Basic

/-! Hypersurface projection kernels in arbitrary dimension.
The proper-intersection estimate excludes a second independent equation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/- An irreducible equation generates the whole kernel whenever the image
contains the expected number of independent linear coordinates. -/

/-- A linear projection with one more coordinate than Hilbert dimension
and an independent subtuple has a principal prime equation. -/
theorem exists_hypersurface_projection_equation
    {K τ : Type*} [Field K] [Fintype τ] [LinearOrder τ] {n : ℕ}
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : Fin (n + 2) → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (hd : (filteredHilbertPolynomial I).natDegree < n + 2)
    (b : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hb : ∀ i, (b i).totalDegree ≤ 1)
    (hi : AlgebraicIndependent K (fun i => projectionCoordinateMap I a (b i))) :
    ∃ f : MvPolynomial (Fin (n + 2)) K, Irreducible f ∧
      RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f} := by
  let ψ := projectionCoordinateMap I a
  have hker : RingHom.ker ψ ≠ ⊥ := fun he =>
    linear_projection_not_injective_of_hilbert_dimension_lt I a ha
      (by simpa only [Fintype.card_fin] using hd)
      ((RingHom.injective_iff_ker_eq_bot ψ.toRingHom).mpr he)
  have hprime : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ.toRingHom
  obtain ⟨f, hfmem, hf⟩ := hprime.exists_mem_prime_of_ne_bot hker
  refine ⟨f, hf.irreducible, ?_⟩
  ext g
  rw [Ideal.mem_span_singleton]
  refine ⟨fun hg => ?_, fun ⟨u, hu⟩ => by
    change ψ g = 0; rw [hu, map_mul, show ψ f = 0 from hfmem, zero_mul]⟩
  by_contra hnd
  let J := RingHom.ker ψ
  have hlo := independent_linear_card_le_hilbert_dimension J b hb
    (AlgebraicIndependent.of_comp (Ideal.kerLiftAlg ψ) hi)
  simp only [Fintype.card_fin] at hlo
  let Q := Polynomial.C ((f.totalDegree * g.totalDegree : ℕ) : ℚ) *
    Polynomial.preHilbertPoly ℚ n 0
  have hQ : Q.natDegree ≤ n := Polynomial.natDegree_mul_le.trans
    (by simp only [Polynomial.natDegree_C, Polynomial.natDegree_preHilbertPoly, zero_add]; exact le_rfl)
  obtain ⟨M, hM⟩ := filteredHilbertPolynomial_spec J
  have hhi := (polynomial_natDegree_le_of_eventual_nat_eval_le (filteredHilbertPolynomial J) Q
    (filteredHilbertPolynomial_leadingCoeff_pos J (RingHom.ker_ne_top ψ))
    ⟨max M (f.totalDegree + g.totalDegree), fun N hN => by
      rw [hM N ((le_max_left _ _).trans hN)]
      dsimp [Q]
      rw [Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.preHilbertPoly_eq_choose_add_sub ℚ n (by omega : 0 ≤ N + n)]
      simp only [Nat.sub_zero, Nat.add_comm N n]
      exact_mod_cast filteredCoordinateSpace_codim_two_bound hf.irreducible.prime hnd J hfmem hg
        ((le_max_right _ _).trans hN)⟩).trans hQ
  omega

end
end CCDN
