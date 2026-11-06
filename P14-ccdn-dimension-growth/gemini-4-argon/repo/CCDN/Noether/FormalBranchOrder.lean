/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.PowerSeries.Basic
import CCDN.Algebra.SectionImageRank
import CCDN.Hilbert.PlaneHilbert
import CCDN.Noether.PowerSeriesFrobenius
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! A local Bézout bound on formal vanishing orders. It gives injective jets
on low-degree functions and verifies the jet condition in Frobenius
noncancellation for irreducible plane curves. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- If `X ^ N` divides the power series `g`, then the images of `1, X, …, X ^ (N - 1)` in the
quotient by `g` are linearly independent. -/
lemma powerSeries_quotient_powers_independent {K : Type*} [Field K]
    (g : PowerSeries K) (N : ℕ) (hvan : PowerSeries.X ^ N ∣ g) :
    LinearIndependent K (fun i : Fin N =>
      (Ideal.Quotient.mkₐ K (Ideal.span {g})) (PowerSeries.X ^ i.val)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  let P := ∑ j : Fin N, a j • (PowerSeries.X : PowerSeries K) ^ j.val
  have hP : P ∈ Ideal.span {g} :=
    Ideal.Quotient.eq_zero_iff_mem.mp (by
      change (Ideal.Quotient.mkₐ K (Ideal.span {g})) P = 0
      simpa only [P, map_sum, map_smul] using ha)
  have hc := PowerSeries.X_pow_dvd_iff.mp (hvan.trans (Ideal.mem_span_singleton.mp hP)) i.val i.isLt
  simp only [P, map_sum, PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_X_pow] at hc
  rwa [show (∑ j : Fin N, a j * if i.val = j.val then (1 : K) else 0) = a i by simp [Fin.val_inj]]
    at hc

/-- Frobenius coefficients cannot cancel a low-degree basis on a
formal plane branch. The numerical condition is d*D<p^r. -/
theorem formal_plane_frobenius_relation_trivial {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] (p r : ℕ) [Fact p.Prime] [CharP K p]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K) (hψ : ψ f = 0)
    (j : Fin 2) (a : K) (hparam : ψ (X j - C a) = PowerSeries.X)
    {D : ℕ} (hD : f.totalDegree * D < p ^ r) (h : ι → MvPolynomial (Fin 2) K)
    (hd : ∀ i, (h i).totalDegree ≤ D)
    (hi : LinearIndependent K (fun i => (Ideal.Quotient.mkₐ K (Ideal.span {f})) (h i)))
    (g : ι → PowerSeries K) (hrel : ∑ i, ψ (h i) * (g i) ^ (p ^ r) = 0) : ∀ i, g i = 0 := by
  refine powerSeries_frobenius_relation_trivial p r (fun i => ψ (h i)) (fun c hc => ?_) g hrel
  let P := ∑ i, c i • h i
  have hP : P.totalDegree ≤ D :=
    MvPolynomial.totalDegree_finsetSum_le fun i _ =>
      (MvPolynomial.totalDegree_smul_le _ _).trans (hd i)
  have hdiv : f ∣ P := by
    by_contra hnd
    have hvan : PowerSeries.X ^ p ^ r ∣ ψ P :=
      PowerSeries.X_pow_dvd_iff.mpr (by simpa only [P, map_sum, map_smul] using hc)
    let I : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {f}
    have : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hf.prime
    let J : Ideal (PowerSeries K) := Ideal.span {ψ P}
    let q := (Ideal.Quotient.mkₐ K J).comp ψ
    let φ : (MvPolynomial (Fin 2) K ⧸ I) →ₐ[K] (PowerSeries K ⧸ J) :=
      Ideal.Quotient.liftₐ I q fun l hl => by
        obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.mp hl
        simp only [q, AlgHom.comp_apply, map_mul, hψ, map_zero, zero_mul]
    have hli : LinearIndependent K
        (fun i : Fin (p ^ r) => φ ((Ideal.Quotient.mk I) ((X j - C a) ^ i.val))) := by
      have he : (fun i : Fin (p ^ r) => φ ((Ideal.Quotient.mk I) ((X j - C a) ^ i.val))) =
          fun i : Fin (p ^ r) => (Ideal.Quotient.mkₐ K J) (PowerSeries.X ^ i.val) :=
        funext fun i => by change q _ = _; simp only [q, AlgHom.comp_apply, map_pow, hparam]
      rw [he]
      exact powerSeries_quotient_powers_independent (ψ P) (p ^ r) hvan
    have hh : p ^ r ≤ f.totalDegree * P.totalDegree := by
      simpa only [Fintype.card_fin] using section_image_rank_le I f.totalDegree
        ⟨f.totalDegree, (f.totalDegree : ℤ) - f.totalDegree.choose 2,
          fun M hM => principal_plane_hilbert_function f hf.ne_zero hM⟩
        φ (fun i : Fin (p ^ r) => (X j - C a) ^ i.val) hli P
        (by simpa only [I, Ideal.mem_span_singleton] using hnd) P.totalDegree le_rfl
        (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)))
    exact (not_lt_of_ge (hh.trans (Nat.mul_le_mul_left _ hP))) hD
  have he : (Ideal.Quotient.mkₐ K (Ideal.span {f})) P = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
  exact Fintype.linearIndependent_iff.mp hi c (by simpa only [P, map_sum, map_smul] using he)

end
end CCDN
