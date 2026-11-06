/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PowerSeries.Basic
import CCDN.Algebra.SectionImageRank
import CCDN.Hilbert.PlaneHilbert
import CCDN.Noether.PowerSeriesFrobenius
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! A local Bézout bound on formal vanishing orders. It gives injective jets
on low-degree functions and verifies the jet condition in Frobenius
noncancellation for irreducible plane curves. -/

namespace CCDN
open MvPolynomial

/-- If `X ^ N` divides the power series `g`, then the images of `1, X, …, X ^ (N - 1)` in the
quotient by `g` are linearly independent. -/
lemma powerSeries_quotient_powers_independent {K : Type*} [Field K]
    (g : PowerSeries K) (N : ℕ) (hvan : PowerSeries.X ^ N ∣ g) :
    LinearIndependent K (fun i : Fin N =>
      (Ideal.Quotient.mkₐ K (Ideal.span {g})) (PowerSeries.X ^ i.val)) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  let P := ∑ j : Fin N, a j • (PowerSeries.X : PowerSeries K) ^ j.val
  have hP : P ∈ Ideal.span {g} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    aesop
  have hX := hvan.trans (Ideal.mem_span_singleton.mp hP)
  have hc := PowerSeries.X_pow_dvd_iff.mp hX i.val i.isLt
  simp only [P, map_sum, PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_X_pow] at hc
  have hsum : (∑ j : Fin N, a j * if i.val = j.val then (1 : K) else 0) = a i := by
    simp [Fin.val_inj]
  rwa [hsum] at hc

section
variable {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K) (hf : Irreducible f) (ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K) (hψ : ψ f = 0) (j : Fin 2) (a : K) (hparam : ψ (X j - C a) = PowerSeries.X)
include hf hψ hparam

/-- If a proper degree-m section vanishes to order N on a formal plane
branch, then N<=d*m. The parameter map and its equation are maps. -/
theorem formal_plane_vanishing_order_bound
    (g : MvPolynomial (Fin 2) K) (hnd : ¬ f ∣ g) {N : ℕ}
    (hvan : PowerSeries.X ^ N ∣ ψ g) : N ≤ f.totalDegree * g.totalDegree := by
  let p : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {f}
  have : p.IsPrime := Ideal.isPrime_span_singleton_of_prime hf.prime
  let J : Ideal (PowerSeries K) := Ideal.span {ψ g}
  let q := (Ideal.Quotient.mkₐ K J).comp ψ
  let φ : (MvPolynomial (Fin 2) K ⧸ p) →ₐ[K] (PowerSeries K ⧸ J) :=
    Ideal.Quotient.liftₐ p q (by
      intro l hl
      obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.mp hl
      aesop)
  have hφ (l : MvPolynomial (Fin 2) K) : φ ((Ideal.Quotient.mk p) l) = q l := rfl
  let h : Fin N → MvPolynomial (Fin 2) K := fun i => (X j - C a) ^ i.val
  have hi : LinearIndependent K (fun i => φ ((Ideal.Quotient.mk p) (h i))) := by
    have he : (fun i => φ ((Ideal.Quotient.mk p) (h i))) =
        (fun i => (Ideal.Quotient.mkₐ K J) (PowerSeries.X ^ i.val)) := by
      funext i
      rw [hφ]
      simp [q, AlgHom.comp_apply, h, map_pow, hparam]
    rw [he]
    exact powerSeries_quotient_powers_independent (ψ g) N hvan
  have hz : φ ((Ideal.Quotient.mk p) g) = 0 := by aesop
  have hh := section_image_rank_le p f.totalDegree
    ⟨f.totalDegree, f.totalDegree - f.totalDegree.choose 2,
      fun M hM => principal_plane_hilbert_function f hf.ne_zero hM⟩
    φ h hi g (by simp_all [p, Ideal.mem_span_singleton]) g.totalDegree le_rfl hz
  simpa using hh

/-- Jets longer than d*D detect every degree-at-most-D function on the curve. -/
theorem formal_plane_jet_detects_divisibility
    {D N : ℕ} (hN : f.totalDegree * D < N)
    (g : MvPolynomial (Fin 2) K) (hg : g.totalDegree ≤ D)
    (hzero : ∀ n < N, PowerSeries.coeff n (ψ g) = 0) : f ∣ g := by
  by_contra hnd
  have hh := formal_plane_vanishing_order_bound f hf ψ hψ j a hparam g hnd
    (PowerSeries.X_pow_dvd_iff.mpr hzero)
  exact (not_lt_of_ge (hh.trans (Nat.mul_le_mul_left _ hg))) hN

end

