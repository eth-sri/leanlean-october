/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.RingTheory.PowerSeries.Basic
import CCDN.Algebra.PointSeparation
import CCDN.Algebra.SectionImageRank
import CCDN.Hilbert.PlaneHilbert
import CCDN.Noether.FormalBranchOrder
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.SimpleRing.Principal

/-! A proper plane section has total multiplicity at least N at no more
than d*m/N distinct smooth points. The proof uses local expansions
and polynomial interpolation. -/

namespace CCDN
section
open MvPolynomial

/-- Bézout with a uniform lower bound on vanishing at distinct formal branches. -/
theorem formal_plane_multiplicity_bound {K ι : Type*} [Field K]
    [Fintype ι] [DecidableEq ι]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : ι → Fin 2 → K) (hz : Function.Injective z)
    (ψ : ι → MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K)
    (hψ : ∀ i, ψ i f = 0)
    (hconst : ∀ i h, PowerSeries.constantCoeff (ψ i h) = eval (z i) h)
    (j : ι → Fin 2)
    (hparam : ∀ i, ψ i (X (j i) - C (z i (j i))) = PowerSeries.X)
    (g : MvPolynomial (Fin 2) K) (hnd : ¬ f ∣ g) (N : ℕ)
    (hvan : ∀ i, PowerSeries.X ^ N ∣ ψ i g) :
    Fintype.card ι * N ≤ f.totalDegree * g.totalDegree := by
  by_cases hN : N = 0
  · grind
  let J : Ideal (PowerSeries K) := Ideal.span {(PowerSeries.X : PowerSeries K) ^ N}
  let Q := PowerSeries K ⧸ J
  let π : PowerSeries K →ₐ[K] Q := Ideal.Quotient.mkₐ K J
  let q : MvPolynomial (Fin 2) K →ₐ[K] (ι → Q) :=
    AlgHom.pi (fun i => π.comp (ψ i))
  obtain ⟨s, hs⟩ := exists_point_separators z hz
  let h : ι × Fin N → MvPolynomial (Fin 2) K :=
    fun t => s t.1 ^ N * (X (j t.1) - C (z t.1 (j t.1))) ^ t.2.val
  have hoff (i k : ι) (hik : i ≠ k) : π (ψ i (s k) ^ N) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    apply pow_dvd_pow_of_dvd
    rw [PowerSeries.X_dvd_iff]
    grind
  have himage (i k : ι) (b : Fin N) :
      q (h (k, b)) i = if i = k then π (ψ i (s i) ^ N) * π (PowerSeries.X ^ b.val) else 0 := by
    change π (ψ i (s k ^ N * (X (j k) - C (z k (j k))) ^ b.val)) = _
    rw [map_mul, map_pow, map_pow, map_mul]
    by_cases hik : i = k
    · grind
    · simp_all
  have hi : LinearIndependent K (fun t => q (h t)) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha t
    have he := congrFun ha t.1
    simp [Finset.sum_apply, Pi.smul_apply, Fintype.sum_prod_type, himage] at he
    have he' : π (ψ t.1 (s t.1) ^ N) *
        (∑ b : Fin N, a (t.1, b) • π (PowerSeries.X ^ b.val)) = 0 := by
      rw [Finset.mul_sum]
      have he'' : (∑ b : Fin N, a (t.1, b) •
          (π (ψ t.1 (s t.1) ^ N) * π (PowerSeries.X ^ b.val))) = 0 := by
        simpa using he
      simpa [mul_smul_comm] using he''
    have hu : IsUnit (π (ψ t.1 (s t.1) ^ N)) := by
      apply IsUnit.map π
      apply IsUnit.pow
      rw [PowerSeries.isUnit_iff_constantCoeff, hconst, hs]
      grind
    have hli : LinearIndependent K (fun b : Fin N => π (PowerSeries.X ^ b.val)) :=
      powerSeries_quotient_powers_independent (PowerSeries.X ^ N) N dvd_rfl
    exact Fintype.linearIndependent_iff.mp hli (fun b => a (t.1, b)) (by
      apply hu.mul_left_cancel
      simp_all) t.2
  let p : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {f}
  have : p.IsPrime := Ideal.isPrime_span_singleton_of_prime hf.prime
  let φ : (MvPolynomial (Fin 2) K ⧸ p) →ₐ[K] (ι → Q) :=
    Ideal.Quotient.liftₐ p q (by
      intro l hl
      obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.mp hl
      ext i
      change π (ψ i (f * u)) = 0
      grind)
  have hφ (l : MvPolynomial (Fin 2) K) : φ ((Ideal.Quotient.mk p) l) = q l := rfl
  have hz' : φ ((Ideal.Quotient.mk p) g) = 0 := by
    ext i
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hvan i))
  have hb := section_image_rank_le p f.totalDegree
    ⟨f.totalDegree, f.totalDegree - f.totalDegree.choose 2,
      fun M hM => principal_plane_hilbert_function f hf.ne_zero hM⟩
    φ h (by grind) g
    (by simpa [p, Ideal.mem_span_singleton] using hnd) g.totalDegree le_rfl hz'
  simpa using hb

