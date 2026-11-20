/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
import CCDN.Algebra.PointSeparation
import CCDN.Algebra.SectionImageRank
import CCDN.Hilbert.PlaneHilbert
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.SimpleRing.Principal

/-! A proper plane section has total multiplicity at least N at no more
than d*m/N distinct smooth points. The proof uses local expansions
and polynomial interpolation. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Monomials of degree below `N` are independent modulo `X ^ N`. -/
private lemma powerSeries_quotient_powers_independent {K : Type*} [Field K]
    (N : ℕ) :
    LinearIndependent K (fun i : Fin N =>
      (Ideal.Quotient.mkₐ K (Ideal.span {(PowerSeries.X : PowerSeries K) ^ N})) (PowerSeries.X ^ i.val)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  let P := ∑ j : Fin N, a j • (PowerSeries.X : PowerSeries K) ^ j.val
  have hP : P ∈ Ideal.span {(PowerSeries.X : PowerSeries K) ^ N} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (Ideal.Quotient.mkₐ K (Ideal.span {(PowerSeries.X : PowerSeries K) ^ N})) P = 0
    simpa only [P, map_sum, map_smul] using ha
  have hc := PowerSeries.X_pow_dvd_iff.mp (Ideal.mem_span_singleton.mp hP) i.val i.isLt
  simp only [P, map_sum, PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_X_pow] at hc
  have hsum : (∑ j : Fin N, a j * if i.val = j.val then (1 : K) else 0) = a i := by
    simp [Fin.val_inj]
  rwa [hsum] at hc

/-- Bézout with a uniform lower bound on vanishing at distinct formal branches. -/
theorem formal_plane_multiplicity_bound {K ι : Type*} [Field K]
    [Fintype ι]
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
  classical
  let J := Ideal.span {(PowerSeries.X : PowerSeries K) ^ N}
  
  let π := Ideal.Quotient.mkₐ K J
  let q :=
    AlgHom.pi (fun i => π.comp (ψ i))
  obtain ⟨s, hs⟩ := exists_point_separators z hz
  let h : (Σ _ : ι, Fin N) → MvPolynomial (Fin 2) K :=
    fun t => s t.1 ^ N * (X (j t.1) - C (z t.1 (j t.1))) ^ t.2.val
  have hoff (i k : ι) (hik : i ≠ k) : π (ψ i (s k) ^ N) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    apply pow_dvd_pow_of_dvd
    rw [PowerSeries.X_dvd_iff]
    rw [hconst, hs, ite_eq_right hik]
  let v (i : ι) (b : Fin N) := π (ψ i (s i) ^ N) * π (PowerSeries.X ^ b.val)
  have himage (t : Σ _ : ι, Fin N) : q (h t) = Pi.single t.1 (v t.1 t.2) := by
    rcases t with ⟨k, b⟩
    funext i
    change π (ψ i (s k ^ N * (X (j k) - C (z k (j k))) ^ b.val)) = _
    rw [map_mul, map_pow, map_pow, map_mul]
    by_cases hik : i = k
    · subst k
      simp [v, hparam]
    · rw [hoff i k hik, zero_mul, Pi.single_eq_of_ne hik]
  have hv (i : ι) : LinearIndependent K (v i) := by
    have hu : IsUnit (π (ψ i (s i) ^ N)) := by
      apply IsUnit.map π (IsUnit.pow _ ?_)
      simp [PowerSeries.isUnit_iff_constantCoeff, hconst, hs]
    exact (powerSeries_quotient_powers_independent (K := K) N).map' (LinearMap.mulLeft K (π (ψ i (s i) ^ N)))
      (LinearMap.ker_eq_bot.mpr fun _ _ h => hu.mul_left_cancel h)
  have hi : LinearIndependent K (fun t => q (h t)) := by
    simpa only [himage] using Pi.linearIndependent_single v hv
  let p := Ideal.span {f}
  have : p.IsPrime := Ideal.isPrime_span_singleton_of_prime hf.prime
  let φ :=
    Ideal.Quotient.liftₐ p q (by
      intro l hl
      obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.mp hl
      ext i
      change π (ψ i (f * u)) = 0
      simp [hψ])
  have hφ (l : MvPolynomial (Fin 2) K) : φ ((Ideal.Quotient.mk p) l) = q l := rfl
  have hz' : φ ((Ideal.Quotient.mk p) g) = 0 := by
    rw [hφ]
    ext i
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (hvan i))
  have hb := section_image_rank_le p f.totalDegree
    (principal_plane_curve_degree f hf.ne_zero)
    φ h (by assumption) g
    (by simpa [p, Ideal.mem_span_singleton] using hnd) g.totalDegree le_rfl hz'
  simpa [Fintype.card_sigma] using hb

/-- The multiplicity bound at one branch. -/
lemma formal_plane_vanishing_order_bound {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : Fin 2 → K) (ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K) (hψ : ψ f = 0)
    (hconst : ∀ h, PowerSeries.constantCoeff (ψ h) = eval z h)
    (j : Fin 2) (hparam : ψ (X j - C (z j)) = PowerSeries.X)
    (g : MvPolynomial (Fin 2) K) (hnd : ¬ f ∣ g) {N : ℕ}
    (hvan : PowerSeries.X ^ N ∣ ψ g) : N ≤ f.totalDegree * g.totalDegree := by
  simpa using formal_plane_multiplicity_bound f hf (fun _ : Unit => z)
    (Function.injective_of_subsingleton _) (fun _ => ψ) (fun _ => hψ) (fun _ => hconst)
    (fun _ => j) (fun _ => hparam) g hnd N (fun _ => hvan)

end
end CCDN
