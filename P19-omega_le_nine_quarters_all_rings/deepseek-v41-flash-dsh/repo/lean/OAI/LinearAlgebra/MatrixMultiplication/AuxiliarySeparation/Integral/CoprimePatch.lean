module

public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Integral.Restriction

public section

@[expose] section

/-!
# Patching scalar multiples before applying a character

Scalar multiples need not be primitive tensors over the integers. These
lemmas combine their actual coefficient maps first; no character is applied
to a nonprimitive scalar multiple.
-/

namespace OAI.MatrixMultiplication.AuxiliarySeparation.Integral

open Foundation
open scoped BigOperators

variable {R X Y Z ι : Type*} [CommSemiring R]

/-- A finite Bezout combination patches exact rank decompositions. -/
theorem rankAtMost_patch [Fintype ι] (T : Tensor R X Y Z)
    (d u : ι → R) (r : ι → ℕ) (hu : ∑ i, u i * d i = 1)
    (h : ∀ i, Tensor.RankAtMost (fun x y z => d i * T x y z) (r i)) :
    Tensor.RankAtMost T (∑ i, r i) := by
  classical
  choose a b c hc using fun i => (h i).scale (u i)
  have heq : T = fun x y z =>
      ∑ q : Σ i, Fin (r i), Tensor.rankOne (a q.1 q.2) (b q.1 q.2) (c q.1 q.2) x y z := by
    funext x y z
    simp only [Fintype.sum_sigma]
    calc
      T x y z = (∑ i, u i * d i) * T x y z := by rw [hu, one_mul]
      _ = ∑ i, u i * (d i * T x y z) := by simp [Finset.sum_mul, mul_assoc]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact congrFun (congrFun (congrFun (hc i) x) y) z
  rw [heq]
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    Tensor.rankAtMost_sum_rankOne
      (fun q : Σ i, Fin (r i) => a q.1 q.2)
      (fun q : Σ i, Fin (r i) => b q.1 q.2)
      (fun q : Σ i, Fin (r i) => c q.1 q.2)

/-- Consecutive periods are coprime over every commutative ring. -/
theorem isCoprime_consecutive {R : Type*} [CommRing R] (d : R) :
    IsCoprime d (d + 1) := by
  exact ⟨-1, 1, by ring⟩

/-- Powers of any finite Bezout family are again a Bezout family. The new
coefficients may depend on k; the family of source schemes does not. -/
theorem exists_bezout_powers {R ι : Type*} [CommRing R] [Fintype ι]
    (d u : ι → R) (hu : ∑ i, u i * d i = 1) (k : ℕ) :
    ∃ v : ι → R, ∑ i, v i * d i ^ k = 1 := by
  have hs : Ideal.span (Set.range d) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    change (1 : R) ∈ Submodule.span R (Set.range d)
    exact (Submodule.mem_span_range_iff_exists_fun R).mpr ⟨u, by simpa only [smul_eq_mul] using hu⟩
  have hp := Ideal.span_pow_eq_top (Set.range d) hs k
  have hset : ((fun x : R => x ^ k) '' Set.range d) = Set.range (fun i => d i ^ k) := by
    ext x
    simp
  rw [hset] at hp
  have hm := (Ideal.eq_top_iff_one _).mp hp
  change (1 : R) ∈ Submodule.span R (Set.range (fun i => d i ^ k)) at hm
  simpa only [smul_eq_mul] using (Submodule.mem_span_range_iff_exists_fun R).mp hm

/-- A finite collection of clearing schemes with one Bezout identity patches
all powers with a constant total overhead. -/
theorem rankAtMost_patch_power_family {R ι : Type*} [CommRing R] [Fintype ι]
    (T : Tensor R X Y Z) (d u : ι → R) (r : ι → ℕ) (s : ℕ)
    (hu : ∑ i, u i * d i = 1)
    (h : ∀ i k, Tensor.RankAtMost
      (fun x y z => d i ^ k * Tensor.power T k x y z) (s ^ k * r i)) (k : ℕ) :
    Tensor.RankAtMost (Tensor.power T k) (s ^ k * ∑ i, r i) := by
  obtain ⟨v, hv⟩ := exists_bezout_powers d u hu k
  simpa only [Finset.mul_sum] using
    rankAtMost_patch (Tensor.power T k) (fun i => d i ^ k) v (fun i => s ^ k * r i) hv
      (fun i => h i k)

/-- No common prime divisor implies that a collection of integers generates
one. The collection itself need not be finite at this stage. -/
theorem integer_span_eq_top_of_prime_witness (S : Set ℤ)
    (h : ∀ p : ℕ, p.Prime → ∃ D ∈ S, ¬ (p : ℤ) ∣ D) :
    Ideal.span S = ⊤ := by
  let g := Submodule.IsPrincipal.generator (Ideal.span S)
  have hu : IsUnit g := by
    by_contra hunit
    have hg : g.natAbs ≠ 1 := by
      intro hg
      exact hunit (Int.isUnit_iff_natAbs_eq.mpr hg)
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
    obtain ⟨D, hDS, hpD⟩ := h p hp
    apply hpD
    apply (Int.natCast_dvd.mpr hpg).trans
    exact (Submodule.IsPrincipal.mem_iff_generator_dvd (Ideal.span S)).mp
      (Ideal.subset_span hDS)
  rw [← Ideal.span_singleton_generator (Ideal.span S)]
  exact Ideal.span_singleton_eq_top.mpr hu

/-- Extract one finite Bezout family before any tensor-power parameter varies. -/
theorem exists_finite_bezout_of_prime_witness (S : Set ℤ)
    (h : ∀ p : ℕ, p.Prime → ∃ D ∈ S, ¬ (p : ℤ) ∣ D) :
    ∃ t : Finset ℤ, (↑t : Set ℤ) ⊆ S ∧
      ∃ u : t → ℤ, ∑ i, u i * (i : ℤ) = 1 := by
  classical
  have htop := integer_span_eq_top_of_prime_witness S h
  have hmem := (Ideal.eq_top_iff_one _).mp htop
  change (1 : ℤ) ∈ Submodule.span ℤ S at hmem
  obtain ⟨t, htS, ht⟩ := Submodule.mem_span_finite_of_mem_span hmem
  have hrange : Set.range (fun i : t => (i : ℤ)) = (↑t : Set ℤ) := by
    ext x
    simp
  rw [← hrange] at ht
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp ht
  exact ⟨t, htS, u, by simpa only [smul_eq_mul] using hu⟩

end OAI.MatrixMultiplication.AuxiliarySeparation.Integral
