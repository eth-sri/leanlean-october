/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Analysis.PrimeCutoff
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimes
public import CCDN.Plane.IntegerPlaneLogHeight
import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeHeight
import CCDN.AuxiliaryPolynomial.BadPrimeCharge

/-! Coordinate invariance of geometric bad reduction and coefficient height,
with the exact bad-prime charge in standard Fin-indexed coordinates. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma degree_le_stepanovThreshold (d : ℕ) : d ≤ stepanovThreshold d := by
  unfold stepanovThreshold
  nlinarith [Nat.le_self_pow (by decide : 4 ≠ 0) d]

section

variable {σ τ : Type*} (e : σ ≃ τ)
  (f : MvPolynomial σ ℤ)
include σ τ e f

/-- Geometric bad reduction at `p` is invariant under a bijective renaming of the
variables. -/
lemma hypersurfaceBadReduction_renameEquiv (p : ℕ) :
    HypersurfaceBadReduction (rename e f) p ↔ HypersurfaceBadReduction f p := by
  unfold HypersurfaceBadReduction
  apply exists_congr
  intro hp
  let : Fact p.Prime := ⟨hp⟩
  dsimp only
  have hd : (rename e f).totalDegree = f.totalDegree := totalDegree_renameEquiv e f
  have hd' : (rename e (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f)).totalDegree =
      (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f).totalDegree :=
    totalDegree_renameEquiv e _
  rw [map_rename, hd, hd']
  exact or_congr Iff.rfl (not_congr (MulEquiv.irreducible_iff (renameEquiv (AlgebraicClosure (ZMod p)) e)))

/-- A bound `H` on the coefficients of `f` also bounds the coefficients of `f` after a
bijective renaming of the variables. -/
lemma polynomial_coefficient_bound_renameEquiv (H : ℝ) (hf : CoefficientHeightLE f H) :
    CoefficientHeightLE (rename e f) H := by
  intro m
  have he : rename e.symm (rename e f) = f := by simp
  have hc := coeff_rename_mapDomain e.symm e.symm.injective (rename e f) m
  grind

end

section

variable {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] {n : ℕ}
  (f : MvPolynomial (Fin (n + 1)) ℤ)
include L n f

/-- The integer witness in the standard Fin-indexed coordinates. -/
theorem exists_fin_hypersurface_bad_prime_height_witness
    (hf : Irreducible (map (Int.castRingHom L) f)) (hd : 0 < f.totalDegree)
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H) :
    ∃ D : ℤ, 0 < D ∧
      Real.log D ≤ (27 * (f.totalDegree : ℝ) ^ 4) *
        (hypersurfaceHeightConstant (n + 1) *
          (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) ∧
      ∀ p, f.totalDegree < p → HypersurfaceBadReduction f p → (p : ℤ) ∣ D := by
  let e : Fin (n + 1) ≃ Option (Fin n) := finSuccEquiv' 0
  let g := rename e f
  have hg : Irreducible (map (Int.castRingHom L) g) := by
    rw [show g = rename e f from rfl, map_rename]
    exact (MulEquiv.irreducible_iff (renameEquiv L e)).mpr hf
  have hgd : g.totalDegree = f.totalDegree := totalDegree_renameEquiv e f
  obtain ⟨D, hD, hheight, hdiv⟩ := exists_hypersurface_bad_prime_height_witness g hg
    (hgd ▸ hd) H hH (polynomial_coefficient_bound_renameEquiv e f H hcoeff)
  refine ⟨D, hD, ?_, ?_⟩
  simp_all
  · intro p hp hbad
    apply hdiv p (hgd ▸ hp)
    exact (hypersurfaceBadReduction_renameEquiv e f p).mpr hbad

/-- The same witness gives the exact finite bad-prime set and bounds its charge. -/
theorem exists_fin_hypersurface_bad_prime_charge
    (hf : Irreducible (MvPolynomial.map (Int.castRingHom L) f))
    (hpos : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H) :
    ∃ P : Finset ℕ,
      (∀ p, p ∈ P ↔ stepanovThreshold f.totalDegree < p ∧ HypersurfaceBadReduction f p) ∧
      (∑ p ∈ P, Real.log p / p) ≤
        Real.log (hypersurfaceHeightConstant (n + 1) *
          (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) + 2 * mertensError + 1 := by
  classical
  obtain ⟨D, hD, hheight, hdiv⟩ :=
    exists_fin_hypersurface_bad_prime_height_witness f hf hpos H hH hcoeff
  let P := D.natAbs.primeFactors.filter (fun p =>
    stepanovThreshold f.totalDegree < p ∧ HypersurfaceBadReduction f p)
  have hdp := degree_le_stepanovThreshold f.totalDegree
  have hmem p : p ∈ P ↔ stepanovThreshold f.totalDegree < p ∧ HypersurfaceBadReduction f p := by
    simp only [P, Finset.mem_filter, Nat.mem_primeFactors]
    refine ⟨And.right, fun h => ⟨⟨h.2.choose, ?_, Int.natAbs_ne_zero.mpr hD.ne'⟩, h⟩⟩
    exact Int.natAbs_dvd_natAbs.mpr (hdiv p (hdp.trans_lt h.1) h.2)
  have hd1 : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hpos
  refine ⟨P, hmem, ?_⟩
  have hprime p hp := ((hmem p).mp hp).2.choose
  have hlog := prime_divisor_log_sum_le P hD hprime
    (fun p hp => hdiv p (hdp.trans_lt ((hmem p).mp hp).1) ((hmem p).mp hp).2)
  apply bad_prime_charge_of_log_sum P hprime _ _ _ (hlog.trans hheight)
  · nlinarith [one_le_pow₀ hd1 (n := 4)]
  · exact one_le_mul_of_one_le_of_one_le (hypersurfaceHeightConstant_one_le _)
      (le_add_of_nonneg_right (div_nonneg (Real.log_nonneg hH) (sq_nonneg _)))
  · intro p hp
    exact_mod_cast ((hmem p).mp hp).1


/-- Finiteness is invariant under the standard Fin-to-Option reindexing. -/
theorem finite_fin_hypersurface_bad_primes
    (hf : Irreducible (map (Int.castRingHom L) f)) (hpos : 0 < f.totalDegree) :
    {p : ℕ | stepanovThreshold f.totalDegree < p ∧ HypersurfaceBadReduction f p}.Finite := by
  have hH := integerCoefficientHeight_pos f (ne_zero_of_irreducible_map hf)
  obtain ⟨bad, hmem, _⟩ := exists_fin_hypersurface_bad_prime_charge f hf hpos
    (integerCoefficientHeight f) (by exact_mod_cast hH) (coefficient_abs_le_integerCoefficientHeight f)
  exact bad.finite_toSet.subset (fun p hp => (hmem p).mpr hp)

end

/-- For a nonzero homogeneous equation, degree loss is already included in
failure of geometric irreducibility, so the predicate agrees with the paper. -/
lemma homogeneous_hypersurfaceBadReduction_iff {σ : Type*} {d : ℕ}
    (f : MvPolynomial σ ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (p : ℕ) [Fact p.Prime] :
    HypersurfaceBadReduction f p ↔
      ¬Irreducible (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f) := by
  constructor
  · rintro ⟨_, hbad⟩ hi
    rcases hbad with hdegree | hnot
    · apply hdegree
      rw [hf.totalDegree hf0]
      exact (hf.map _).totalDegree hi.ne_zero
    tauto
  · intro hbad
    exact ⟨Fact.out, Or.inr hbad⟩

/-- Outside the bad-prime predicate, both full degree and geometric
irreducibility hold for the coefficient reduction. -/
lemma hypersurface_good_reduction {σ : Type*} (f : MvPolynomial σ ℤ)
    (p : ℕ) [Fact p.Prime] (hgood : ¬HypersurfaceBadReduction f p) :
    HasGoodReduction f p := by
  have hg : Irreducible (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f) := by
    by_contra hn
    exact hgood ⟨Fact.out, Or.inr hn⟩
  have he : (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).comp (Int.castRingHom (ZMod p)) =
      Int.castRingHom (AlgebraicClosure (ZMod p)) := by ext; simp
  have hi : Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) f)) := by
    simpa [map_map, he] using hg
  aesop

/-- The finite set of primes `p > 27 d ^ 4` of bad reduction of an absolutely
irreducible form of degree `d > 0`. -/
theorem exists_hypersurface_bad_prime_finset
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom L) f)) :
    ∃ bad : Finset ℕ, ∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p := by
  have hdeg : f.totalDegree = d := hf.totalDegree (ne_zero_of_irreducible_map hir)
  refine ⟨(finite_fin_hypersurface_bad_primes f hir (hdeg ▸ hd)).toFinset, fun p => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hdeg]

/-- A prime above the cutoff outside the bad-prime set has good reduction. -/
lemma hasGoodReduction_of_not_mem {σ : Type*} {f : MvPolynomial σ ℤ} {d : ℕ}
    {bad : Finset ℕ} (hbad : ∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p)
    (p : ℕ) [Fact p.Prime] (hp : p ∉ bad) (hcut : stepanovThreshold (d : ℝ) < p) :
    HasGoodReduction f p :=
  hypersurface_good_reduction f p fun hb => hp ((hbad p).mpr ⟨by exact_mod_cast hcut, hb⟩)

end
end CCDN
