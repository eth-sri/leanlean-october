/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Analysis.PrimeCutoff
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimes
public import CCDN.Determinant.HypersurfaceLocalDivisor
public import CCDN.Height.CountingHypotheses
import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates
import CCDN.Determinant.PrimeAggregation

/-! Choosing the prime endpoint at the dimension root of the row count
produces the exact rank power and leading constant in CCDN Proposition 3.2.6.
The aggregation step takes the local prime-power divisors as a hypothesis, so it
applies to minor gcds, determinant-family gcds and affine-chart reductions alike. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- An explicit error depending only on hypersurface dimension. -/
def hypersurfaceDeterminantError (n : ℕ) : ℝ :=
  (n + 1 : ℝ) *
      (Real.log 27 + 2 * mertensError + 2 * hypersurfaceCountConstant n * primeBlockMass) +
    (n + 2 : ℝ) ^ 2 / ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) * (Real.log 4 + 4)

/-- The rank form of the lower bound in CCDN Proposition 3.2.6 for `s` points on a
hypersurface of degree `d` with bad-prime charge `c`:
`((n+1)!)^(1/(n+1)) / (n+2) * s^(1+1/(n+1)) * (log s - (n+1) (4 log d + c) - E_n)`. -/
def hypersurfaceRankLowerBound (n s d : ℕ) (c : ℝ) : ℝ :=
  factorialRoot n / (n + 2 : ℝ) * (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) *
    (Real.log s - (n + 1 : ℝ) * (4 * Real.log d + c) - hypersurfaceDeterminantError n)

private lemma hypersurface_rank_prime_endpoint (n s : ℕ) (hs : 0 < s) :
    1 ≤ (s : ℝ) ^ (1 / (n + 1 : ℝ)) := by
  apply Real.one_le_rpow
  · exact_mod_cast hs
  · positivity

private lemma hypersurface_determinant_rank_identity (n s d : ℕ) (hs : 0 < s) (charge : ℝ) :
    hypersurfaceDeterminantMain n s *
        (Real.log ((s : ℝ) ^ (1 / (n + 1 : ℝ))) - 4 * Real.log d - Real.log 27 -
          2 * mertensError - charge - 2 * hypersurfaceCountConstant n * primeBlockMass) -
        ((n + 2 : ℝ) * s) * ((Real.log 4 + 4) * (s : ℝ) ^ (1 / (n + 1 : ℝ))) =
      hypersurfaceRankLowerBound n s d charge := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  
  
  
  have hp : (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) =
      (s : ℝ) * (s : ℝ) ^ (1 / (n + 1 : ℝ)) := by
    rw [Real.rpow_add hs0, Real.rpow_one]
  rw [Real.log_rpow hs0]
  unfold hypersurfaceRankLowerBound hypersurfaceDeterminantMain hypersurfaceDeterminantError
  rw [hp]
  field_simp
  ring

/-- The ordinary and smooth-congruence determinant bounds share the same
rank-cutoff sum, with an extra contribution from any prescribed primes. -/
theorem hypersurface_determinant_log_lower_at_rank {n s N d M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    {F : Fin N → MvPolynomial (Fin (n + 3)) ℤ} {z : Fin s → IntPoint (n + 3)}
    (hev : IsIndependentEvaluation f M F z)
    (bad : Finset ℕ)
    (hbad : ∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (v : ℕ)
    (hcong : ∀ p ∈ P, (p : ℤ) ^ v ∣ minorGcd (Matrix.of fun i j => eval (z i) (F j))) :
    hypersurfaceRankLowerBound n s d (∑ p ∈ bad ∪ P, Real.log p / p) +
      (v : ℝ) * (∑ p ∈ P, Real.log p) ≤ Real.log (minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  have h := determinant_log_lower_of_local_divisors
    (hypersurface_rank_prime_endpoint n s hs) hd (hypersurfaceCountConstant_nonneg n)
    (hypersurfaceDeterminantMain_nonneg n s) (show 0 ≤ (n + 2 : ℝ) * s by positivity) bad P hP v
    (one_pos.trans_le (one_le_minorGcd hev.rows_linearIndependent)) (fun p hp => ?_) hcong
  · rwa [hypersurface_determinant_rank_identity n s d hs] at h
  obtain ⟨hp, hn, hcut⟩ := mem_determinantPrimes hp
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨_, hir⟩ := hasGoodReduction_of_not_mem hbad p (fun hb => hn (mem_union_left P hb)) hcut
  exact projective_hypersurface_minorGcd_dvd hs f hf hd hir hcut F hev.isHomogeneous z hev.primitive
    hev.eval_eq_zero

end
end CCDN
