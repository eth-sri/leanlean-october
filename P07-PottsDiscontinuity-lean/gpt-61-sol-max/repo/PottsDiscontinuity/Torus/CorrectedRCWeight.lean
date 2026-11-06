module
public import Mathlib

public import PottsDiscontinuity.Torus.RCWeight
public import PottsDiscontinuity.TorusLoops.WindingLoopCount

/-! # The corrected RC summand with the homological `ell₀` statistic -/

@[expose] public section

open PottsDiscontinuity.TorusLoops

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The RC summand in Corollary 3.13, with `ell₀` taken to be the homological loop count
`windingLoopCount` (loops with nonzero vertical or horizontal seam winding). -/
noncomputable def torusCorrectedRCWeight
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M)
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) : ℝ :=
  torusRCWeight hN hM q A *
    (2 / Real.sqrt q.val) ^ windingLoopCount hN hM i j A /
      q.val ^ rcNetIndicator hN hM A

section

variable (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M)


/-- The homological loop count is a subset cardinality of the full loop carrier. -/
theorem windingLoopCount_le_rcLoopCount
     (A : RCConfig N M) :
    windingLoopCount hN hM i j A ≤ rcLoopCount hN hM A := by
  
  calc
    (windingLoopSet hN hM i j A).card ≤
        (Finset.univ ).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = rcLoopCount hN hM A := by simp [rcLoopCount, loopCount]

/-- Lemma 3.9 rewrites the corrected RC summand as one factor per
homologically contractible or winding loop, with `ell₀` taken to be the homological
count `windingLoopCount`. -/
theorem torusCorrectedRCWeight_eq_loopFactors
    
    (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    torusCorrectedRCWeight hN hM i j q A =
      torusNormalization q N M *
        2 ^ windingLoopCount hN hM i j A *
          Real.sqrt q.val ^
            (rcLoopCount hN hM A - windingLoopCount hN hM i j A) := by
  let t  := Real.sqrt q.val
  let ell := rcLoopCount hN hM A
  let ell₀ := windingLoopCount hN hM i j A
  let s := rcNetIndicator hN hM A
  
  have ht : 0 < t := by  exact Real.sqrt_pos.2 (lt_of_lt_of_le (by norm_num) q.property)
  
  have hell : ell₀ ≤ ell := by
    grind [windingLoopCount_le_rcLoopCount]
  have hqpow : q.val ^ s = t ^ (2 * s) := by
    rw [←  Real.sq_sqrt (le_trans (by norm_num) q.property) , pow_mul]
  have hratio : (2 / t) ^ ell₀ = (2 ) ^ ell₀ / t ^ ell₀ := by
    rw [div_pow]
  have hsplit : ell + 2 * s =  ell - ell₀  + (ell₀ + 2 * s) := by omega
  unfold torusCorrectedRCWeight
  
  rw [torusRCWeight_eq_loopWeight hN hM q A, hratio, hqpow, hsplit]
  field_simp 
  ring

end

end PottsDiscontinuity.Torus
