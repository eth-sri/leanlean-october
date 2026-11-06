module
public import Mathlib

public import PottsDiscontinuity.TorusLoops.LoopDensityObservable
public import PottsDiscontinuity.TorusLoops.LoopTailSeamBound

/-!
# Finite-volume expectation bounds from the winding-loop tail

These inequalities are the finite-sum form of the truncation step in (3.18).
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus
open PottsDiscontinuity.TorusRC
open scoped Classical

variable {N M : ℕ}

noncomputable section

section

variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M))


private theorem torusRC_sum_mass_indicator
     :
    ∑ A, torusRCMass hN hM q A * (if A ∈ E then (1 : ℝ) else 0) =
      phi_T_probability hN hM q E := by
  
  erw [phi_T_probability_eq_sum]
  aesop

private theorem torusRC_sum_scaled_indicator
     (c : ℝ) :
    ∑ A, torusRCMass hN hM q A *
      (c *  if A ∈ E then (1 : ℝ) else 0 ) =
        c * phi_T_probability hN hM q E := by
  
  calc
    ∑ A, torusRCMass hN hM q A *
        (c *  if A ∈ E then  1  else 0 ) =
      ∑ A, c * (torusRCMass hN hM q A *
         if A ∈ E then  1  else 0 ) := by
          grind
    _ = c * ∑ A, torusRCMass hN hM q A *
         if A ∈ E then  1  else 0  := by rw [Finset.mul_sum]
    _ = c * phi_T_probability hN hM q E := by
      rw [torusRC_sum_mass_indicator]

private theorem torusRCProbability_compl
     :
    phi_T_probability hN hM q E + phi_T_probability hN hM q Eᶜ = 1 := by
  
  erw [phi_T_probability_eq_sum, phi_T_probability_eq_sum]
  
  calc
     ∑ A, E.indicator (torusRCMass hN hM q) A  +
        ∑ A, Eᶜ.indicator (torusRCMass hN hM q) A =
        ∑ A, (E.indicator (torusRCMass hN hM q) A +
          Eᶜ.indicator (torusRCMass hN hM q) A) := by rw [Finset.sum_add_distrib]
    _ = ∑ A, torusRCMass hN hM q A := by
      simp_all
    _ = 1 := sum_torusRCMass hN hM q

end

section

variable (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) (q : Set.Ici (1 : ℝ))


theorem phi_T_windingLoopDensityExpectation_pos
     :
    0 < phi_T_windingLoopDensityExpectation hN hM hNp hMp q := by
  
  apply Finset.sum_pos
  · intro A hA
    exact mul_pos (torusRCMass_pos hN hM q A)
      (windingLoopDensityWeight_pos hN hM hNp hMp q A)
  · simp_all

/-- The weighted expectation is bounded by a low-count contribution and the
global observable bound times the large-loop tail probability. -/
theorem phi_T_windingLoopDensityExpectation_le_tail
     (m : ℕ) :
    phi_T_windingLoopDensityExpectation hN hM hNp hMp q ≤
      windingLoopDensityUpperBase q ^ m +
        windingLoopDensityUpperBase q ^ (N + M) *
          phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m) := by
  
  let T := windingLoopTailEvent hN hM hNp hMp m
  have hpoint (A : RCConfig N M) :
      windingLoopDensityWeight hN hM hNp hMp q A ≤
        windingLoopDensityUpperBase q ^ m +
          windingLoopDensityUpperBase q ^ (N + M) *
             if A ∈ T then  1  else 0  := by
    by_cases ht : A ∈ T
    · 
      have hg := windingLoopDensityWeight_le_global hN hM hNp hMp q A
      have hn : 0 ≤ windingLoopDensityUpperBase q ^ m :=
        pow_nonneg (le_trans (by norm_num) (windingLoopDensityUpperBase_ge_one q)) _
      have hsum : windingLoopDensityUpperBase q ^ (N + M) ≤
          windingLoopDensityUpperBase q ^ m + windingLoopDensityUpperBase q ^ (N + M) :=
        le_add_of_nonneg_left hn
      simpa [ht] using hg.trans hsum
    · have hc : windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A < m := by
        grind [windingLoopTailEvent]
      have hl := windingLoopDensityWeight_le_of_count_le hN hM hNp hMp q m A hc.le
      simpa [ht] using hl
  have hsum := Finset.sum_le_sum (s := Finset.univ)  fun A hA =>
    mul_le_mul_of_nonneg_left (hpoint A) (torusRCMass_pos hN hM q A).le 
  
  
  
  calc
     ∑ A, torusRCMass hN hM q A * windingLoopDensityWeight hN hM hNp hMp q A  ≤
        ∑ A, torusRCMass hN hM q A *
          (windingLoopDensityUpperBase q ^ m +
            windingLoopDensityUpperBase q ^ (N + M) *
               if A ∈ T then  1  else 0 ) := hsum
    _ = windingLoopDensityUpperBase q ^ m +
          windingLoopDensityUpperBase q ^ (N + M) *
            phi_T_probability hN hM q T := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hfirst :  ∑ A, torusRCMass hN hM q A *
            windingLoopDensityUpperBase q ^ m  = windingLoopDensityUpperBase q ^ m := by
        rw [← Finset.sum_mul, (sum_torusRCMass hN hM q)]
        ring
      have hsecond :  ∑ A, torusRCMass hN hM q A *
            (windingLoopDensityUpperBase q ^ (N + M) *
               if A ∈ T then  1  else 0 )  =
          windingLoopDensityUpperBase q ^ (N + M) *
            phi_T_probability hN hM q T := by
        exact torusRC_sum_scaled_indicator hN hM q T (windingLoopDensityUpperBase q ^ (N + M))
      rw [hfirst, hsecond]

/-- The lower truncated-moment estimate. The tail loss is exactly the
probability of at least `m` nonzero-winding loops. -/
theorem phi_T_windingLoopDensityExpectation_ge_tail
     (m : ℕ) :
    windingLoopDensityLowerBase q ^ m / q.val *
        (1 - phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m)) ≤
      phi_T_windingLoopDensityExpectation hN hM hNp hMp q := by
  
  let L  :=
    {A | windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A < m}
  let T := windingLoopTailEvent hN hM hNp hMp m
  let : DecidablePred  fun A  => A ∈ L  := Classical.decPred _
  have hcompl : Lᶜ = T := by
    aesop
  have hprob :
      phi_T_probability hN hM q L +
        phi_T_probability hN hM q T = 1 := by
    grind [torusRCProbability_compl]
  have hpoint (A : RCConfig N M) :
      windingLoopDensityLowerBase q ^ m / q.val *
          (if A ∈ L then  1  else 0) ≤
        windingLoopDensityWeight hN hM hNp hMp q A := by
    by_cases hl : A ∈ L
    · 
      simpa [hl] using windingLoopDensityWeight_ge_of_count_lt
        hN hM hNp hMp q m A  hl 
    · 
      simpa [hl] using (windingLoopDensityWeight_pos hN hM hNp hMp q A).le
  have hsum := Finset.sum_le_sum (s := Finset.univ)  fun A hA =>
    mul_le_mul_of_nonneg_left (hpoint A) (torusRCMass_pos hN hM q A).le 
  have hprob' : phi_T_probability hN hM q L =
      1 - phi_T_probability hN hM q T := by linarith
  
  calc
    windingLoopDensityLowerBase q ^ m / q.val *
        (1 - phi_T_probability hN hM q T) ≤
      windingLoopDensityLowerBase q ^ m / q.val *
        phi_T_probability hN hM q L := by rw [hprob']
    _ = ∑ A, torusRCMass hN hM q A *
        (windingLoopDensityLowerBase q ^ m / q.val *
           if A ∈ L then (1 ) else 0 ) := by
      symm
      exact torusRC_sum_scaled_indicator hN hM q L
        (windingLoopDensityLowerBase q ^ m / q.val)
    _ ≤ ∑ A, torusRCMass hN hM q A *
        windingLoopDensityWeight hN hM hNp hMp q A := hsum

end

end

end PottsDiscontinuity.TorusLoops
