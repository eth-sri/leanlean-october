module
public import Mathlib

public import PottsDiscontinuity.Torus.NetEuler
public import PottsDiscontinuity.TorusLoops.FiniteEnergy

/-!
# The torus random-cluster loop weight identity

The proved Euler/net relation converts the critical RC weight into the loop weight
of Lemma 3.9, with the exact real-power normalization from the paper.
-/

@[expose] public section

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The exact factor C = q^(NM/4) (1 + sqrt q)^(-NM). -/
noncomputable def torusNormalization (q : Set.Ici (1 : ℝ)) (N M : ℕ) : ℝ :=
  q.val ^ ((N * M : ℝ) / 4) * (1 + Real.sqrt q.val) ^ (-(N * M : ℝ))

theorem torusNormalization_pos (q : Set.Ici (1 : ℝ)) (N M : ℕ) :
    0 < torusNormalization q N M := by
  
  apply mul_pos <;> apply Real.rpow_pos_of_pos
  · grind
  · positivity

theorem torusNormalization_eq_sqrt_pow (hN : Even N) (q : Set.Ici (1 : ℝ)) :
    torusNormalization q N M =
      Real.sqrt q.val ^ (N * M / 2) / (1 + Real.sqrt q.val) ^ (N * M) := by
  
  
  have hv :  (N * M / 2 : ℕ)  = (N * M : ℝ) / 2 := by
    have he :  2  * (N * M / 2 : ℕ) = (N * M : ℝ) := by exact_mod_cast  Nat.mul_div_cancel' (hN.mul_right M).two_dvd 
    linarith
  have hs : Real.sqrt q.val ^ (N * M / 2) = q.val ^ ((N * M : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (le_trans (by norm_num) q.property)]
    grind
  rw [torusNormalization, ← hs, Real.rpow_neg (by positivity), ← Nat.cast_mul, Real.rpow_natCast]
  rfl

/-- Lemma 3.9 on the actual indexed torus graph and the winding-defined net indicator. -/
theorem torusRCWeight_eq_loopWeight (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (A : RCConfig N M) :
    torusRCWeight hN hM q A = torusNormalization q N M *
      Real.sqrt q.val ^ (rcLoopCount hN hM A + 2 * rcNetIndicator hN hM A) := by
  let t := Real.sqrt q.val
  let d := 1 + t
  
  
  have hp : (rcCriticalParameter q).val = t / d := rfl
  have hc : 1 - (rcCriticalParameter q).val = 1 / d := by
    grind
  
  have he := euler_netIndicator hN hM A
  have hn : openCount A + 2 * clusterCount hN hM true A =
      N * M / 2 + (rcLoopCount hN hM A + 2 * rcNetIndicator hN hM A) := by omega
  calc
    torusRCWeight hN hM q A =
         t ^ openCount A * t ^ (2 * clusterCount hN hM true A)  /
          (d ^ openCount A * d ^ closedCount A) := by
      rw [torusRCWeight, hc, hp,  Trans.trans (congrArg (fun x => x ^ clusterCount hN hM true A) (Eq.symm (Real.sq_sqrt (le_trans (by norm_num) q.property))))
                                                                                                                         (Eq.symm (pow_mul t 2 (clusterCount hN hM true A))) , div_pow, div_pow, one_pow]
      grind
    _ = t ^ (openCount A + 2 * clusterCount hN hM true A) /
        d ^ (openCount A + closedCount A) := by rw [pow_add, pow_add]
    _ =  t ^ (N * M / 2) / d ^ (N * M)  *
        t ^ (rcLoopCount hN hM A + 2 * rcNetIndicator hN hM A) := by
      rw [hn, openCount_add_closedCount]
      ring
    _ = _ := by rw [torusNormalization_eq_sqrt_pow hN]

end PottsDiscontinuity.Torus
