module

public import Mathlib
public import PottsDiscontinuity.BetheAnsatz.Defs

/-!
# Corollary 3.4: normalized Bethe eigenvalue

The inverse parameter is `ε = 1/Δ`.  The normalized `L` and `M` factors below are the
continuous extensions of `L/(-2Δ)` and `M/(-2Δ)`.  In the odd case, the derivative in the
zero-root eigenvalue formula is written in a rational form that is continuous at `ε=0`.
-/

@[expose] public section

open Finset Complex Filter Topology
open scoped BigOperators

namespace PottsDiscontinuity.SixVertex

/-- The derivative of the Bethe phase in its first variable, evaluated at zero. -/
theorem cor34_deriv_theta_at_zero {Δ y : ℝ} (hΔ : Δ < -1) :
    deriv (fun t : ℝ => Bethe.theta Δ t y) 0 =
      -1 + 2 * (1 + Real.cos y - 2 * Δ) /
        ((1 + Real.cos y - 2 * Δ) ^ 2 +  Real.sin y  ^ 2) := by
  let d  := 1 + Real.cos y - 2 * Δ
  have hd : 0 < d := by
    have hy := Real.neg_one_le_cos y
    
    linarith
  have hnum : HasDerivAt (fun t  => Real.sin t - Real.sin y) 1 0 := by
    simpa using (Real.hasDerivAt_sin 0).sub_const (Real.sin y)
  have hcos : HasDerivAt  Real.cos  0 0 := by
    simpa using  Real.hasDerivAt_cos 0 
  
  have hden : HasDerivAt
      (fun t  => Real.cos t + Real.cos y - 2 * Δ) 0 0 := by
    simp_all
  
  have hDpos : 0 < 1 + Real.cos y - 2 * Δ := by
    simpa [d] using hd
  have hfrac : HasDerivAt
      (fun t  => (Real.sin t - Real.sin y) /
        (Real.cos t + Real.cos y - 2 * Δ)) (1 / d) 0 := by
    have h := hnum.div hden (ne_of_gt (by
                                         rw [Real.cos_zero]
                                         simpa [d] using hd))
    convert h using 1
    rw [Real.sin_zero, Real.cos_zero]
    
    field_simp [ne_of_gt hDpos]; ring
  
  have htan' : HasDerivAt
      (fun t  => Real.arctan ((Real.sin t - Real.sin y) /
        (Real.cos t + Real.cos y - 2 * Δ)))
      (1 / (1 + ((Real.sin 0 - Real.sin y) /
          (Real.cos 0 + Real.cos y - 2 * Δ)) ^ 2) * (1 / d)) 0 := by
    convert  (Real.hasDerivAt_arctan ((Real.sin 0 - Real.sin y) /
                 (Real.cos 0 + Real.cos y - 2 * Δ))).comp 0 hfrac  using 1; rfl
  have hlin : HasDerivAt (fun t  => y - t) (-1) 0 := by
    convert (hasDerivAt_const 0 y).sub (hasDerivAt_id 0) using 1
    · 
      rfl
    · norm_num
  have htheta : HasDerivAt (fun t  => Bethe.theta Δ t y)
      (-1 + 2 * (1 / (1 + ((Real.sin 0 - Real.sin y) /
          (Real.cos 0 + Real.cos y - 2 * Δ)) ^ 2) * (1 / d))) 0 := by
    unfold Bethe.theta
    convert hlin.add (htan'.const_mul 2) using 1
  have hderiv := htheta.deriv
  
  have hEq :
       1 / (1 + ( -Real.sin y  / d) ^ 2) * (1 / d)  =
        d / (d ^ 2 +  Real.sin y  ^ 2) := by
    field_simp [ne_of_gt hd]
  have hderiv' : deriv (fun t  => Bethe.theta Δ t y) 0 =
      -1 + 2 * (1 / (1 + ( -Real.sin y  / d) ^ 2) * (1 / d)) := by
    simpa [d] using hderiv
  rw [hEq] at hderiv'
  convert hderiv' using 1; ring

/-- The rational continuation of the derivative correction in the odd zero-root formula. -/
noncomputable def cor34_derivativeCorrection (ε y : ℝ) : ℝ :=
  2 * ε * (ε * (1 + Real.cos y) - 2) /
    ((ε * (1 + Real.cos y) - 2) ^ 2 + ε ^ 2 *  Real.sin y  ^ 2)

/-- Continuous normalized regular `L` factor. -/
noncomputable def cor34_normalizedL (ε x : ℝ) : ℂ :=
   ((-ε / 2 : ℝ) : ℂ)  + ((1 - ε : ℝ) : ℂ) *
    BetheAnsatz.z x / (1 - BetheAnsatz.z x)

/-- Continuous normalized regular `M` factor. -/
noncomputable def cor34_normalizedM (ε x : ℝ) : ℂ :=
   ((-ε / 2 : ℝ) : ℂ)  - ((1 - ε : ℝ) : ℂ) /
    (1 - BetheAnsatz.z x)

/-- Regular eigenvalue expression after division by `(-2Δ)^n`. -/
noncomputable def cor34_normalizedRegularEigenvalue {n : ℕ} (ε : ℝ)
    (p : Fin n → ℝ)  :=
   ∏ j : Fin n, cor34_normalizedL ε (p j)  +
    ∏ j : Fin n, cor34_normalizedM ε (p j)

/-- Odd zero-root eigenvalue expression after division by `(-2Δ)^n`. -/
noncomputable def cor34_normalizedZeroEigenvalue {N n : ℕ} (ε : ℝ)
    (p : Fin n → ℝ) (l : Fin n) : ℂ :=
  (((-ε : ℝ) : ℂ) + ((1 - ε : ℝ) : ℂ) *
      ((N : ℝ) - 1 + ∑ j ∈ Finset.univ.erase l,
        (-1 + cor34_derivativeCorrection ε (p j)))) *
    ∏ j ∈ Finset.univ.erase l, cor34_normalizedM ε (p j)

section

variable {n : ℕ} {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
include hp

private theorem cor34_momentum_tendsto  (j : Fin n) :
    Tendsto (fun ε => BetheAnsatz.z (p ε j)) (𝓝 0)
      (𝓝 (BetheAnsatz.z (p 0 j))) := by
  
  
  have hz : Continuous  fun x : ℝ => BetheAnsatz.z x  := by
    dsimp [BetheAnsatz.z]
    fun_prop
  exact hz.continuousAt.tendsto.comp (((continuous_apply j).continuousAt).tendsto.comp hp)

section

variable (j : Fin n) (hz : BetheAnsatz.z (p 0 j) ≠ 1)
include hz

/-- The normalized regular `L` factor has the source limit at any nonzero base momentum. -/
theorem cor34_normalizedL_tendsto   :
    Tendsto (fun ε => cor34_normalizedL ε (p ε j)) (𝓝 0)
      (𝓝 (BetheAnsatz.z (p 0 j) / (1 - BetheAnsatz.z (p 0 j)))) := by
  have hZ := cor34_momentum_tendsto hp j
  
  
  
  have hScale : Tendsto (fun ε  =>  ((-ε / 2 : ℝ) : ℂ) ) (𝓝 0) (𝓝 0) := by
    have hc : Continuous  fun ε  =>  ((-ε / 2 : ℝ) : ℂ)   := by fun_prop
    simpa using (hc.continuousAt (x :=  0 )).tendsto
  have hOneMinus : Tendsto (fun ε  =>  ((1 - ε : ℝ) : ℂ) ) (𝓝 0) (𝓝 1) := by
    have hc : Continuous  fun ε  =>  ((1 - ε : ℝ) : ℂ)   := by fun_prop
    simpa using (hc.continuousAt (x :=  0 )).tendsto
  have hsum := hScale.add (hOneMinus.mul (hZ.div (tendsto_const_nhds.sub hZ) (sub_ne_zero.mpr (Ne.symm hz))))
  simpa [cor34_normalizedL, div_eq_mul_inv, mul_assoc] using hsum

/-- The normalized regular `M` factor has the source limit at any nonzero base momentum. -/
theorem cor34_normalizedM_tendsto   :
    Tendsto (fun ε => cor34_normalizedM ε (p ε j)) (𝓝 0)
      (𝓝 (-1 / (1 - BetheAnsatz.z (p 0 j)))) := by
  
  
  
  have hOne : Tendsto (fun _ : ℝ => (1 : ℂ)) (𝓝 0) (𝓝 1) := tendsto_const_nhds
  
  have hScale : Tendsto (fun ε  =>  ((-ε / 2 : ℝ) : ℂ) ) (𝓝 0) (𝓝 0) := by
    have hc : Continuous  fun ε  =>  ((-ε / 2 : ℝ) : ℂ)   := by fun_prop
    simpa using (hc.continuousAt (x :=  0 )).tendsto
  have hOneMinus : Tendsto (fun ε  =>  ((1 - ε : ℝ) : ℂ) ) (𝓝 0) (𝓝 1) := by
    have hc : Continuous  fun ε  =>  ((1 - ε : ℝ) : ℂ)   := by fun_prop
    simpa using (hc.continuousAt (x :=  0 )).tendsto
  have hsub := hScale.sub (hOneMinus.mul (hOne.div (tendsto_const_nhds.sub (cor34_momentum_tendsto hp j)) (sub_ne_zero.mpr (Ne.symm hz))))
  simpa [cor34_normalizedM, div_eq_mul_inv, mul_assoc] using hsub

end

/-- The normalized regular eigenvalue converges for every continuous momentum family whose
base momenta avoid zero. -/
theorem cor34_normalizedRegularEigenvalue_tendsto  (hz : ∀ j, BetheAnsatz.z (p 0 j) ≠ 1) :
    Tendsto (fun ε => cor34_normalizedRegularEigenvalue ε (p ε)) (𝓝 0)
      (𝓝 ( ∏ j : Fin n, BetheAnsatz.z (p 0 j) /
              (1 - BetheAnsatz.z (p 0 j))  +
            ∏ j : Fin n, (-1 : ℂ) / (1 - BetheAnsatz.z (p 0 j)))) := by
  have hL : Tendsto (fun ε => ∏ j : Fin n, cor34_normalizedL ε (p ε j))
      (𝓝 0) (𝓝 (∏ j : Fin n,
        BetheAnsatz.z (p 0 j) / (1 - BetheAnsatz.z (p 0 j)))) := by
    apply tendsto_finsetProd Finset.univ
    intro j hj
    exact cor34_normalizedL_tendsto hp j (hz j)
  have hM : Tendsto (fun ε => ∏ j : Fin n, cor34_normalizedM ε (p ε j))
      (𝓝 0) (𝓝 (∏ j : Fin n,
         -1  / (1 - BetheAnsatz.z (p 0 j)))) := by
    apply tendsto_finsetProd Finset.univ
    intro j hj
    exact cor34_normalizedM_tendsto hp j (hz j)
  
  simpa [cor34_normalizedRegularEigenvalue] using  hL.add hM 

/-- The rational derivative correction in the odd zero-root formula vanishes continuously
as `ε → 0`, even when the other momenta vary with `ε`. -/
theorem cor34_derivativeCorrection_tendsto  (j : Fin n) :
    Tendsto (fun ε => cor34_derivativeCorrection ε (p ε j)) (𝓝 0) (𝓝 0) := by
  
  have hpj  :=
    ((continuous_apply j).continuousAt).tendsto.comp hp
  have hcosFun : Continuous Real.cos := by fun_prop
  have hsinFun : Continuous Real.sin := by fun_prop
  
  have hsin := (hsinFun.continuousAt (x := p 0 j)).tendsto.comp hpj
  have hε : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0) := tendsto_id
  
  
  have hInner : Tendsto (fun ε  => ε * (1 + Real.cos (p ε j)) - 2)
      (𝓝 0) (𝓝 (-2)) := by
    simpa using (hε.mul (tendsto_const_nhds.add ((hcosFun.continuousAt (x := p 0 j)).tendsto.comp hpj))).sub  tendsto_const_nhds 
  have hSinSq : Tendsto (fun ε  =>  Real.sin (p ε j)  ^ 2)
      (𝓝 0) (𝓝 (Real.sin (p 0 j) ^ 2)) := by
    simpa [pow_two] using hsin.mul hsin
  have hNum : Tendsto
      (fun ε  => 2 * ε * (ε * (1 + Real.cos (p ε j)) - 2))
      (𝓝 0) (𝓝 0) := by
    
    simpa using ((tendsto_const_nhds).mul hε).mul hInner
  have hεsq : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝 0) (𝓝 0) := by
    simpa [pow_two] using hε.mul hε
  have hDen : Tendsto
      (fun ε  => (ε * (1 + Real.cos (p ε j)) - 2) ^ 2 +
        ε ^ 2 *  Real.sin (p ε j)  ^ 2)
      (𝓝 0) (𝓝  4 ) := by
    have hInnerSq := by simpa [pow_two] using hInner.mul hInner
    have hProd := hεsq.mul hSinSq
    convert hInnerSq.add hProd using 1
    all_goals grind
  
  have hquot := hNum.div hDen (by norm_num)
  have hfun : (fun ε  =>
       2 * ε * (ε * (1 + Real.cos (p ε j)) - 2)  /
        ((ε * (1 + Real.cos (p ε j)) - 2) ^ 2 +
          ε ^ 2 *  Real.sin (p ε j)  ^ 2)) =
      (fun ε  => 2 * ε * (ε * (1 + Real.cos (p ε j)) - 2)) /
         fun ε  => (ε * (1 + Real.cos (p ε j)) - 2) ^ 2 +
          ε ^ 2 *  Real.sin (p ε j)  ^ 2  := by
    
    rfl
  rw [← hfun] at hquot
  simpa [cor34_derivativeCorrection] using hquot

end

/-- The normalized odd zero-root eigenvalue has the source limit for a continuous family when
the nonzero base roots avoid `z=1`. -/
theorem cor34_normalizedZeroEigenvalue_tendsto {N n : ℕ} {p : ℝ → Fin n → ℝ}
    (hp : ContinuousAt p 0) (l : Fin n)
    (hz : ∀ j ∈ Finset.univ.erase l, BetheAnsatz.z (p 0 j) ≠ 1) :
    Tendsto (fun ε => cor34_normalizedZeroEigenvalue (N := N) ε (p ε) l) (𝓝 0)
      (𝓝 (((N : ℂ) - (n : ℂ)) *
        ∏ j ∈ Finset.univ.erase l,
          (-1 : ℂ) / (1 - BetheAnsatz.z (p 0 j)))) := by
  have hn  := Nat.zero_lt_of_lt l.isLt
  have hDeriv (j : Fin n) (hj : j ∈ Finset.univ.erase l) :
      Tendsto (fun ε  => -1 + cor34_derivativeCorrection ε (p ε j))
        (𝓝 0) (𝓝 (-1 )) := by
    
    simpa using  tendsto_const_nhds.add (cor34_derivativeCorrection_tendsto hp j) 
  have hSum : Tendsto
      (fun ε  => ∑ j ∈ Finset.univ.erase l,
        (-1 + cor34_derivativeCorrection ε (p ε j)))
      (𝓝 0) (𝓝 (- (n - 1 : ℕ) )) := by
    have h := tendsto_finsetSum (Finset.univ.erase l) hDeriv
    have hcard : (Finset.univ.erase l).card = n - 1 := by simp
    simpa [Finset.sum_const, hcard, Nat.cast_sub (by omega : 1 ≤ n)] using h
  
  
  have hneg : Tendsto (fun ε : ℝ => ( -ε  : ℂ)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous  fun ε : ℝ => ( -ε  : ℂ)  := by fun_prop
    simpa using (hc.continuousAt (x :=  0 )).tendsto
  have hOneMinus : Tendsto (fun ε  =>  ((1 - ε : ℝ) : ℂ) ) (𝓝 0) (𝓝 1) := by
    have hc : Continuous  fun ε  =>  ((1 - ε : ℝ) : ℂ)   := by fun_prop
    simpa using (hc.continuousAt (x :=  0 )).tendsto
  have hfirst := hneg.add (hOneMinus.mul (by
                                                                                     exact Tendsto.comp (ContinuousAt.tendsto (Continuous.continuousAt continuous_ofReal)) (by
                                                                                                                                                                              have hconst : Tendsto (fun _ : ℝ => (N : ℝ) - 1) (𝓝 0) (𝓝 ((N : ℝ) - 1)) :=
                                                                                                                                                                                tendsto_const_nhds
                                                                                                                                                                              have h := hconst.add hSum
                                                                                                                                                                              have hlim : (N : ℝ) - 1 + -((n - 1 : ℕ) : ℝ) = (N : ℝ) - n := by
                                                                                                                                                                                rw [Nat.cast_sub (by omega : 1 ≤ n)]
                                                                                                                                                                                ring
                                                                                                                                                                              simpa only [hlim] using h)))
  
  have hfinal := hfirst.mul (by
                               apply tendsto_finsetProd (Finset.univ.erase l)
                               intro j hj
                               exact cor34_normalizedM_tendsto hp j (hz j hj))
  simpa [cor34_normalizedZeroEigenvalue, div_eq_mul_inv, mul_assoc] using hfinal

end PottsDiscontinuity.SixVertex
