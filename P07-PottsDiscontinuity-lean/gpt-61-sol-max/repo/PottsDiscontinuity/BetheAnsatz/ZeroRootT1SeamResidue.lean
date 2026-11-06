module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Residue
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1SeamPair

/-!
# The seam residue and paired limit

At a seam ML edge the unique pole is the cyclic edge from the last slot to
slot zero. Its residue combines with the corrected phase slope containing `N`.
-/

@[expose] public section

open Finset Complex Filter Topology Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The amplitude-weighted seam word term has an explicit pole residue. -/
theorem tendsto_t_mul_perturbedWordTerm_seam {N n : ℕ} {c : ℝ}
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (hn : 0 < n)
    (hsig : σ 0 = l) (hLast : w (Fin.last n) = false) (hZero : w 0 = true) :
    Tendsto (fun t : ℝ => (t : ℂ) *
      perturbedWordTerm (N := N) c x p l t σ w) (𝓝[≠] (0 : ℝ))
      (𝓝 (I * ((c : ℂ)^2 * amplitude (anisotropy c) p σ *
        M c (z (p (σ (Fin.last n)))) *
        wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w (Fin.last n) *
        wordPhase (N := N) x p σ w))) := by
  let u := Fin.last n
  
  have hrot : finRotate (n + 1) u = 0 := by simp [u]
  have hσu : σ u ≠ l := by
    aesop
  
  let m := M c (z (p (σ u)))
  let q (t : ℝ) := perturbedMomenta p l t
  let edge (t : ℝ) := wordEdgeFactor c (q t) σ w u
  let rest (t : ℝ) := ∏ k ∈ (univ ).erase u,
    wordEdgeFactor c (q t) σ w k
  have hlocal (t : ℝ) : edge t = m * L c (z t) - 1 := by
    aesop  (add norm (by omega))  (add simp [z, perturbedMomenta, wordEdgeFactor])
       (add unsafe apply [_root_.congrArg, _root_.zero_add])
  have hrest : ∀ t, rest t = rest 0 := by
    intro t
    
    apply Finset.prod_congr rfl
    intro k hk
    
    have hnext : finRotate (n + 1) k ≠ 0 := by
      simp_all <;> grind
    
    have h3 := perturbedMomenta_of_ne p l (σ (finRotate (n + 1) k)) t (by
                                                                         aesop)
    have h4 := perturbedMomenta_of_ne p l (σ (finRotate (n + 1) k)) 0 (by
                                                                         aesop)
    cases hw : w k <;> cases hnxt : w (finRotate (n + 1) k)
    · have hσk : σ k ≠ l := by
        aesop
      
      
      unfold wordEdgeFactor
      simp only [q, hw, hnxt, Bool.false_eq_true, ↓reduceIte]
      rw [ perturbedMomenta_of_ne p l (σ k) t hσk ,  perturbedMomenta_of_ne p l (σ k) 0 hσk ]
    · have hσk : σ k ≠ l := by
        aesop
      
      
      unfold wordEdgeFactor
      simp only [q, hw, hnxt, Bool.false_eq_true, ↓reduceIte]
      rw [ perturbedMomenta_of_ne p l (σ k) t hσk ,  perturbedMomenta_of_ne p l (σ k) 0 hσk , h3, h4]
    · simp_all [wordEdgeFactor]
    · unfold wordEdgeFactor
      grind
  have hprod (t : ℝ) : wordCoefficient c (q t) σ w = edge t * rest t := Eq.symm (mul_prod_erase univ (wordEdgeFactor c (q t) σ w) (mem_univ u))
  have hlocalLimit : Tendsto (fun t  =>  t  * edge t)
      (𝓝[≠]  0 ) (𝓝 (m * (I *  c ^2))) := by
    
    
    have heq : (fun t  =>  t  * edge t) =
      fun (t : ℝ) => m * ( t  * L c (z t)) -  t  := by
      funext t
      rw [hlocal]
      ring
    rw [heq]
    simpa using (tendsto_const_nhds.mul (tendsto_t_mul_L_z_zero c)).sub ((continuous_ofReal.continuousAt : ContinuousAt (fun t : ℝ => (t : ℂ)) 0)
                                                      |>.tendsto.mono_left nhdsWithin_le_nhds)
  have hphase : Continuous  fun t  => wordPhase (N := N) x (q t) σ w  := by
    unfold wordPhase positionPhase q perturbedMomenta
    fun_prop
  
  have hrestT : Tendsto (fun _  => rest 0) (𝓝[≠] (0 : ℝ)) (𝓝 (rest 0)) :=
    tendsto_const_nhds
  have hphaseT : Tendsto (fun t  => wordPhase (N := N) x (q t) σ w)
      (𝓝[≠]  0 ) (𝓝 (wordPhase (N := N) x p σ w)) := by
    have h0 : q 0 = p := by
      funext k
      by_cases hk : k = l
      · 
        simp [q, perturbedMomenta]
      · simp [q, perturbedMomenta]
    convert hphase.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    rw [h0]
  
  have hA : Tendsto (fun _  => amplitude (anisotropy c) p σ)
      (𝓝[≠] (0 : ℝ)) (𝓝 (amplitude (anisotropy c) p σ)) := tendsto_const_nhds
  have hlim := hA.mul ((hlocalLimit.mul hrestT).mul hphaseT)
  have hfun' : (fun t : ℝ =>  t  *
      perturbedWordTerm (N := N) c x p l t σ w) =
      fun (t : ℝ) => amplitude (anisotropy c) p σ *
        ( t  * edge t * rest 0 * wordPhase (N := N) x (q t) σ w) := by
    calc
      _ = fun (t : ℝ) => amplitude (anisotropy c) p σ *
          ( t  * edge t * rest 0) * wordPhase (N := N) x (q t) σ w :=  by
                                                                             funext t
                                                                             unfold perturbedWordTerm
                                                                             rw [hprod t, hrest t]
                                                                             
                                                                             ring 
      _ = _ := by funext t; ring
  have hvalue : amplitude (anisotropy c) p σ *
      (m * (I *  c ^2) * rest 0 * wordPhase (N := N) x p σ w) =
      I * ( c ^2 * amplitude (anisotropy c) p σ * m * rest 0 *
        wordPhase (N := N) x p σ w) := by ring
  rw [← hfun', hvalue] at hlim
  have hrest0 : rest 0 =
      wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w u := rfl
  rw [hrest0] at hlim
  simpa [m, u] using hlim

/-- The seam-paired terms have a finite limit with the corrected phase slope,
including the additional `N` contribution. -/
theorem tendsto_seamT1_pair {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0) (hBE : BetheEquations N (anisotropy c) p)
    (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) (hn : 0 < n)
    (hsig : σ 0 = l) (hLast : w (Fin.last n) = false) (hZero : w 0 = true) :
    Tendsto (fun t : ℝ =>
      perturbedWordTerm (N := N) c x p l t σ w +
        perturbedWordTerm (N := N) c x p l t
          (σ * Equiv.swap (Fin.last n) 0) w)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ( (c : ℂ)^2 * amplitude (anisotropy c) p σ *
          M c (z (p (σ (Fin.last n)))) *
          wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w (Fin.last n) *
          wordPhase (N := N) x p σ w  *
        (zeroRootPhaseDerivative (N := N) (anisotropy c)
          (p (σ (Fin.last n))) True : ℂ))) := by
  let f  := fun t => Complex.exp (I *
     zeroRootPhaseExponent (N := N) (anisotropy c)
      (p (σ (Fin.last n))) True t )
  
  
  
  
  
  have hf0 : f 0 = 1 := by simp [f, zeroRootPhaseExponent]
   
  have heq : (fun t  =>
      perturbedWordTerm (N := N) c x p l t σ w +
        perturbedWordTerm (N := N) c x p l t
          (σ * Equiv.swap (Fin.last n) 0) w) =ᶠ[𝓝[≠] (0 )]
      fun t => perturbedWordTerm (N := N) c x p l t σ w * (1 - f t) := by
    filter_upwards [eventually_z_ne_one_zero] with t ht
    rw [perturbedWordTerm_seam_pair hc x p hp hinj l hpl hBE t ht σ w
      hn hsig hLast hZero]
    
    ring
  
  simpa  using  (tendsto_pole_mul_one_sub_of_hasDerivAt (hasDerivAt_zeroRootPhaseExp hc True) hf0  (tendsto_t_mul_perturbedWordTerm_seam (N := N) (c := c) x p hinj
                                                                                                                            l hpl σ w hn hsig hLast hZero)).congr' heq.symm 

end PottsDiscontinuity.BetheAnsatz
