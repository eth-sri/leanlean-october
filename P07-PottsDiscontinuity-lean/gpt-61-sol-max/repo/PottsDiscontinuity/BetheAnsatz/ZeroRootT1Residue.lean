module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Analytic
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Ordinary
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Pairing
public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Phase

/-!
# Residue and cancellation for an ordinary T₁ pair

At an ordinary ML edge carrying the moved zero root on its L end, exactly one
word-coefficient edge factor has a pole. The fixed-amplitude pair cancels that
pole against the first-order scattering phase.
-/

@[expose] public section

open Finset Complex Filter Topology Classical

namespace PottsDiscontinuity.BetheAnsatz

/-- The coefficient product with one selected cyclic edge removed. -/
noncomputable def wordCoefficientEraseEdge {n : ℕ} (c : ℝ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (a : Fin (n + 1))  :=
  ∏ k ∈ (univ : Finset (Fin (n + 1))).erase a, wordEdgeFactor c p σ w k

/-- The pole residue of the amplitude-weighted ordinary word term. -/
theorem tendsto_t_mul_perturbedWordTerm {N n : ℕ} {c : ℝ}
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (a : Fin n)
    (hsig : σ a.succ = l) (ha : w a.castSucc = false) (hb : w a.succ = true) :
    Tendsto (fun t : ℝ => (t : ℂ) *
      perturbedWordTerm (N := N) c x p l t σ w) (𝓝[≠] (0 : ℝ))
      (𝓝 (I * ((c : ℂ)^2 * amplitude (anisotropy c) p σ *
        M c (z (p (σ a.castSucc))) *
        wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w a.castSucc *
        wordPhase (N := N) x p σ w))) := by
  
  have hσa : σ a.castSucc ≠ l := by
    aesop
  
  let m := M c (z (p (σ a.castSucc)))
  let q (t : ℝ) := perturbedMomenta p l t
  let edge (t : ℝ) := wordEdgeFactor c (q t) σ w a.castSucc
  let rest (t : ℝ) := ∏ k ∈ (univ ).erase a.castSucc,
    wordEdgeFactor c (q t) σ w k
  have hlocal (t : ℝ) : edge t = m * L c (z t) - 1 := by
    dsimp [edge, q, m]
    
    have hother  :=
      perturbedMomenta_of_ne p l (σ a.castSucc) t hσa
    unfold wordEdgeFactor
    simp_all
  have hrest : ∀ t, rest t = rest 0 := by
    intro t
    
    apply Finset.prod_congr rfl
    intro k hk
    
    have hnext : finRotate (n + 1) k ≠ a.succ := by
      intro he
      apply  (mem_erase.mp hk).1 
      exact (finRotate (n + 1)).injective (he.trans (finRotate_of_lt a.isLt).symm)
    
    have h3 := perturbedMomenta_of_ne p l (σ (finRotate (n + 1) k)) t (by
                                                                         aesop)
    have h4 := perturbedMomenta_of_ne p l (σ (finRotate (n + 1) k)) 0 (by
                                                                         aesop)
    unfold wordEdgeFactor
    cases hw : w k <;> cases hn : w (finRotate (n + 1) k)
    · 
      
      
      
      simp only [q, Bool.false_eq_true, ↓reduceIte]
      rw [ perturbedMomenta_of_ne p l (σ k) t (by
                                                            aesop) ,  perturbedMomenta_of_ne p l (σ k) 0 (by
                                                                aesop) ]
    · 
      
      
      
      simp only [q, Bool.false_eq_true, ↓reduceIte]
      rw [ perturbedMomenta_of_ne p l (σ k) t (by
                                                            aesop) ,  perturbedMomenta_of_ne p l (σ k) 0 (by
                                                                aesop) , h3, h4]
    all_goals grind
  have hprod (t : ℝ) : wordCoefficient c (q t) σ w = edge t * rest t := Eq.symm (mul_prod_erase univ (wordEdgeFactor c (q t) σ w) (mem_univ a.castSucc))
  have hlocalLimit : Tendsto (fun t : ℝ =>  t  * edge t)
      (𝓝[≠]  0 ) (𝓝 (m * (I *  c ^2))) := by
    
    
    have heq : (fun t  =>  t  * edge t) =
        fun (t : ℝ) => m * ( t  * L c (z t)) -  t  := by
      funext t
      rw [hlocal]
      ring
    rw [heq]
    simpa using (tendsto_const_nhds.mul (tendsto_t_mul_L_z_zero c)).sub ((continuous_ofReal.continuousAt : ContinuousAt (fun t : ℝ => (t : ℂ)) 0)
                                                      |>.tendsto.mono_left nhdsWithin_le_nhds)
  have hphase : Continuous  fun t  =>
      wordPhase (N := N) x (q t) σ w  := by
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
        ( t  * edge t * rest 0 *
          wordPhase (N := N) x (q t) σ w) := by
    calc
      _ = fun (t : ℝ) => amplitude (anisotropy c) p σ *
          ( t  * edge t * rest 0) *
            wordPhase (N := N) x (q t) σ w :=  by
                                                 grind [perturbedWordTerm] 
      _ = _ := by funext t; ring
  have hvalue : amplitude (anisotropy c) p σ *
      (m * (I *  c ^2) * rest 0 *
        wordPhase (N := N) x p σ w) =
      I * ( c ^2 * amplitude (anisotropy c) p σ * m * rest 0 *
        wordPhase (N := N) x p σ w) := by ring
  rw [← hfun', hvalue] at hlim
  have hrest0 : rest 0 =
      wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w a.castSucc := rfl
  rw [hrest0] at hlim
  simpa [m] using hlim

/-- The ordinary-edge paired terms have a finite limit, given by the phase slope
times the explicit pole residue. -/
theorem tendsto_ordinaryT1_pair {N n : ℕ} {c : ℝ} (hc : 2 < c)
    (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ)
    (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi) (hinj : Function.Injective p)
    (l : Fin (n + 1)) (hpl : p l = 0) (σ : Equiv.Perm (Fin (n + 1)))
    (w : Fin (n + 1) → Bool) (a : Fin n)
    (hsig : σ a.succ = l) (ha : w a.castSucc = false) (hb : w a.succ = true) :
    Tendsto (fun t : ℝ =>
      perturbedWordTerm (N := N) c x p l t σ w +
        perturbedWordTerm (N := N) c x p l t
          (σ * Equiv.swap a.castSucc a.succ) w)
      (𝓝[≠] (0 : ℝ))
      (𝓝 ( (c : ℂ)^2 * amplitude (anisotropy c) p σ *
          M c (z (p (σ a.castSucc))) *
          wordCoefficientEraseEdge c (perturbedMomenta p l 0) σ w a.castSucc *
          wordPhase (N := N) x p σ w  *
        (zeroRootPhaseDerivative (N := N) (anisotropy c)
          (p (σ a.castSucc)) False : ℂ))) := by
  let f  := fun t => Complex.exp (I *
     zeroRootPhaseExponent (N := N) (anisotropy c)
      (p (σ a.castSucc)) False t )
  
  
  
  
  
  have hf0 : f 0 = 1 := by simp [f, zeroRootPhaseExponent]
   
  have heq : (fun t  =>
      perturbedWordTerm (N := N) c x p l t σ w +
        perturbedWordTerm (N := N) c x p l t
          (σ * Equiv.swap a.castSucc a.succ) w) =ᶠ[𝓝[≠] (0 )]
      fun t => perturbedWordTerm (N := N) c x p l t σ w * (1 - f t) := by
    filter_upwards [eventually_z_ne_one_zero] with t ht
    rw [perturbedWordTerm_adjacent_pair hc x p hp hinj l hpl t ht σ w a hsig ha hb]
    simp only [f, zeroRootPhaseExponent, ite_false, add_zero, Pi.sub_apply,
      Complex.ofReal_sub]
    ring
  
  simpa  using  (tendsto_pole_mul_one_sub_of_hasDerivAt (hasDerivAt_zeroRootPhaseExp hc False) hf0  (tendsto_t_mul_perturbedWordTerm (N := N) (c := c) x p hinj l hpl σ w a hsig ha hb)).congr' heq.symm 

end PottsDiscontinuity.BetheAnsatz
