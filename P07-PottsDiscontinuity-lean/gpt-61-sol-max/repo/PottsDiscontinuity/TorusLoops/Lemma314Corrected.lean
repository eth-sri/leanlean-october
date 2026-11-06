module
public import Mathlib

public import PottsDiscontinuity.TorusLoops.LoopDensityLogBounds
public import PottsDiscontinuity.TorusLoops.LoopTailBoundaryDecay

/-!
# Corrected Lemma 3.14

The source proof yields a limsup estimate, not the existence of a width limit.
This is the corrected statement, with the rotated-lattice free one-arm decay
provided as its sole additional premise.
-/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.FK
open PottsDiscontinuity.Zhang

/-- At the critical point, the normalized logarithm of the loop observable has
vanishing limsup in absolute value as the even circumference tends to infinity.
The only additional input is decay of the rotated-lattice free one-arm
probability. -/
theorem lemma_3_14_corrected_limsup
    (q : Set.Ici (1 : ℝ))
    (hzero : Tendsto
      (fun n => (((Classical.choose (freeBoxLimit_existsUnique
        (rectangleFKParameters q))) (boundaryConnectionEvent n) : NNReal) : ℝ))
      atTop (𝓝 0)) :
    ∀ ε > 0, ∃ N₀ : {k : ℕ // 2 ≤ k}, ∀ N, (hN : Even N) →
      (hN₀ : N₀.val ≤ N) →
      Filter.limsup
        (fun n => abs (windingLoopDensityLogRate hN (by omega) q n)) atTop ≤ ε := by
  intro ε hε
  
  let C₀ := windingLoopDensityLogOffset q
  let C₁ := windingLoopDensityLogSlope q
  
  
  obtain ⟨r, hrlarge⟩ := exists_nat_gt (C₁ / ε)
  have hr : 0 < r := by
    by_contra hn
    have : (r : ℝ) = 0 := by exact_mod_cast  Nat.eq_zero_of_not_pos hn 
    
    have hC1div  := div_nonneg (windingLoopDensityLogSlope_nonneg q) hε.le
    linarith
  have hrR  := hrlarge
  have hfirst : C₁ / (2 *  r ) < ε / 2 := by
    
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith [ by
                  simpa  using (div_lt_iff₀ hε).mp hrR ]
  
  
  
  obtain ⟨Narm, hNarm⟩ := Filter.eventually_atTop.1 (by
                                                       filter_upwards [(tendsto_rectangleFreeOneArmProbability_of_boundaryConnection_zero q hzero).eventually (Iio_mem_nhds (windingLoopTailArmThreshold_pos q r))] with N hN
                                                       exact hN.le)
  refine ⟨⟨max Narm 2, ?_⟩, ?_⟩
  · exact le_max_right _ _
  · intro N hN hN₀
    
    
    have hNp  := lt_of_lt_of_le (by decide : 0 < 2) ((le_max_right _ _).trans hN₀)
    
    
    let C := C₀ + C₁
    
    obtain ⟨Kε, hKε⟩ := exists_nat_gt (C / ε)
    
    let Kgeom := max N (r * (9 * N))
    
    have hEventually : ∀ᶠ n : ℕ in atTop,
        |windingLoopDensityLogRate hN hNp q n| ≤ ε := by
      filter_upwards [eventually_ge_atTop (max Kgeom Kε)] with n hn
      
      
      
      have hmul :  9 * N  * r ≤ n + 1 := by
        grind
      have hdiv  := (Nat.le_div_iff_mul_le hr).2 hmul
      
      have hrate := abs_windingLoopDensityLogRate_le hN hNp q r n hr
        (by omega) (by omega)  (hNarm N ((le_max_left Narm 2).trans hN₀)) 
      
      
      have hrem : (C₀ + C₁) / (2 *  (n + 1 : ℕ) ) < ε / 2 := by
        
        
        have hmono : C / (2 *  (n + 1 : ℕ) ) ≤
            C / (2 *  (Kε + 1 : ℕ) ) := by
          exact div_le_div_of_nonneg_left (add_nonneg (windingLoopDensityLogOffset_nonneg q) (windingLoopDensityLogSlope_nonneg q)) (by positivity) (by
                                                      have hncast : ((Kε + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
                                                        exact_mod_cast Nat.succ_le_succ (le_trans (le_max_right Kgeom Kε) hn)
                                                      nlinarith)
        exact hmono.trans_lt (by simpa  using (by
                                                 have hmul : C < ε * (Kε ) := by
                                                   simpa [mul_comm] using (div_lt_iff₀ hε).mp hKε
                                                 have hcastK : ((Kε + 1 : ℕ) ) = (Kε : ℝ) + 1 := by norm_cast
                                                 
                                                 apply (div_lt_iff₀ (by positivity)).2
                                                 exact hmul.trans (by  nlinarith )))
      have hrate' : |windingLoopDensityLogRate hN hNp q n| < ε := by
        linarith
      exact hrate'.le
    
    exact Filter.limsup_le_of_le (Filter.isCoboundedUnder_le_of_le atTop  fun n => abs_nonneg _ ) hEventually

end PottsDiscontinuity.TorusLoops
