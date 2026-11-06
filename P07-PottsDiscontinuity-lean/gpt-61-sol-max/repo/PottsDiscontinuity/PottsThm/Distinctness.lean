module
public import Mathlib

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.PottsThm.DiscontinuityConsequences
public import PottsDiscontinuity.PottsThm.OneSite

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.PottsThm


open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts

open PottsDiscontinuity.RCInfinite

theorem critical_potts_limits_pairwise_distinct (q : ℕ) (hq : 4 < q)
    (μ : Fin (q + 1) → ProbabilityMeasure (SpinSpace q))
    (φ₀ : ProbabilityMeasure LatticeConfiguration)
    (φp : Fin q → ProbabilityMeasure LatticeConfiguration)
    (hRC₀ : IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 0 φ₀.toMeasure)
    (hμ₀ : IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) 0 (μ 0).toMeasure)
    (hRCp : ∀ i : Fin q, IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 1 (φp i).toMeasure)
    (hμp : ∀ i : Fin q, IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) i.succ
      (μ i.succ).toMeasure)
    (L : ℝ) (hL : 0 < L)
    (hrate : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
      (φ₀.toMeasure.real
        {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
      atTop (𝓝 L)) :
    ∀ i j : Fin (q + 1), i ≠ j → (μ i).toMeasure ≠ (μ j).toMeasure := by
  have hq2 : 2 ≤ q := by omega
  have hβ  := pottsCriticalBeta_pos q hq
  
  have hφ₀weak : Tendsto
       (boxProbabilityMeasure (fkParameters q hq2 (pottsCriticalBeta q) hβ) (0, 0)) 
      atTop (𝓝 φ₀) := by
    have ht := boxMeasure_tendsto (criticalFKParameters q hq) 0 φ₀.toMeasure hRC₀
    have htarget :
         ⟨φ₀.toMeasure, hRC₀.1⟩  = φ₀ := by
      
      rfl
    rw [htarget] at ht
    simpa [criticalFKParameters] using ht
  have hφpweak (k : Fin q) : Tendsto
      (fun n => wiredBoxProbabilityMeasure
        (fkParameters q hq2 (pottsCriticalBeta q) hβ) (0, 0) n)
      atTop (𝓝 (φp k)) := by
    have ht := boxMeasure_tendsto (criticalFKParameters q hq) 1 (φp k).toMeasure (hRCp k)
    have htarget :
         ⟨(φp k).toMeasure, (hRCp k).1⟩  = φp k := by
      
      rfl
    rw [htarget] at ht
    simpa [criticalFKParameters] using ht
  have hpin (k : Fin q) :
      1 /  q  < (μ k.succ).toMeasure.real
        {σ |  σ (0, 0)  = (k.succ : ℕ)} := by
    
    
    exact wired_pinned_one_site_probability_gt q hq2 (pottsCriticalBeta q) hβ
      k.succ (by simp only [Fin.val_succ]; omega) (φp k) (hφpweak k)
      (μ k.succ) (hμp k) (ENNReal.toReal_pos (rc_discontinuity_of_positive_rate q hq φ₀ (φp k)
                                                  hRC₀ (hRCp k) L hL hrate).2.ne' (measure_ne_top _ _))
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact (hij rfl).elim
    | succ k =>
      intro heq
      
      have hfree' : (μ 0).toMeasure.real
          {σ |  σ (0, 0)  = (k.succ : ℕ)} = 1 /  q  := by
        simpa [boundaryColor, Subtype.ext_iff] using  free_one_site_probability q hq2 (pottsCriticalBeta q) hβ
                                                        φ₀ hφ₀weak (μ 0) hμ₀ (0, 0)
                                                        (boundaryColor q k.succ (by simp only [Fin.val_succ]; omega)) 
      
      have hpin' := hpin k
      rw [←  congrArg (fun ν  => ν.real
               {σ |  σ (0, 0)  = (k.succ : ℕ)}) heq ] at hpin'
      linarith 
  | succ k =>
    cases j using Fin.cases with
    | zero =>
      intro heq
      
      have hfree' : (μ 0).toMeasure.real
          {σ |  σ (0, 0)  = (k.succ : ℕ)} = 1 /  q  := by
        simpa [boundaryColor, Subtype.ext_iff] using  free_one_site_probability q hq2 (pottsCriticalBeta q) hβ
                                                        φ₀ hφ₀weak (μ 0) hμ₀ (0, 0)
                                                        (boundaryColor q k.succ (by simp only [Fin.val_succ]; omega)) 
      
      have hpin' := hpin k
      rw [←  congrArg (fun ν  => ν.real
               {σ |  σ (0, 0)  = (k.succ : ℕ)}) heq.symm ] at hpin'
      linarith 
    | succ l =>
      intro heq
      have hcolor : boundaryColor q l.succ
          (by simp only [Fin.val_succ]; omega) ≠ boundaryColor q k.succ
          (by simp only [Fin.val_succ]; omega) := by
        intro h
        apply hij
        exact Fin.ext (by
          simp_all [boundaryColor])
      
      have hoff' : (μ l.succ).toMeasure.real
          {σ |  σ (0, 0)  = (k.succ : ℕ)} ≤ 1 /  q  := by
        simpa [boundaryColor, Subtype.ext_iff] using  wired_off_color_probability_le_uniform q hq2
                                                        (pottsCriticalBeta q) hβ l.succ (by simp only [Fin.val_succ]; omega)
                                                        (φp l) (hφpweak l) (μ l.succ) (hμp l) (0, 0)
                                                        (boundaryColor q k.succ (by simp only [Fin.val_succ]; omega)) hcolor.symm 
      
      have hpin' := hpin k
      rw [ congrArg (fun ν  => ν.real
             {σ | (σ (0, 0) ) = (k.succ : ℕ)}) heq ] at hpin'
      linarith 

end PottsDiscontinuity.PottsThm
