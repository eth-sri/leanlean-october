module
public import Mathlib

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Infra.Lambda
public import PottsDiscontinuity.PottsThm.ColoringPushforward
public import PottsDiscontinuity.PottsThm.CriticalLimits
public import PottsDiscontinuity.PottsThm.Distinctness
public import PottsDiscontinuity.PottsThm.MixtureSeparation
public import PottsDiscontinuity.PottsThm.PottsColoringErgodicity
public import PottsDiscontinuity.PottsThm.RateTransfer

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace PottsDiscontinuity.PottsThm


open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts

open PottsDiscontinuity.RCInfinite

private theorem probabilityMeasure_eq_of_spinCylinder_real (q : ℕ) (hq : 2 ≤ q)
    (μ ν : ProbabilityMeasure (SpinSpace q))
    (h : ∀ A ξ, μ.toMeasure.real (spinCylinder q A ξ) =
      ν.toMeasure.real (spinCylinder q A ξ)) : μ = ν := by
  apply spinCylinderCoordinates_injective q hq
  funext i
  apply NNReal.coe_injective
  simpa only [spinCylinderCoordinates,
    ProbabilityMeasure.measureReal_eq_coe_coeFn] using h i.1 i.2

/-- Theorem 1.1 follows from the stated random-cluster rate input at every
positive solution of `cosh λ = √q / 2`. -/
theorem potts_theorem_1_1_of_rc_rate (q : ℕ) (hq : 4 < q)
    (hRCrate : ∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
      ∀ φ₀ : Measure LatticeConfiguration,
        IsRCInfiniteVolumeLimit
          (rcCriticalParameter ⟨(q : ℝ), by
            simp_all <;> omega ⟩)
          ⟨(q : ℝ), by
            simp_all <;> omega ⟩ 0 φ₀ →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
            (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
            (φ₀.real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
            atTop (𝓝 (lam + 2 * S)) ∧ 0 < lam + 2 * S) :
    ∃ μ : Fin (q + 1) → Measure (ℤ × ℤ → Set.Icc 1 q),
      (∀ i, IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) i (μ i)) ∧
      ((∀ i j, i ≠ j → μ i ≠ μ j) ∧ (∀ i, IsTranslationErgodic (μ i)) ∧
        μ 0 ≠ (q : ℝ≥0∞)⁻¹ • ∑ i : Fin q, μ i.succ) ∧
      (∀ i : Fin q, (1 : ℝ) / q < (μ i.succ).real
        {σ |  (σ (0, 0) : ℕ)  = (i.succ : ℕ)}) ∧
       ∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
            (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
              Real.log ((μ 0).real {σ | σ (0, 0) = σ (diagonalSite n)} - 1 / q))
            atTop (𝓝 (lam + 2 * S)) ∧
          0 < lam + 2 * S  := by
  
  have hq2 : 2 ≤ q := by omega
  have hqReal : (4 : ℝ) < q := by exact_mod_cast hq
  have hβ  := pottsCriticalBeta_pos q hq
  
  
  have : Nonempty (Set.Icc 1 q) := ⟨⟨1, le_rfl, by omega⟩⟩
  have hcriticalParams :
      (criticalFKParameters q hq).toP = rcCriticalParameter  ⟨q, by
                                                               grind⟩  ∧
        (criticalFKParameters q hq).toQ =  ⟨q, by
                                             grind⟩  := by
    have hbridge := fkCritical_toP_toQ q hq
    constructor
    · rw [hbridge.1]
      rfl
    · 
      
      rfl
  obtain ⟨μP, φ₀, φp, hRC₀, hμ₀, hES₀, hrest⟩ :=
    exists_critical_coloured_limits q hq
  have hRCp  :=
    fun k => (hrest k).1
  have hμp  := fun k => (hrest k).2.1
  have hESp  :=
    fun k => (hrest k).2.2
  
  let lam₀  := Real.arcosh (Real.sqrt q / 2)
  
  
  obtain ⟨S₀, hseries₀, hrate₀, hpositive₀⟩ :=
    hRCrate lam₀  (arcosh_pos_of_gt4  ↑q  hqReal).left   (arcosh_pos_of_gt4  ↑q  hqReal).right  φ₀.toMeasure (by
                                              grind)
  
  have hdisc (k : Fin q) := rc_discontinuity_of_positive_rate q hq φ₀ (φp k)
    hRC₀ (hRCp k) (lam₀ + 2 * S₀) hpositive₀ hrate₀
  have hno  :=
    free_no_infinite_clusters (criticalFKParameters q hq) φ₀.toMeasure hRC₀ (hdisc  ⟨0, by omega⟩ ).1
  
  have hφpweak (k : Fin q) : Tendsto
      (fun n => wiredBoxProbabilityMeasure
        (fkParameters q hq2 (pottsCriticalBeta q) hβ) (0, 0) n)
      atTop (𝓝 (φp k)) := by
    have ht := boxMeasure_tendsto (criticalFKParameters q hq) 1
      (φp k).toMeasure (hRCp k)
    have htarget :
         ⟨(φp k).toMeasure, (hRCp k).1⟩  = φp k := by
      
      rfl
    rw [htarget] at ht
    simpa [criticalFKParameters] using ht
  let μ  := fun i => (μP i).toMeasure
  
  
  
  have herg₀ : IsTranslationErgodic (μ 0) := by
    have hsampler := freeColoringMap_isFreeESC q hq φ₀ hno
    let samplerMeasure  :=
      (φ₀.toMeasure.prod (iidFieldMeasure
        (ProbabilityTheory.uniformOn  Set.univ ))).map
          (clusterColoring (⟨1, le_rfl, by omega⟩ : Set.Icc 1 q))
    have : IsProbabilityMeasure samplerMeasure := hsampler.1
    let samplerPM : ProbabilityMeasure (SpinSpace q) := ⟨samplerMeasure, inferInstance⟩
    
    have hPM := probabilityMeasure_eq_of_spinCylinder_real q hq2 samplerPM (μP 0)  fun A ξ => by
                                                                                     simpa [samplerPM] using
                                                                                       (hsampler.2 A ξ).trans (hES₀.2 A ξ).symm 
    
    have hmeasure : samplerPM.toMeasure = μ 0 := congrArg ProbabilityMeasure.toMeasure hPM
    rw [← hmeasure]
    simpa [samplerPM] using  clusterColoring_map_ergodic_of_RCmixing
                                               (criticalFKParameters q hq) 0 φ₀.toMeasure hRC₀
                                               (⟨1, le_rfl, by omega⟩ : Set.Icc 1 q) 
  have hergp (k : Fin q) : IsTranslationErgodic (μ k.succ) := by
    
    have hsampler := wiredColoringMap_isWiredESC q hq (φp k) k.succ (by simp)
    let c₀  := boundaryColor q k.succ (by simp)
    let samplerMeasure  :=
      (φp k).toMeasure.prod (iidFieldMeasure
        (ProbabilityTheory.uniformOn  Set.univ )) |>.map
          (clusterColoring c₀)
    have : IsProbabilityMeasure samplerMeasure := hsampler.1
    let samplerPM : ProbabilityMeasure (SpinSpace q) := ⟨samplerMeasure, inferInstance⟩
    
    have hPM := probabilityMeasure_eq_of_spinCylinder_real q hq2 samplerPM
      (μP k.succ)  fun A ξ => by
                     simpa [samplerPM] using
                       (hsampler.2 A ξ).trans ((hESp k).2 A ξ).symm 
    
    have hmeasure : samplerPM.toMeasure = μ k.succ := congrArg ProbabilityMeasure.toMeasure hPM
    rw [← hmeasure]
    simpa [samplerPM] using  clusterColoring_map_ergodic_of_RCmixing
                                                   (criticalFKParameters q hq) 1 (φp k).toMeasure (hRCp k) c₀ 
  
  
  refine ⟨μ,  fun i => by
                cases i using Fin.cases with
                | zero => simpa  using hμ₀
                | succ k => simpa  using hμp k , ?_⟩
  refine ⟨⟨ critical_potts_limits_pairwise_distinct q hq μP φ₀ φp
              hRC₀ hμ₀ hRCp hμp (lam₀ + 2 * S₀) hpositive₀ hrate₀ ,  fun i => by
                         cases i using Fin.cases with
                         | zero => exact herg₀
                         | succ k => exact hergp k ,  critical_potts_free_measure_ne_wired_average q hq μP φ₀ φp
                                   hRC₀ hμ₀ hRCp hμp (lam₀ + 2 * S₀) hpositive₀ hrate₀ ⟩, ?_⟩
  refine ⟨ fun k => by
             
             
             simpa [μ] using wired_pinned_one_site_probability_gt q hq2
               (pottsCriticalBeta q) hβ k.succ (by simp) (φp k) (hφpweak k)
               (μP k.succ) (hμp k) (ENNReal.toReal_pos (hdisc k).2.ne' (measure_ne_top _ _)) , ?_⟩
  intro lam hlam hcosh
  obtain ⟨S, hseries, hrate, hpositive⟩ :=
    hRCrate lam hlam hcosh φ₀.toMeasure (by
                                           grind)
  have hspinRate := free_spin_rate_of_rc_rate q hq2 (pottsCriticalBeta q) hβ
    φ₀ (by
          have ht := boxMeasure_tendsto (criticalFKParameters q hq) 0 φ₀.toMeasure hRC₀
          have htarget :
               ⟨φ₀.toMeasure, hRC₀.1⟩  = φ₀ := by
            
            rfl
          rw [htarget] at ht
          simpa [criticalFKParameters] using ht) hRC₀ (μP 0) hμ₀ (lam + 2 * S) hrate
  exact ⟨S, hseries, by simpa [μ] using hspinRate, hpositive⟩

end PottsDiscontinuity.PottsThm
