module
public import Mathlib

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.PottsThm.DiscontinuityConsequences
public import PottsDiscontinuity.PottsThm.FreeCorrelationLimit
public import PottsDiscontinuity.PottsThm.WiredCorrelation
public import PottsDiscontinuity.PottsThm.WiredInfiniteAssociation

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PottsDiscontinuity.PottsThm


open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.RCInfinite

section

variable (q : ℕ) (hq : 4 < q)
include hq

private theorem criticalFreeBoxLimit 
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 0 φ.toMeasure) :
    Tendsto (fun n => boxProbabilityMeasure
      (fkParameters q (by omega) (pottsCriticalBeta q) (pottsCriticalBeta_pos q hq))
      (0, 0) n) atTop (𝓝 φ) := by
  have ht := boxMeasure_tendsto (criticalFKParameters q hq) 0 φ.toMeasure hφ
  aesop

section

variable (φ : ProbabilityMeasure LatticeConfiguration) (hφ : IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 1 φ.toMeasure)
include hφ

private theorem criticalWiredBoxLimit 
     :
    Tendsto (fun n => wiredBoxProbabilityMeasure
      (fkParameters q (by omega) (pottsCriticalBeta q) (pottsCriticalBeta_pos q hq))
      (0, 0) n) atTop (𝓝 φ) := by
  have ht := boxMeasure_tendsto (criticalFKParameters q hq) 1 φ.toMeasure hφ
  aesop

private theorem criticalInfiniteAt_translate 
    
    (x : LatticeVertex) :
    φ.toMeasure.real (infiniteAt x) = φ.toMeasure.real (infiniteAt (0, 0)) := by
  have htrans := limit_translate_real (criticalFKParameters q hq) 1 φ.toMeasure hφ
    x (measurableSet_infiniteAt x)
  have hpre :  edgeTranslate x  ⁻¹' infiniteAt x = infiniteAt (0, 0) := by
    simpa [latticeTranslate] using infiniteAt_preimage x (0, 0)
  rw [hpre] at htrans
  exact htrans.symm

end

/-- At criticality, the wired average has a uniform two point excess over the
free limit. The gap comes from any one pinned component with positive
percolation probability and wired FKG. -/
theorem critical_potts_free_measure_ne_wired_average 
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
    (μ 0).toMeasure ≠ (q : ℝ≥0∞)⁻¹ • ∑ i : Fin q, (μ i.succ).toMeasure := by
  
  let j0 : Fin q := ⟨0, by omega⟩
  have hqR :  1  < (q : ℝ) := by exact_mod_cast  show 1 < q by omega 
  have hqRpos :  0  < (q : ℝ) := by linarith
  have hβ  := pottsCriticalBeta_pos q hq
  
  have hφpweak (i : Fin q) := criticalWiredBoxLimit q hq (φp i) (hRCp i)
  have hdisc := rc_discontinuity_of_positive_rate q hq φ₀ (φp j0)
    hRC₀ (hRCp j0) L hL hrate
  have hθ : 0 < (φp j0).toMeasure.real (infiniteAt (0, 0)) := by
                                                                exact ENNReal.toReal_pos (LT.lt.ne' hdisc.right) (measure_ne_top  ↑(φp j0)  (infiniteAt (0, 0)))
  let c : ℝ := 1 - 1 /  q 
  have hc : 0 < c := by
    bound
  have hjoint (n : ℕ) :
      (φp j0).toMeasure.real (infiniteAt (0, 0) ∩ infiniteAt (diagonalSite n)) ≥
        (φp j0).toMeasure.real (infiniteAt (0, 0)) ^ 2 := by
    have hfkg := wired_infinite_at_positive_association
      (criticalFKParameters q hq) (φp j0) (hφpweak j0) (0, 0) (diagonalSite n)
    rw [criticalInfiniteAt_translate q hq (φp j0) (hRCp j0) (diagonalSite n)] at hfkg
    nlinarith 
  have hcorrPos (n : ℕ) :
      1 /  q  + c * (φp j0).toMeasure.real
        (infiniteAt (0, 0) ∩ infiniteAt (diagonalSite n)) ≤
      (μ j0.succ).toMeasure.real
        {σ | σ (0, 0) = σ (diagonalSite n)} := by
    have hi : 1 ≤ (j0.succ : ℕ) := by simp 
    have h := wired_spin_correlation_lower_bound q (by omega) (pottsCriticalBeta q) hβ
      j0.succ hi (φp j0) (hφpweak j0) (μ j0.succ) (hμp j0) (0, 0) (diagonalSite n)
    simpa [c] using h
  have hcorrStrict (n : ℕ) :
      1 /  q  + c *  (φp j0).toMeasure.real (infiniteAt (0, 0)) ^ 2  ≤
      (μ j0.succ).toMeasure.real
        {σ | σ (0, 0) = σ (diagonalSite n)} := by
    have hmul := mul_le_mul_of_nonneg_left (hjoint n) (le_of_lt hc)
    have := hcorrPos n
    linarith
  have hcorrBase (i : Fin q) (n : ℕ) :
      1 /  q  ≤ (μ i.succ).toMeasure.real
        {σ | σ (0, 0) = σ (diagonalSite n)} := by
    have hi : 1 ≤ (i.succ : ℕ) := by simp
    have h := wired_spin_correlation_lower_bound q (by omega) (pottsCriticalBeta q) hβ
      i.succ hi (φp i) (hφpweak i) (μ i.succ) (hμp i) (0, 0) (diagonalSite n)
    have hnonneg := measureReal_nonneg (μ := (φp i).toMeasure)
      (s := infiniteAt (0, 0) ∩ infiniteAt (diagonalSite n))
    have hc_nonneg  := le_of_lt hc
    have hmul := mul_nonneg hc_nonneg hnonneg
    linarith
  have hsumGap (n : ℕ) :
       q  * (1 /  q ) + c *
           (φp j0).toMeasure.real (infiniteAt (0, 0)) ^ 2  ≤
        ∑ i : Fin q, (μ i.succ).toMeasure.real
          {σ | σ (0, 0) = σ (diagonalSite n)} := by
    let d : Fin q → ℝ := fun i => (μ i.succ).toMeasure.real
        {σ | σ (0, 0) = σ (diagonalSite n)} - 1 /  q 
    have hd (i : Fin q) : 0 ≤ d i := sub_nonneg.mpr (hcorrBase i n)
    have hd0 : c *  (φp j0).toMeasure.real (infiniteAt (0, 0)) ^ 2  ≤ d j0 := by
      
      linarith [hcorrStrict n]
    have hdsum  :=
      hd0.trans (Finset.single_le_sum (fun i _ => hd i) (Finset.mem_univ j0))
    have hdecomp :
         ∑ i : Fin q, (μ i.succ).toMeasure.real
          {σ | σ (0, 0) = σ (diagonalSite n)}  =
          ∑ i : Fin q, (1 /  q  + d i) := by
      aesop
    rw [hdecomp, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
    nlinarith
  
  
  intro heq
  have hcorEq (n : ℕ) :
      (μ 0).toMeasure.real {σ | σ (0, 0) = σ (diagonalSite n)} =
         1 /  q   * ∑ i : Fin q, (μ i.succ).toMeasure.real
          {σ | σ (0, 0) = σ (diagonalSite n)} := by
    have h := congrArg (fun ν  => ν.real
      {σ | σ (0, 0) = σ (diagonalSite n)}) heq
    rw [measureReal_ennreal_smul_apply] at h
    have hsumreal : (∑ i : Fin q, (μ i.succ).toMeasure).real
        {σ | σ (0, 0) = σ (diagonalSite n)} =
          ∑ i : Fin q, (μ i.succ).toMeasure.real
            {σ | σ (0, 0) = σ (diagonalSite n)} := by
      simp [Measure.real_def, ENNReal.toReal_sum]
    rw [hsumreal] at h
    simpa using h
  have hlow (n : ℕ) :
      1 /  q  +  c *  (φp j0).toMeasure.real (infiniteAt (0, 0)) ^ 2   / q ≤
         1 /  q   * ∑ i : Fin q, (μ i.succ).toMeasure.real
          {σ | σ (0, 0) = σ (diagonalSite n)} := by
    have h := hsumGap n
    have hmul := mul_le_mul_of_nonneg_left h (le_of_lt (one_div_pos.mpr hqRpos))
    calc
      _ =  1 /  q   *
          ( q  * (1 /  q ) + c *
             (φp j0).toMeasure.real (infiniteAt (0, 0)) ^ 2 ) := by
        field_simp 
      _ ≤ _ := hmul
  have hbound (n : ℕ) :
      1 /  q  +  c *  (φp j0).toMeasure.real (infiniteAt (0, 0)) ^ 2   / q ≤
        (μ 0).toMeasure.real {σ | σ (0, 0) = σ (diagonalSite n)} := by
    rw [hcorEq n]
    exact hlow n
  have hδ  :=
    div_pos (mul_pos hc (sq_pos_of_pos hθ)) hqRpos
  
  have : 1 /  q  +  c *  (φp j0).toMeasure.real (infiniteAt (0, 0)) ^ 2   / q ≤
      1 /  q  := by
    simpa using  le_of_tendsto_of_tendsto'
                   (tendsto_const_nhds )
                   (free_spin_correlation_tendsto_uniform q hq φ₀ hRC₀ (μ 0) hμ₀
                      (criticalFreeBoxLimit q hq φ₀ hRC₀) L hL hrate)  hbound  
  linarith

end

end PottsDiscontinuity.PottsThm
