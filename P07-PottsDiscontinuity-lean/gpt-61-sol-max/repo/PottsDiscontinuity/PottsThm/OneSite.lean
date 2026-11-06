module
public import Mathlib

public import PottsDiscontinuity.Potts.FreeSpinObservations
public import PottsDiscontinuity.Potts.WiredSpinFormula

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.PottsThm


open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open Classical



private lemma optionUnit_setoid_bot (R : Setoid (Option PUnit))
    (h : ¬ R (some PUnit.unit) none) : R = ⊥ := by
  apply bot_unique
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>  exact (h (R.symm hab)).elim
  | some a =>
    
    cases b with
    | none => exact (h hab).elim
    | some b =>  rfl

private lemma card_optionUnit_quotient_bot :
    Nat.card (Quotient (⊥ : Setoid (Option PUnit))) = 2 := by
  calc
    Nat.card (Quotient  ⊥ ) = Nat.card (Option PUnit) :=
      Nat.card_congr  Setoid.quotientBotEquiv 
    _ = 2 := by norm_num

section

variable (q : ℕ)
include q

private lemma wired_one_point_kernel_off_pin 
    (R : Setoid (Option PUnit)) (pin color : Set.Icc 1 q) (hcolor : color ≠ pin) :
    pinnedClusterCylinderProbability R some (fun _ : PUnit => color) none pin =
      if R (some PUnit.unit) none then 0 else (q : ℝ)⁻¹ := by
  
  have hid : markedMap some none = (id : Option PUnit → Option PUnit) := by
    funext a
    cases a <;> rfl
  have hcount : observedClassCount R (markedMap some none) = Nat.card (Quotient R) := by
    rw [hid]
    rfl
  by_cases h : R (some PUnit.unit) none
  · 
    
    unfold pinnedClusterCylinderProbability
    rw [ite_eq_right (by
                        intro hle
                        have hrel : R.comap (markedMap some none) (some PUnit.unit) none := h
                        
                        exact hcolor (hle hrel)), ite_eq_left h]
  · have hbot  := optionUnit_setoid_bot R h
    
    have hcount' : observedClassCount R (markedMap some none) = 2 := by
      rw [hcount, hbot, card_optionUnit_quotient_bot]
    rw [pinnedClusterCylinderProbability, ite_eq_left (by
                                                         simp_all), hcount', card_pottsColors]
    rw [ite_eq_right h]
    norm_num

section

variable (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
include hq hβ

/-- At a wired Potts limit, a non-pinned colour at one site has probability at
most `1/q`. -/
theorem wired_off_color_probability_le_uniform   (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto  (wiredBoxProbabilityMeasure (fkParameters q hq β hβ) (0, 0)) 
      atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q))
    (hμ : IsPottsInfiniteVolumeLimit q β i μ.toMeasure)
    (x : ℤ × ℤ) (color : Set.Icc 1 q)
    (hcolor : color ≠ boundaryColor q i hi) :
    μ.toMeasure.real {σ | σ x = color} ≤ 1 / (q : ℝ) := by
  let v : Unit → ℤ × ℤ := fun _ => x
  let ξ : Unit → Set.Icc 1 q := fun _ => color
  have hevent : {σ : SpinSpace q | σ x = color} =
      spinObservationEvent (A := PUnit) q v ξ := by
    
    simp [spinObservationEvent, v, ξ]
  rw [hevent, wired_spin_observation_formula q hq β hβ i hi φ hφ μ hμ v ξ]
  let r  :=
    infiniteWiredPartition (Option.map v)
  
  
  rw [funext  fun (R : Setoid (Option Unit)) => wired_one_point_kernel_off_pin q R (boundaryColor q i hi) color hcolor ]
  
  
  
  have hprob : φ.toMeasure.real {ω | ¬ r ω (some PUnit.unit) none} ≤ 1 := by
    simp_all
  calc
    partitionExpectation φ.toMeasure r
        (fun R => if R (some PUnit.unit) none then 0 else q⁻¹) =
         1 /  q   * φ.toMeasure.real {ω | ¬ r ω (some PUnit.unit) none} := by
      
      simpa using  partitionExpectation_affine_indicator φ.toMeasure r
                     (infiniteWiredPartition_measurableSet (Option.map v))
                     (fun R => ¬ R (some PUnit.unit) none) 0 (1 /  q ) 
    _ ≤ 1 /  q  := by
      bound

/-- A free Edwards--Sokal limit has a uniform one site marginal. -/
theorem free_one_site_probability  
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto  (boxProbabilityMeasure (fkParameters q hq β hβ) (0, 0)) 
      atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q))
    (hμ : IsPottsInfiniteVolumeLimit q β 0 μ.toMeasure)
    (x : ℤ × ℤ) (color : Set.Icc 1 q) :
    μ.toMeasure.real {σ | σ x = color} = 1 / (q : ℝ) := by
  let v : Unit → ℤ × ℤ := fun _ => x
  let ξ : Unit → Set.Icc 1 q := fun _ => color
  
  rw [(by
         
         simp [spinObservationEvent, v, ξ] : {σ : SpinSpace q | σ x = color} =
      spinObservationEvent (A := Unit) q v ξ), free_spin_observation_formula (A := Unit) q hq β hβ φ hφ μ hμ v ξ]
  let r  := infiniteFreePartition v
  
  have hexpect : partitionExpectation φ.toMeasure r
      (fun R => clusterCylinderProbability (A := Unit) (V := Unit) R id ξ) =
        1 /  q  := by
    rw [show (fun R  =>
      clusterCylinderProbability (A := Unit) (V := Unit) R id ξ) =
      fun _ => 1 / (q : ℝ) from funext  fun R => by
                                          have hcomp : R.comap id ≤ Setoid.ker ξ := by
                                            intro a b _
                                            simp
                                          have hcount : observedClassCount (A := Unit) (V := Unit) R id = 1 := by
                                            rw [observedClassCount_eq_range]
                                            all_goals simp_all
                                          rw [clusterCylinderProbability, ite_eq_left hcomp, hcount]
                                          
                                          simp  ]
    unfold partitionExpectation
    rw [← Finset.sum_mul]
    rw [sum_partition_mass φ.toMeasure r
      (infiniteFreePartition_measurableSet v), one_mul]
  omega

/-- Positive wired percolation makes the pinned one site colour strictly more
likely than a uniform colour. -/
theorem wired_pinned_one_site_probability_gt   (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto (fun n => wiredBoxProbabilityMeasure (fkParameters q hq β hβ)
      (0, 0) n) atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q))
    (hμ : IsPottsInfiniteVolumeLimit q β i μ.toMeasure)
    (hpos : 0 < φ.toMeasure.real
      {ω | clusterIsInfinite (rcInfiniteOpenGraph ω) (0, 0)}) :
    1 / (q : ℝ) < μ.toMeasure.real
      {σ | (σ (0, 0) : ℕ) = (i : ℕ)} := by
  rw [wired_origin_spin_probability q hq β hβ i hi φ hφ μ hμ]
   
  have hc : 0 < 1 - 1 / (q : ℝ) := by
    rw [sub_pos]
    exact (div_lt_one (by exact_mod_cast  by omega)).2 (by exact_mod_cast  by omega )
  nlinarith 

end

end

end PottsDiscontinuity.PottsThm
