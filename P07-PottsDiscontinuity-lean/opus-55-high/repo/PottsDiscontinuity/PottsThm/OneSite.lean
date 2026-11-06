module

public import PottsDiscontinuity.Potts.FreeSpinObservations
public import PottsDiscontinuity.Potts.WiredSpinFormula

public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open Classical

section
variable (R : Setoid (Option PUnit))

theorem optionUnit_setoid_bot (h : ¬ R (some PUnit.unit) none) : R = ⊥ := by
  apply bot_unique
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => tauto
  | some a =>
    cases b with
    | none => simp_all
    | some b => rfl
end

theorem card_optionUnit_quotient_bot :
    Nat.card (Quotient (⊥ : Setoid (Option PUnit))) = 2 := by
  calc
    Nat.card (Quotient (⊥ : Setoid (Option PUnit))) = Nat.card (Option PUnit) :=
      Nat.card_congr (Setoid.quotientBotEquiv : Quotient (⊥ : Setoid (Option PUnit)) ≃ Option PUnit)
    _ = 2 := by norm_num

theorem wired_one_point_kernel_off_pin (q : ℕ)
    (R : Setoid (Option PUnit)) (pin color : Set.Icc 1 q) (hcolor : color ≠ pin) :
    pinnedClusterCylinderProbability R some (fun _ : PUnit => color) none pin =
      if R (some PUnit.unit) none then 0 else (q : ℝ)⁻¹ := by
  have hid : markedMap some none = (id : Option PUnit → Option PUnit) := by
    funext a
    cases a <;> rfl
  have hcount : observedClassCount R (markedMap some none) = Nat.card (Quotient R) := by
    tauto
  by_cases h : R (some PUnit.unit) none
  · have hcompat : ¬ R.comap (markedMap some none) ≤
        Setoid.ker (markedMap (fun _ : PUnit => color) pin) := by
      intro hle
      have hrel : R.comap (markedMap some none) (some PUnit.unit) none := by
        tauto
      have heq := hle hrel
      tauto
    simp_all [pinnedClusterCylinderProbability]
  · have hbot := optionUnit_setoid_bot R h
    have hcompat : R.comap (markedMap some none) ≤
        Setoid.ker (markedMap (fun _ : PUnit => color) pin) := by
      simp_all
    have hcount' : observedClassCount R (markedMap some none) = 2 := by
      grind [card_optionUnit_quotient_bot]
    rw [pinnedClusterCylinderProbability, ite_eq_left hcompat, hcount', card_pottsColors]
    simp_all

section
variable (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
/-- At a wired Potts limit, a non-pinned colour at one site has probability at
most `1/q`. -/
theorem wired_off_color_probability_le_uniform (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto (fun n => wiredBoxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n)
      atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q))
    (hμ : IsPottsInfiniteVolumeLimit q β i μ.toMeasure)
    (x : ℤ × ℤ) (color : Set.Icc 1 q)
    (hcolor : color ≠ boundaryColor q i hi) :
    μ.toMeasure.real {σ | σ x = color} ≤ 1 / (q : ℝ) := by
  let v : Unit → ℤ × ℤ := fun _ => x
  let ξ : Unit → Set.Icc 1 q := fun _ => color
  have hevent : {σ : SpinSpace q | σ x = color} =
      spinObservationEvent q v ξ := by
    ext σ
    tauto
  rw [hevent, wired_spin_observation_formula q hq β hβ i hi φ hφ μ hμ v ξ]
  let r :=
    infiniteWiredPartition (Option.map v)
  have hkernel (R : Setoid (Option Unit)) :
      pinnedClusterCylinderProbability R some ξ none (boundaryColor q i hi) =
        if R (some PUnit.unit) none then 0 else (q : ℝ)⁻¹ :=
    wired_one_point_kernel_off_pin q R (boundaryColor q i hi) color hcolor
  rw [show (fun R : Setoid (Option Unit) =>
      pinnedClusterCylinderProbability R some ξ none (boundaryColor q i hi)) =
      fun R => if R (some PUnit.unit) none then 0 else (q : ℝ)⁻¹ from funext hkernel]
  have hpart := partitionExpectation_affine_indicator φ.toMeasure r
    (infiniteWiredPartition_measurableSet (Option.map v))
    (fun R => ¬ R (some PUnit.unit) none) 0 (1 / (q : ℝ))
  have hprob : φ.toMeasure.real {ω | ¬ r ω (some PUnit.unit) none} ≤ 1 := by
    simp
  calc
    partitionExpectation φ.toMeasure r
        (fun R => if R (some PUnit.unit) none then 0 else (q : ℝ)⁻¹) =
        (1 / (q : ℝ)) * φ.toMeasure.real {ω | ¬ r ω (some PUnit.unit) none} := by
      simpa using hpart
    _ ≤ 1 / (q : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hprob (by positivity : 0 ≤ 1 / (q : ℝ))

/-- A free Edwards--Sokal limit has a uniform one site marginal. -/
theorem free_one_site_probability (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto (fun n => boxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n)
      atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q))
    (hμ : IsPottsInfiniteVolumeLimit q β 0 μ.toMeasure)
    (x : ℤ × ℤ) (color : Set.Icc 1 q) :
    μ.toMeasure.real {σ | σ x = color} = 1 / (q : ℝ) := by
  let v : Unit → ℤ × ℤ := fun _ => x
  let ξ : Unit → Set.Icc 1 q := fun _ => color
  have hevent : {σ : SpinSpace q | σ x = color} =
      spinObservationEvent q v ξ := by
    ext σ
    tauto
  rw [hevent, free_spin_observation_formula q hq β hβ φ hφ μ hμ v ξ]
  let r := infiniteFreePartition v
  have hkernel (R : Setoid Unit) :
      clusterCylinderProbability R id ξ = 1 / (q : ℝ) := by
    have hcomp : R.comap id ≤ Setoid.ker ξ := by
      tauto
    have hcount : observedClassCount R id = 1 := by
      rw [observedClassCount_eq_range]
      simp
    rw [clusterCylinderProbability, ite_eq_left hcomp, hcount, card_pottsColors]
    simp
  have hexpect : partitionExpectation φ.toMeasure r
      (fun R => clusterCylinderProbability R id ξ) =
        1 / (q : ℝ) := by
    rw [show (fun R : Setoid Unit =>
      clusterCylinderProbability R id ξ) =
      fun _ => 1 / (q : ℝ) from funext hkernel]
    unfold partitionExpectation
    rw [← Finset.sum_mul]
    rw [sum_partition_mass φ.toMeasure r
      (infiniteFreePartition_measurableSet v), one_mul]
  omega

/-- Positive wired percolation makes the pinned one site colour strictly more
likely than a uniform colour. -/
theorem wired_pinned_one_site_probability_gt (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
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
    exact (div_lt_one (by positivity)).2 (by aesop)
  simp_all
end

end PottsDiscontinuity.PottsThm
