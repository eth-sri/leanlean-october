module

public import PottsDiscontinuity.Potts.FreeSpinObservations
public import PottsDiscontinuity.Potts.WiredSpinFormula

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open Classical

private lemma optionUnit_setoid_bot (R : Setoid (Option PUnit))
    (h : ¬ R (some PUnit.unit) none) : R = ⊥ :=
  bot_unique fun a b hab => by
    rcases a with _ | ⟨⟩ <;> rcases b with _ | ⟨⟩
    · rfl
    · exact (h (R.symm hab)).elim
    · exact (h hab).elim
    · rfl

private lemma wired_one_point_kernel_off_pin (q : ℕ)
    (R : Setoid (Option PUnit)) (pin color : Set.Icc 1 q) (hcolor : color ≠ pin) :
    pinnedClusterCylinderProbability R some (fun _ : PUnit => color) none pin =
      if R (some PUnit.unit) none then 0 else (q : ℝ)⁻¹ := by
  classical
  have hid : markedMap some none = (id : Option PUnit → Option PUnit) := by
    funext a; cases a <;> rfl
  unfold pinnedClusterCylinderProbability
  rw [hid, Setoid.comap_id, show observedClassCount R id = Nat.card (Quotient R) from rfl]
  by_cases h : R (some PUnit.unit) none
  · have hcompat : ¬ R ≤ Setoid.ker (markedMap (fun _ : PUnit => color) pin) :=
      fun hle => hcolor (hle h)
    rw [ite_eq_right hcompat, ite_eq_left h]
  · have hbot : R = ⊥ := optionUnit_setoid_bot R h
    rw [ite_eq_left (hbot ▸ bot_le), ite_eq_right h, hbot, card_pottsColors,
      Nat.card_congr (Setoid.quotientBotEquiv : Quotient (⊥ : Setoid (Option PUnit)) ≃ Option PUnit)]
    norm_num

theorem wired_off_color_probability_le_uniform (q : ℕ) (hq : 2 ≤ q)
    (β : ℝ) (hβ : 0 < β) (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
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
  have hevent : {σ : SpinSpace q | σ x = color} = spinObservationEvent (A := PUnit) q v ξ := by
    ext σ; simp [spinObservationEvent, v, ξ]
  rw [hevent, wired_spin_observation_formula q hq β hβ i hi φ hφ μ hμ v ξ]
  let r : LatticeConfiguration → Setoid (Option Unit) := infiniteWiredPartition (Option.map v)
  have hpart := partitionExpectation_affine_indicator φ.toMeasure r
    (infiniteWiredPartition_measurableSet (Option.map v))
    (fun R => ¬ R (some PUnit.unit) none) 0 (1 / (q : ℝ))
  have hrew : partitionExpectation φ.toMeasure r
      (fun R => pinnedClusterCylinderProbability R some ξ none (boundaryColor q i hi)) =
      (1 / (q : ℝ)) * φ.toMeasure.real {ω | ¬ r ω (some PUnit.unit) none} := by
    rw [show (fun R : Setoid (Option Unit) =>
        pinnedClusterCylinderProbability R some ξ none (boundaryColor q i hi)) =
        fun R => 0 + (1 / (q : ℝ)) * (if ¬ R (some PUnit.unit) none then 1 else 0) by
      funext R
      rw [wired_one_point_kernel_off_pin q R (boundaryColor q i hi) color hcolor]
      by_cases hR : R (some PUnit.unit) none <;> simp [hR]]
    simpa using hpart
  exact hrew.le.trans (mul_le_of_le_one_right (by positivity) measureReal_le_one)

theorem free_one_site_probability (q : ℕ) (hq : 2 ≤ q)
    (β : ℝ) (hβ : 0 < β)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto (fun n => boxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n)
      atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q))
    (hμ : IsPottsInfiniteVolumeLimit q β 0 μ.toMeasure)
    (x : ℤ × ℤ) (color : Set.Icc 1 q) :
    μ.toMeasure.real {σ | σ x = color} = 1 / (q : ℝ) := by
  let v : Unit → ℤ × ℤ := fun _ => x
  let ξ : Unit → Set.Icc 1 q := fun _ => color
  rw [show {σ : SpinSpace q | σ x = color} = spinObservationEvent (A := Unit) q v ξ by
    ext σ; simp [spinObservationEvent, v, ξ],
    free_spin_observation_formula (A := Unit) q hq β hβ φ hφ μ hμ v ξ]
  let r : LatticeConfiguration → Setoid Unit := infiniteFreePartition v
  have hkernel (R : Setoid Unit) :
      clusterCylinderProbability (A := Unit) (V := Unit) R id ξ = 1 / (q : ℝ) := by
    have hcomp : R.comap id ≤ Setoid.ker ξ := fun _ _ _ => rfl
    have hcount : observedClassCount (A := Unit) (V := Unit) R id = 1 :=
      Nat.card_unique
    rw [clusterCylinderProbability, ite_eq_left hcomp, hcount, card_pottsColors, pow_one, one_div]
  change partitionExpectation φ.toMeasure r
    (fun R => clusterCylinderProbability (A := Unit) (V := Unit) R id ξ) = _
  rw [show (fun R : Setoid Unit =>
      clusterCylinderProbability (A := Unit) (V := Unit) R id ξ) =
      fun _ => 1 / (q : ℝ) from funext hkernel]
  unfold partitionExpectation
  rw [← Finset.sum_mul, sum_partition_mass φ.toMeasure r (infiniteFreePartition_measurableSet v),
    one_mul]

theorem wired_pinned_one_site_probability_gt (q : ℕ) (hq : 2 ≤ q)
    (β : ℝ) (hβ : 0 < β) (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
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
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hc : 0 < 1 - 1 / (q : ℝ) :=
    sub_pos.mpr ((div_lt_one hqpos).2 (by exact_mod_cast (show 1 < q by omega)))
  linarith [mul_pos hc hpos]

end PottsDiscontinuity.PottsThm
