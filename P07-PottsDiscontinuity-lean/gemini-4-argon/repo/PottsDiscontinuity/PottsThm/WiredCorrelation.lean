module

public import PottsDiscontinuity.Potts.InfinitePartitionMeasurability
public import PottsDiscontinuity.Potts.PartitionExpectationAlgebra
public import PottsDiscontinuity.Potts.SpinEventDecomposition
public import PottsDiscontinuity.Potts.WiredSpinObservations
public import PottsDiscontinuity.RCInfinite.ClusterEvents

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Topology
open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.RCInfinite
open Classical

noncomputable section

def pairClassLabel : Option Bool → Bool
  | none => false
  | some _ => true

def pinClassLabel (b₀ : Bool) : Option Bool → Bool
  | some b => b == b₀
  | none => false

private theorem natCard_quotient_ker_bool_of_surjective
    (f : Option Bool → Bool) (hf : Function.Surjective f) :
    Nat.card (Quotient (Setoid.ker f)) = 2 := by
  rw [Nat.card_congr (Setoid.quotientKerEquivRange f), Set.range_eq_univ.mpr hf]
  simp

private theorem pinnedObservedClassCount (R : Setoid (Option Bool)) :
    observedClassCount R (markedMap some none) = Nat.card (Quotient R) := by
  rw [show markedMap some none = (id : Option Bool → Option Bool) by funext a; cases a <;> rfl]
  rfl

private theorem markedMap_some_none_comap (R : Setoid (Option Bool)) :
    R.comap (markedMap some none) = R := by
  ext a b; cases a <;> cases b <;> rfl

private theorem ker_bool_surjective (f : Option Bool → Bool)
    (h0 : f none = false) (x : Option Bool) (hx : f x = true) :
    Function.Surjective f := fun b => by
  cases b
  · exact ⟨none, h0⟩
  · exact ⟨x, hx⟩

private theorem kernel_sum_of_always_compat {R : Setoid (Option Bool)} (q : ℕ)
    (pin : Set.Icc 1 q)
    (hcompat : ∀ c : Set.Icc 1 q, R ≤ Setoid.ker (markedMap (fun _ : Bool => c) pin)) :
    ∑ c : Set.Icc 1 q,
      pinnedClusterCylinderProbability R some (fun _ : Bool => c) none pin =
        (q : ℝ) * ((q : ℝ) ^ (Nat.card (Quotient R) - 1))⁻¹ := by
  have h1 (c : Set.Icc 1 q) :
      pinnedClusterCylinderProbability R some (fun _ : Bool => c) none pin =
        ((q : ℝ) ^ (Nat.card (Quotient R) - 1))⁻¹ := by
    unfold pinnedClusterCylinderProbability
    rw [markedMap_some_none_comap, ite_eq_left (hcompat c), pinnedObservedClassCount,
      card_pottsColors]
  simp_rw [h1]
  simp

private theorem kernel_sum_of_pin_iff {R : Setoid (Option Bool)} (q : ℕ)
    (pin : Set.Icc 1 q)
    (hcompat : ∀ c : Set.Icc 1 q, R ≤ Setoid.ker (markedMap (fun _ : Bool => c) pin) ↔ c = pin) :
    ∑ c : Set.Icc 1 q,
      pinnedClusterCylinderProbability R some (fun _ : Bool => c) none pin =
        ((q : ℝ) ^ (Nat.card (Quotient R) - 1))⁻¹ := by
  have h1 (c : Set.Icc 1 q) :
      pinnedClusterCylinderProbability R some (fun _ : Bool => c) none pin =
        if c = pin then ((q : ℝ) ^ (Nat.card (Quotient R) - 1))⁻¹ else 0 := by
    unfold pinnedClusterCylinderProbability
    simp only [markedMap_some_none_comap, hcompat c, pinnedObservedClassCount, card_pottsColors]
  simp_rw [h1]
  simp

private theorem wired_two_point_kernel_sum (q : ℕ) (hq : 2 ≤ q)
    (pin : Set.Icc 1 q) (R : Setoid (Option Bool)) :
    ∑ c : Set.Icc 1 q,
      pinnedClusterCylinderProbability R some (fun _ : Bool => c) none pin =
        1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
          (if R (some false) (some true) ∨
            (R (some false) none ∧ R (some true) none) then 1 else 0) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  by_cases hxy : R (some false) (some true)
  · by_cases hxg : R (some false) none
    · have hyg : R (some true) none := R.trans (R.symm hxy) hxg
      have htop : R = ⊤ := top_unique fun a b _ => by
        rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩
        · exact R.refl _
        · exact R.symm hxg
        · exact R.symm hyg
        · exact hxg
        · exact R.refl _
        · exact hxy
        · exact hyg
        · exact R.symm hxy
        · exact R.refl _
      have hcard : Nat.card (Quotient R) = 1 := by
        rw [htop]
        let : Subsingleton (Quotient (⊤ : Setoid (Option Bool))) := Quotient.subsingleton_iff.mpr rfl
        let : Nonempty (Quotient (⊤ : Setoid (Option Bool))) := ⟨Quotient.mk _ none⟩
        exact Nat.card_unique
      rw [kernel_sum_of_pin_iff q pin fun c => ⟨fun h => h hxg, fun hcp a b _ => by
        rcases a with _ | _ <;> rcases b with _ | _ <;> simp [markedMap, hcp]⟩, hcard]
      simp [hxy]
    · have hyg : ¬ R (some true) none := fun h => hxg (R.trans hxy h)
      have hgnx : ¬ R none (some false) := fun h => hxg (R.symm h)
      have hgny : ¬ R none (some true) := fun h => hyg (R.symm h)
      have hyx : R (some true) (some false) := R.symm hxy
      have hR : R = Setoid.ker pairClassLabel := Setoid.ext fun a b => by
        change R a b ↔ pairClassLabel a = pairClassLabel b
        rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;>
          simp [pairClassLabel, hxy, hyx, hxg, hyg, hgnx, hgny]
      have hcard : Nat.card (Quotient R) = 2 := by
        rw [hR]
        exact natCard_quotient_ker_bool_of_surjective _ (ker_bool_surjective _ rfl (some false) rfl)
      rw [kernel_sum_of_always_compat q pin fun c a b hab => by
        rw [hR] at hab
        rcases a with _ | _ <;> rcases b with _ | _ <;> simp_all [pairClassLabel, markedMap], hcard]
      simp [hxy, mul_inv_cancel₀ hq0]
  · by_cases hxg : R (some false) none
    · have hyg : ¬ R (some true) none := fun h => hxy (R.trans hxg (R.symm h))
      have hyx : ¬ R (some true) (some false) := fun h => hxy (R.symm h)
      have hgx : R none (some false) := R.symm hxg
      have hgy : ¬ R none (some true) := fun h => hyg (R.symm h)
      have hR : R = Setoid.ker (pinClassLabel true) := Setoid.ext fun a b => by
        change R a b ↔ pinClassLabel true a = pinClassLabel true b
        rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;>
          simp [pinClassLabel, hxy, hyx, hxg, hyg, hgx, hgy]
      have hcard : Nat.card (Quotient R) = 2 := by
        rw [hR]
        exact natCard_quotient_ker_bool_of_surjective _ (ker_bool_surjective _ rfl (some true) rfl)
      rw [kernel_sum_of_pin_iff q pin fun c => ⟨fun h => h hxg, fun hcp a b hab => by
        rw [hR] at hab
        rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;>
          simp_all [pinClassLabel, markedMap]⟩, hcard]
      simp [hxy, hxg, hyg, one_div]
    · by_cases hyg : R (some true) none
      · have hyx : ¬ R (some true) (some false) := fun h => hxy (R.symm h)
        have hgx : ¬ R none (some false) := fun h => hxg (R.symm h)
        have hgy : R none (some true) := R.symm hyg
        have hR : R = Setoid.ker (pinClassLabel false) := Setoid.ext fun a b => by
          change R a b ↔ pinClassLabel false a = pinClassLabel false b
          rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;>
            simp [pinClassLabel, hxy, hyx, hxg, hyg, hgx, hgy]
        have hcard : Nat.card (Quotient R) = 2 := by
          rw [hR]
          exact natCard_quotient_ker_bool_of_surjective _ (ker_bool_surjective _ rfl (some false) rfl)
        rw [kernel_sum_of_pin_iff q pin fun c => ⟨fun h => h hyg, fun hcp a b hab => by
          rw [hR] at hab
          rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩ <;>
            simp_all [pinClassLabel, markedMap]⟩, hcard]
        simp [hxy, hxg, hyg, one_div]
      · have hbot : R = ⊥ := bot_unique fun a b hab => by
          rcases a with _ | ⟨_ | _⟩ <;> rcases b with _ | ⟨_ | _⟩
          · rfl
          · exact (hxg (R.symm hab)).elim
          · exact (hyg (R.symm hab)).elim
          · exact (hxg hab).elim
          · rfl
          · exact (hxy hab).elim
          · exact (hyg hab).elim
          · exact (hxy (R.symm hab)).elim
          · rfl
        have hcard : Nat.card (Quotient R) = 3 := by
          rw [hbot, Nat.card_congr (Setoid.quotientBotEquiv : Quotient (⊥ : Setoid (Option Bool)) ≃ Option Bool)]
          norm_num
        rw [kernel_sum_of_always_compat q pin fun c a b hab => by
          rw [hbot] at hab; subst hab; rfl, hcard]
        simp only [hxy, hxg, hyg, and_self, or_self, ↓reduceIte, mul_zero, add_zero]
        field_simp

theorem wired_spin_correlation_lower_bound (q : ℕ) (hq : 2 ≤ q)
    (β : ℝ) (hβ : 0 < β) (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto (fun n => wiredBoxProbabilityMeasure (fkParameters q hq β hβ)
      (0, 0) n) atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q))
    (hμ : IsPottsInfiniteVolumeLimit q β i μ.toMeasure)
    (x y : LatticeVertex) :
    μ.toMeasure.real {σ | σ x = σ y} ≥
      1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
        φ.toMeasure.real (infiniteAt x ∩ infiniteAt y) := by
  let v : Bool → LatticeVertex := fun b => if b then y else x
  let pin := boundaryColor q i hi
  let r : LatticeConfiguration → Setoid (Option Bool) :=
    infiniteWiredPartition (Option.map v)
  let P : Setoid (Option Bool) → Prop := fun R =>
    R (some false) (some true) ∨ (R (some false) none ∧ R (some true) none)
  have hformula (c : Set.Icc 1 q) :
      μ.toMeasure.real {σ : SpinSpace q | σ x = c ∧ σ y = c} =
        partitionExpectation φ.toMeasure r
          (fun R => pinnedClusterCylinderProbability R some (fun _ : Bool => c) none pin) := by
    rw [show {σ : SpinSpace q | σ x = c ∧ σ y = c} = spinObservationEvent q v (fun _ => c) by
      ext σ; simp [spinObservationEvent, v]]
    exact wired_spin_observation_formula q hq β hβ i hi φ hφ μ hμ v (fun _ => c)
  let : IsProbabilityMeasure μ.toMeasure := hμ.1
  have hsum_colors := measureReal_same_colour_sum μ.toMeasure
    (fun σ : SpinSpace q => σ x) (fun σ => σ y)
    (measurable_pi_apply x) (measurable_pi_apply y)
  have hsum_kernel :
      (∑ c : Set.Icc 1 q,
        partitionExpectation φ.toMeasure r
          (fun R => pinnedClusterCylinderProbability R some (fun _ : Bool => c) none pin)) =
        partitionExpectation φ.toMeasure r
          (fun R => 1 / (q : ℝ) + (1 - 1 / (q : ℝ)) * (if P R then 1 else 0)) := by
    unfold partitionExpectation
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [← Finset.mul_sum, wired_two_point_kernel_sum q hq pin R]
  have hrelation_event : {ω | P (r ω)} =
      {ω | (rcInfiniteOpenGraph ω).Reachable x y ∨
        (ω ∈ infiniteAt x ∧ ω ∈ infiniteAt y)} := by
    ext ω
    change (infiniteMergedSetoid (rcInfiniteOpenGraph ω) (some x) (some y) ∨
      (infiniteMergedSetoid (rcInfiniteOpenGraph ω) (some x) none ∧
        infiniteMergedSetoid (rcInfiniteOpenGraph ω) (some y) none)) ↔ _
    rw [infiniteMergedSetoid_some_some, infiniteMergedSetoid_some_none,
      infiniteMergedSetoid_some_none]
    simp [RCInfinite.infiniteAt, RCInfinite.cluster, clusterIsInfinite]
  have hformula' : μ.toMeasure.real {σ | σ x = σ y} =
      1 / (q : ℝ) + (1 - 1 / (q : ℝ)) * φ.toMeasure.real {ω | P (r ω)} := by
    rw [hsum_colors]
    simp_rw [hformula]
    rw [hsum_kernel]
    convert partitionExpectation_affine_indicator φ.toMeasure r
      (infiniteWiredPartition_measurableSet (Option.map v)) P
      (1 / (q : ℝ)) (1 - 1 / (q : ℝ)) using 2
    funext R; by_cases hR : P R <;> simp [hR]
  rw [hformula', hrelation_event]
  have hmass := measureReal_mono (μ := φ.toMeasure)
    (fun _ hω => Or.inr hω : infiniteAt x ∩ infiniteAt y ⊆
      {ω | (rcInfiniteOpenGraph ω).Reachable x y ∨ (ω ∈ infiniteAt x ∧ ω ∈ infiniteAt y)})
  have hcoef : 0 ≤ 1 - 1 / (q : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact_mod_cast (by omega : 1 ≤ q)
  exact add_le_add_right (mul_le_mul_of_nonneg_left hmass hcoef) (1 / (q : ℝ))

end
end PottsDiscontinuity.PottsThm
