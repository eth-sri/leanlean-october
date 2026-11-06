module

public import PottsDiscontinuity.Potts.InfinitePartitionMeasurability
public import PottsDiscontinuity.Potts.PartitionExpectationAlgebra
public import PottsDiscontinuity.Potts.SpinEventDecomposition
public import PottsDiscontinuity.Potts.WiredSpinObservations
public import PottsDiscontinuity.RCInfinite.ClusterEvents

public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Topology
open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.RCInfinite
open Classical

noncomputable section

theorem natCard_quotient_ker_bool_of_surjective
    (f : Option Bool → Bool) (hf : Function.Surjective f) :
    Nat.card (Quotient (Setoid.ker f)) = 2 := by
  rw [Nat.card_congr (Setoid.quotientKerEquivRange f), Set.range_eq_univ.mpr hf]
  simp

theorem wiredPairSetoid_cases (R : Setoid (Option Bool)) :
    R = (⊤ : Setoid (Option Bool)) ∨ R = Setoid.ker Option.isSome ∨
      R = Setoid.ker (· == some true) ∨ R = Setoid.ker (· == some false) ∨ R = ⊥ := by
  have t1 : R (some false) (some true) → R (some false) none → R (some true) none :=
    fun h1 h2 => R.trans (R.symm h1) h2
  have t2 : R (some false) none → R (some true) none → R (some false) (some true) :=
    fun h1 h2 => R.trans h1 (R.symm h2)
  have t3 : R (some false) (some true) → R (some true) none → R (some false) none := R.trans
  simp only [Setoid.ext_iff, Option.forall, Bool.forall_bool, Setoid.comm' R (x := none),
    Setoid.comm' R (y := some false), R.refl', Setoid.ker_def]
  by_cases hxy : R (some false) (some true) <;> by_cases hxg : R (some false) none <;>
    by_cases hyg : R (some true) none <;> simp_all

theorem hcomap (R : Setoid (Option Bool)) : R.comap (markedMap some none) = R :=
  Setoid.ext fun a b => by cases a <;> cases b <;> rfl

section
variable (q : ℕ) (hq : 2 ≤ q)
theorem pin_kernel_sum {R : Setoid (Option Bool)} {b : Bool} (hb : R (some b) none) (pin : Set.Icc 1 q) :
    ∑ c : Set.Icc 1 q, pinnedClusterCylinderProbability R some (fun _ : Bool => c) none pin =
      ((q : ℝ) ^ (Nat.card (Quotient R) - 1))⁻¹ := by
  have (c : Set.Icc 1 q) : R ≤ Setoid.ker (markedMap (fun _ : Bool => c) pin) ↔ c = pin :=
    ⟨fun h => h hb, fun h a b _ => by subst h; cases a <;> cases b <;> rfl⟩
  simp [pinnedClusterCylinderProbability, this, observedClassCount, hcomap]

theorem free_kernel_sum {R : Setoid (Option Bool)} (hf : ¬R (some false) none) (ht : ¬R (some true) none)
    (pin : Set.Icc 1 q) :
    ∑ c : Set.Icc 1 q, pinnedClusterCylinderProbability R some (fun _ : Bool => c) none pin =
      q * ((q : ℝ) ^ (Nat.card (Quotient R) - 1))⁻¹ := by
  have (c : Set.Icc 1 q) : R ≤ Setoid.ker (markedMap (fun _ : Bool => c) pin) := fun a b h => by
    rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> simp_all [markedMap, Setoid.comm' R]
  simp [pinnedClusterCylinderProbability, this, observedClassCount, hcomap]

include hq
theorem wired_two_point_kernel_sum (pin : Set.Icc 1 q) (R : Setoid (Option Bool)) :
    ∑ c : Set.Icc 1 q,
      pinnedClusterCylinderProbability R some (fun _ : Bool => c) none pin =
        1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
          (if R (some false) (some true) ∨
            (R (some false) none ∧ R (some true) none) then 1 else 0) := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  rcases wiredPairSetoid_cases R with rfl | rfl | rfl | rfl | rfl
  · have : Subsingleton (Quotient (⊤ : Setoid (Option Bool))) := Quotient.subsingleton_iff.mpr rfl
    rw [pin_kernel_sum q (b := false) trivial, Nat.card_unique]
    simp
  · rw [free_kernel_sum q (by simp [Setoid.ker_def]) (by simp [Setoid.ker_def]),
      natCard_quotient_ker_bool_of_surjective _ (by decide)]
    simp [Setoid.ker_def, hq0]
  · rw [pin_kernel_sum q rfl, natCard_quotient_ker_bool_of_surjective _ (by decide)]
    simp [Setoid.ker_def]
  · rw [pin_kernel_sum q (b := true) rfl, natCard_quotient_ker_bool_of_surjective _ (by decide)]
    simp [Setoid.ker_def]
  · rw [free_kernel_sum q (by simp) (by simp), Nat.card_congr (Setoid.quotientBotEquiv (α := Option Bool))]
    simp
    field_simp

/-- Edwards--Sokal coloring gives a wired two-spin lower bound: the spins are
equal whenever the observations are connected, and in particular are equal
with certainty when both observations lie in infinite clusters. -/
theorem wired_spin_correlation_lower_bound (β : ℝ) (hβ : 0 < β) (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
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
  let r := infiniteWiredPartition (Option.map v)
  have hformula (c : Set.Icc 1 q) : μ.toMeasure.real {σ : SpinSpace q | σ x = c ∧ σ y = c} =
      partitionExpectation φ.toMeasure r
        (fun R => pinnedClusterCylinderProbability R some (fun _ : Bool => c) none (boundaryColor q i hi)) := by
    rw [show {σ : SpinSpace q | σ x = c ∧ σ y = c} = spinObservationEvent q v (fun _ => c) by
      simp [spinObservationEvent, v]]
    exact wired_spin_observation_formula q hq β hβ i hi φ hφ μ hμ v (fun _ => c)
  rw [measureReal_same_colour_sum μ.toMeasure (· x) (· y) (measurable_pi_apply x) (measurable_pi_apply y)]
  simp_rw [hformula]
  unfold partitionExpectation
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, wired_two_point_kernel_sum q hq]
  rw [ge_iff_le, ← partitionExpectation]
  rw [show partitionExpectation _ _ _ = _ by convert (partitionExpectation_affine_indicator φ.toMeasure r
    (infiniteWiredPartition_measurableSet (Option.map v)) _ (1 / (q : ℝ)) (1 - 1 / (q : ℝ)))]
  have hc : 0 ≤ 1 - 1 / (q : ℝ) := sub_nonneg.2 (div_le_one_of_le₀ (by exact_mod_cast (by omega : 1 ≤ q)) (by positivity))
  gcongr
  · simp
  exact fun ω h => Or.inr ⟨(infiniteMergedSetoid_some_none _ x).2 h.1,
    (infiniteMergedSetoid_some_none _ y).2 h.2⟩
end

end
end PottsDiscontinuity.PottsThm
