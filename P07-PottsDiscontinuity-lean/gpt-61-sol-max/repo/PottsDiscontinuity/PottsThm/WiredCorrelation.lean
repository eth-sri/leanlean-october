module
public import Mathlib

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

def falsePinClassLabel : Option Bool → Bool
  | some true => true
  | _ => false

def truePinClassLabel : Option Bool → Bool
  | some false => true
  | _ => false

def pairClassRel  := Setoid.ker pairClassLabel
def falsePinClassRel  := Setoid.ker falsePinClassLabel
def truePinClassRel  := Setoid.ker truePinClassLabel

private theorem natCard_quotient_ker_bool_of_surjective
    (f : Option Bool → Bool) (hf : Function.Surjective f) :
    Nat.card (Quotient (Setoid.ker f)) = 2 := by
  calc
    Nat.card (Quotient (Setoid.ker f)) = Nat.card (Set.range f) :=
      Nat.card_congr (Setoid.quotientKerEquivRange f)
    _ = Nat.card Bool := by rw [Set.range_eq_univ.mpr hf]; simp
    _ = 2 := by simp

private theorem natCard_quotient_top_optionBool :
    Nat.card (Quotient (⊤ : Setoid (Option Bool))) = 1 := by
  let : Subsingleton (Quotient (⊤ : Setoid (Option Bool))) :=
    Quotient.subsingleton_iff.mpr rfl
  
  exact Nat.card_unique

private theorem natCard_quotient_bot_optionBool :
    Nat.card (Quotient (⊥ : Setoid (Option Bool))) = 3 := by
  calc
    Nat.card (Quotient  ⊥ ) = Nat.card (Option Bool) :=
      Nat.card_congr Setoid.quotientBotEquiv
    _ = 3 := by norm_num

private theorem pinnedObservedClassCount (R : Setoid (Option Bool)) :
    observedClassCount R (markedMap some none) = Nat.card (Quotient R) := by
  have hid : markedMap some none = (id : Option Bool → Option Bool) := by
    funext a
    cases a <;> rfl
  rw [hid]
  rfl

private theorem pairClassRel_card : Nat.card (Quotient pairClassRel) = 2 := natCard_quotient_ker_bool_of_surjective pairClassLabel (by
                                                                        intro b
                                                                        cases b
                                                                        · exact ⟨none, rfl⟩
                                                                        · exact ⟨some false, rfl⟩)

private theorem falsePinClassRel_card : Nat.card (Quotient falsePinClassRel) = 2 := natCard_quotient_ker_bool_of_surjective falsePinClassLabel (by
                                                                                intro b
                                                                                cases b
                                                                                · exact ⟨none, rfl⟩
                                                                                · exact ⟨some true, rfl⟩)

private theorem truePinClassRel_card : Nat.card (Quotient truePinClassRel) = 2 := natCard_quotient_ker_bool_of_surjective truePinClassLabel (by
                                                                              intro b
                                                                              cases b
                                                                              · exact ⟨none, rfl⟩
                                                                              · exact ⟨some false, rfl⟩)

section

variable (q : ℕ)
include q

private theorem pairClassRel_kernel 
    (pin c : Set.Icc 1 q) :
    pinnedClusterCylinderProbability pairClassRel some (fun _ : Bool => c) none pin =
      (q : ℝ)⁻¹ := by
  
  unfold pinnedClusterCylinderProbability
  rw [ite_eq_left (by
                     intro a b hab
                     change pairClassLabel (markedMap some none a) = pairClassLabel (markedMap some none b) at hab
                     
                     cases a <;> cases b <;> simp_all [pairClassLabel, markedMap]), pinnedObservedClassCount, pairClassRel_card]
  simp

private theorem falsePinClassRel_compatible_iff  (c pin : Set.Icc 1 q) :
    falsePinClassRel.comap (markedMap some none) ≤
      Setoid.ker (markedMap (fun _ : Bool => c) pin) ↔ c = pin := by
  constructor
  · intro h
    have hrel : falsePinClassRel.comap (markedMap some none) (some false) none := rfl
    have heq := h hrel
    
    simpa [markedMap] using heq
  · intro hcp a b hab
    
    
    cases a <;> cases b <;> simp_all [falsePinClassLabel, markedMap]

private theorem truePinClassRel_compatible_iff  (c pin : Set.Icc 1 q) :
    truePinClassRel.comap (markedMap some none) ≤
      Setoid.ker (markedMap (fun _ : Bool => c) pin) ↔ c = pin := by
  constructor
  · intro h
    have hrel : truePinClassRel.comap (markedMap some none) (some true) none := rfl
    have heq := h hrel
    
    simpa [markedMap] using heq
  · intro hcp a b hab
    
    
    cases a <;> cases b <;> simp_all [truePinClassLabel, markedMap]

private theorem falsePinClassRel_kernel 
    (pin c : Set.Icc 1 q) :
    pinnedClusterCylinderProbability falsePinClassRel some (fun _ : Bool => c) none pin =
      if c = pin then (q : ℝ)⁻¹ else 0 := by
  by_cases hcp : c = pin
  · 
    unfold pinnedClusterCylinderProbability
    rw [ite_eq_left ((falsePinClassRel_compatible_iff q c pin).2 hcp), pinnedObservedClassCount, falsePinClassRel_card]
    simp [hcp]
  · simp_all [markedMap, pinnedClusterCylinderProbability, falsePinClassRel_compatible_iff]

private theorem truePinClassRel_kernel 
    (pin c : Set.Icc 1 q) :
    pinnedClusterCylinderProbability truePinClassRel some (fun _ : Bool => c) none pin =
      if c = pin then (q : ℝ)⁻¹ else 0 := by
  by_cases hcp : c = pin
  · 
    unfold pinnedClusterCylinderProbability
    rw [ite_eq_left ((truePinClassRel_compatible_iff q c pin).2 hcp), pinnedObservedClassCount, truePinClassRel_card]
    simp [hcp]
  · simp_all [markedMap, pinnedClusterCylinderProbability, truePinClassRel_compatible_iff]

private theorem pairClassRel_kernel_sum  (hq : 2 ≤ q)
    (pin : Set.Icc 1 q) :
    ∑ c : Set.Icc 1 q,
      pinnedClusterCylinderProbability pairClassRel some (fun _ : Bool => c) none pin = 1 := by
  simp_rw [pairClassRel_kernel q pin]
   
  have hcard : Fintype.card (Set.Icc 1 q) = q := by
    simp
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hcard]
  field_simp

private theorem falsePinClassRel_kernel_sum 
    (pin : Set.Icc 1 q) :
    ∑ c : Set.Icc 1 q,
      pinnedClusterCylinderProbability falsePinClassRel some (fun _ : Bool => c) none pin =
        (q : ℝ)⁻¹ := by
  simp_rw [falsePinClassRel_kernel q pin]
  simp

private theorem truePinClassRel_kernel_sum 
    (pin : Set.Icc 1 q) :
    ∑ c : Set.Icc 1 q,
      pinnedClusterCylinderProbability truePinClassRel some (fun _ : Bool => c) none pin =
        (q : ℝ)⁻¹ := by
  simp_rw [truePinClassRel_kernel q pin]
  simp

private theorem top_optionBool_compatible_iff  (c pin : Set.Icc 1 q) :
    (⊤ : Setoid (Option Bool)).comap (markedMap some none) ≤
      Setoid.ker (markedMap (fun _ : Bool => c) pin) ↔ c = pin := by
  constructor
  · exact fun a => (fun q c pin => (falsePinClassRel_compatible_iff q c pin).mp) q c pin fun ⦃x y⦄ a_1 => a trivial
  · intro hcp a b hab
    
    
    cases a <;> cases b <;> simp [markedMap, hcp]

private theorem top_optionBool_kernel 
    (pin c : Set.Icc 1 q) :
    pinnedClusterCylinderProbability (⊤ : Setoid (Option Bool)) some
      (fun _ : Bool => c) none pin = if c = pin then 1 else 0 := by
  by_cases hcp : c = pin
  · 
    unfold pinnedClusterCylinderProbability
    rw [ite_eq_left ((top_optionBool_compatible_iff q c pin).2 hcp), pinnedObservedClassCount, natCard_quotient_top_optionBool]
    simp [hcp]
  · simp_all [markedMap, pinnedClusterCylinderProbability, top_optionBool_compatible_iff]

private theorem top_optionBool_kernel_sum 
    (pin : Set.Icc 1 q) :
    ∑ c : Set.Icc 1 q,
      pinnedClusterCylinderProbability (⊤ : Setoid (Option Bool)) some
        (fun _ : Bool => c) none pin = 1 := by
  simp_rw [top_optionBool_kernel q pin]
  simp

private theorem bot_optionBool_compatible  (c pin : Set.Icc 1 q) :
    (⊥ : Setoid (Option Bool)).comap (markedMap some none) ≤
      Setoid.ker (markedMap (fun _ : Bool => c) pin) := by
  intro a b hab
  
  have hab' : a = b := by
    have hid : markedMap some none = (id : Option Bool → Option Bool) := by
      funext z
      cases z <;> rfl
    simp_all
  rw [hab']

private theorem bot_optionBool_kernel 
    (pin c : Set.Icc 1 q) :
    pinnedClusterCylinderProbability (⊥ : Setoid (Option Bool)) some
      (fun _ : Bool => c) none pin = ((q : ℝ) ^ 2)⁻¹ := by
  
  unfold pinnedClusterCylinderProbability
  rw [ite_eq_left (bot_optionBool_compatible q c pin), pinnedObservedClassCount, natCard_quotient_bot_optionBool]
  simp

private theorem bot_optionBool_kernel_sum  (hq : 2 ≤ q)
    (pin : Set.Icc 1 q) :
    ∑ c : Set.Icc 1 q,
      pinnedClusterCylinderProbability (⊥ : Setoid (Option Bool)) some
        (fun _ : Bool => c) none pin = (q : ℝ)⁻¹ := by
  simp_rw [bot_optionBool_kernel q pin]
   
  have hcard : Fintype.card (Set.Icc 1 q) = q := by
    simp
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hcard]
  field_simp

end

section

variable (R : Setoid (Option Bool))
include R

section

variable (hxy : R (some false) (some true))
include hxy

private theorem wiredRelation_eq_top 
     (hxg : R (some false) none) : R = ⊤ := by
  
  apply top_unique
  intro a b _
  cases a with
  | none =>
    cases b with
    | none => exact R.refl _
    | some b =>
      cases b with
      | false => exact R.symm hxg
      | true => exact R.symm (R.trans (R.symm hxy) hxg)
  | some a =>
    cases a with
    | false =>
      cases b with
      | none => exact hxg
      | some b =>
        cases b with
        | false => exact R.refl _
        | true => exact hxy
    | true =>
      cases b with
      | none => exact  R.trans (R.symm hxy) hxg 
      | some b =>
        cases b with
        | false => exact R.symm hxy
        | true => exact R.refl _

private theorem wiredRelation_eq_pairClassRel 
     (hxg : ¬ R (some false) none) :
    R = pairClassRel := by
  have hyg : ¬ R (some true) none := by
                                       solve_by_elim [_root_.Setoid.trans]
  have hgnx : ¬ R none (some false) := by
                                         solve_by_elim [_root_.Setoid.symm]
  have hgny : ¬ R none (some true) := by
                                        solve_by_elim [_root_.Setoid.symm]
  
  apply Setoid.ext
  intro a b
  change R a b ↔ pairClassLabel a = pairClassLabel b
  cases a with
  | none =>
    cases b with
    | none => simp [pairClassLabel]
    | some b =>
      cases b <;> simp [pairClassLabel, hgnx, hgny]
  | some a =>
    cases a with
    | false =>
      cases b with
      | none => simp [pairClassLabel, hxg]
      | some b =>
        cases b with
        | false => simp [pairClassLabel]
        | true => simp [pairClassLabel, hxy]
    | true =>
      cases b with
      | none => simp [pairClassLabel, hyg]
      | some b =>
        cases b with
        | false => simp [pairClassLabel,  R.symm hxy ]
        | true => simp [pairClassLabel]

end

section

variable (hxy : ¬ R (some false) (some true))
include hxy

private theorem wiredRelation_eq_falsePinClassRel 
     (hxg : R (some false) none) :
    R = falsePinClassRel := by
  have hyg : ¬ R (some true) none := by
                                       solve_by_elim [_root_.Setoid.trans]
  have hyx : ¬ R (some true) (some false) := by
                                               solve_by_elim [_root_.Setoid.symm]
  
  have hgy : ¬ R none (some true) := by
                                       solve_by_elim [_root_.Setoid.symm]
  apply Setoid.ext
  intro a b
  change R a b ↔ falsePinClassLabel a = falsePinClassLabel b
  cases a with
  | none =>
    cases b with
    | none => simp [falsePinClassLabel]
    | some b =>
      cases b with
      | false => simp [falsePinClassLabel,  R.symm hxg ]
      | true => simp [falsePinClassLabel, hgy]
  | some a =>
    cases a with
    | false =>
      cases b with
      | none => simp [falsePinClassLabel, hxg]
      | some b =>
        cases b with
        | false => simp [falsePinClassLabel]
        | true => simp [falsePinClassLabel, hxy]
    | true =>
      cases b with
      | none => simp [falsePinClassLabel, hyg]
      | some b =>
        cases b with
        | false => simp [falsePinClassLabel, hyx]
        | true => simp [falsePinClassLabel]

private theorem wiredRelation_eq_truePinClassRel 
     (hyg : R (some true) none) :
    R = truePinClassRel := by
  have hxg : ¬ R (some false) none := by
                                        solve_by_elim [_root_.Setoid.trans]
  have hyx : ¬ R (some true) (some false) := by
                                               solve_by_elim [_root_.Setoid.symm]
  have hgx : ¬ R none (some false) := by
                                        solve_by_elim [_root_.Setoid.symm]
  
  apply Setoid.ext
  intro a b
  change R a b ↔ truePinClassLabel a = truePinClassLabel b
  cases a with
  | none =>
    cases b with
    | none => simp [truePinClassLabel]
    | some b =>
      cases b with
      | false => simp [truePinClassLabel, hgx]
      | true => simp [truePinClassLabel,  R.symm hyg ]
  | some a =>
    cases a with
    | false =>
      cases b with
      | none => simp [truePinClassLabel, hxg]
      | some b =>
        cases b with
        | false => simp [truePinClassLabel]
        | true => simp [truePinClassLabel, hxy]
    | true =>
      cases b with
      | none => simp [truePinClassLabel, hyg]
      | some b =>
        cases b with
        | false => simp [truePinClassLabel, hyx]
        | true => simp [truePinClassLabel]

private theorem wiredRelation_eq_bot 
    
    (hxg : ¬ R (some false) none) (hyg : ¬ R (some true) none) : R = ⊥ := by
  apply bot_unique
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      cases b with
      | false => exact (hxg (R.symm hab)).elim
      | true => exact (hyg (R.symm hab)).elim
  | some a =>
    cases a with
    | false =>
      cases b with
      | none => exact (hxg hab).elim
      | some b =>
        simp_all <;> grind
    | true =>
      cases b with
      | none => exact (hyg hab).elim
      | some b =>
        cases b with
        | false => exact (hxy (R.symm hab)).elim
        | true => rfl

end

private theorem wiredPairSetoid_cases  :
    R = (⊤ : Setoid (Option Bool)) ∨ R = pairClassRel ∨
      R = falsePinClassRel ∨ R = truePinClassRel ∨ R = ⊥ := by
  by_cases hxy : R (some false) (some true)
  · grind [wiredRelation_eq_top, wiredRelation_eq_pairClassRel]
  · grind [wiredRelation_eq_falsePinClassRel, wiredRelation_eq_truePinClassRel, wiredRelation_eq_bot]

end

private theorem wired_two_point_kernel_sum (q : ℕ) (hq : 2 ≤ q)
    (pin : Set.Icc 1 q) (R : Setoid (Option Bool)) :
    ∑ c : Set.Icc 1 q,
      pinnedClusterCylinderProbability R some (fun _ : Bool => c) none pin =
        1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
           if R (some false) (some true) ∨
             R (some false) none ∧ R (some true) none  then 1 else 0  := by
  rcases wiredPairSetoid_cases R with htop | hpair | hfalse | htrue | hbot
  · rw [htop]
    
    rw [top_optionBool_kernel_sum q pin]
    simp [ True.intro ]
  · rw [hpair]
    have hxy : pairClassRel (some false) (some true) := rfl
    rw [pairClassRel_kernel_sum q hq pin]
    simp [hxy]
  · rw [hfalse]
    have hxy : ¬ falsePinClassRel (some false) (some true) := of_eq_true (Eq.trans (congrArg Not Bool.false_eq_true) not_false_eq_true)
    
    have hyg : ¬ falsePinClassRel (some true) none := by
                                                        solve_by_elim [_root_.of_eq_true]
    rw [falsePinClassRel_kernel_sum q pin]
    simp [hxy, (rfl), hyg]
  · rw [htrue]
    have hxy : ¬ truePinClassRel (some false) (some true) := of_eq_true (Eq.trans (congrArg Not Bool.true_eq_false) not_false_eq_true)
    have hxg : ¬ truePinClassRel (some false) none := by
      assumption
    
    rw [truePinClassRel_kernel_sum q pin]
    simp [hxy, hxg, (rfl)]
  · rw [hbot]
    
    
    
    rw [bot_optionBool_kernel_sum q hq pin]
    simp

/-- Edwards--Sokal coloring gives a wired two-spin lower bound: the spins are
equal whenever the observations are connected, and in particular are equal
with certainty when both observations lie in infinite clusters. -/
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
  let r  :=
    infiniteWiredPartition (Option.map v)
  let P : Setoid (Option Bool) → Prop := fun R =>
    R (some false) (some true) ∨  R (some false) none ∧ R (some true) none 
  have hevent (c : Set.Icc 1 q) :
      {σ : SpinSpace q | σ x = c ∧ σ y = c} =
        spinObservationEvent q v  fun _ => c  := by
    
    simp [spinObservationEvent, v]
  have hformula (c : Set.Icc 1 q) :
      μ.toMeasure.real {σ : SpinSpace q | σ x = c ∧ σ y = c} =
        partitionExpectation φ.toMeasure r
           fun R => pinnedClusterCylinderProbability R some (fun _  => c) none pin  := by
    rw [hevent c]
    exact wired_spin_observation_formula q hq β hβ i hi φ hφ μ hμ v  fun _ => c 
  
  
  have hsum_kernel :
       ∑ c : Set.Icc 1 q,
        partitionExpectation φ.toMeasure r
          (fun R => pinnedClusterCylinderProbability R some (fun _  => c) none pin)  =
        partitionExpectation φ.toMeasure r
           fun R => ∑ c : Set.Icc 1 q,
            pinnedClusterCylinderProbability R some (fun _  => c) none pin  := by
    unfold partitionExpectation
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro R hR
    rw [← Finset.mul_sum]
  
  have hrelation_event : {ω | P (r ω)} =
      {ω | (rcInfiniteOpenGraph ω).Reachable x y ∨
         ω ∈ infiniteAt x ∧ ω ∈ infiniteAt y } := by
    ext ω
    change  infiniteMergedSetoid (rcInfiniteOpenGraph ω) (some x) (some y) ∨
       infiniteMergedSetoid (rcInfiniteOpenGraph ω) (some x) none ∧
        infiniteMergedSetoid (rcInfiniteOpenGraph ω) (some y) none   ↔ _
    rw [infiniteMergedSetoid_some_some, infiniteMergedSetoid_some_none,
      infiniteMergedSetoid_some_none]
    simp [RCInfinite.infiniteAt, RCInfinite.cluster, clusterIsInfinite]
  have hformula' : μ.toMeasure.real {σ | σ x = σ y} =
      1 /  q  + (1 - 1 /  q ) *
        φ.toMeasure.real {ω | P (r ω)} := by
    rw [ measureReal_same_colour_sum μ.toMeasure
           (fun σ  => σ x) (fun σ => σ y)
           (measurable_pi_apply x) (measurable_pi_apply y) ]
    simp_rw [hformula]
    rw [hsum_kernel,  funext (wired_two_point_kernel_sum q hq pin) ]
    calc
      _ = partitionExpectation φ.toMeasure r  fun R =>
          1 /  q  + (1 - 1 /  q ) *  if P R then 1 else 0   := by
        congr 1
      _ = _ := by
        convert  partitionExpectation_affine_indicator φ.toMeasure r
          (infiniteWiredPartition_measurableSet (Option.map v)) P
          (1 /  q ) (1 - 1 /  q )  using 1
        
        grind
  rw [hrelation_event] at hformula'
  
  have hcoef : 0 ≤ 1 - 1 / (q : ℝ) := by
    exact Nat.one_sub_one_div_cast_nonneg q
  calc
    μ.toMeasure.real {σ | σ x = σ y} =
        1 /  q  + (1 - 1 /  q ) *
          φ.toMeasure.real {ω | (rcInfiniteOpenGraph ω).Reachable x y ∨
             ω ∈ infiniteAt x ∧ ω ∈ infiniteAt y } := hformula'
    _ ≥ 1 /  q  + (1 - 1 /  q ) *
          φ.toMeasure.real (infiniteAt x ∩ infiniteAt y) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left (mul_le_mul_of_nonneg_left (measureReal_mono (μ := φ.toMeasure)
                                                      (show {ω : LatticeConfiguration | ω ∈ infiniteAt x ∧ ω ∈ infiniteAt y} ⊆
                                                        {ω | (rcInfiniteOpenGraph ω).Reachable x y ∨
                                                           ω ∈ infiniteAt x ∧ ω ∈ infiniteAt y } from fun ⦃ω⦄ => Or.inr)) hcoef) (1 /  q )

end
end PottsDiscontinuity.PottsThm
