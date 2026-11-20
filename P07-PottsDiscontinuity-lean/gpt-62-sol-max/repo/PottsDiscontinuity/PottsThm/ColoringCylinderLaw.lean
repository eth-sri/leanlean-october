module

public import PottsDiscontinuity.Potts.CylinderColoring
public import PottsDiscontinuity.Potts.LimitCompactness
public import PottsDiscontinuity.Potts.ObservedPartitionLimits
public import PottsDiscontinuity.PottsThm.ColoringFactor

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.RCInfinite
open scoped Classical ENNReal

noncomputable section

/-- Distinct coordinates of the iid field have the finite product law. -/
private theorem iidFieldMeasure_injective_cylinder {A C : Type*} [Fintype A]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    (ν : Measure C) [IsProbabilityMeasure ν]
    (v : A → Vertex) (hv : Function.Injective v) (ξ : A → C) :
    iidFieldMeasure ν {u : Vertex → C | ∀ a, u (v a) = ξ a} =
      ∏ a : A, ν {ξ a} := by
  let F (u : Vertex → C) (a : A) := u (v a)
  have hm : Measurable F := by fun_prop
  rw [show {u : Vertex → C | ∀ a, u (v a) = ξ a} = F ⁻¹' {ξ} by
      ext u; simp [F, funext_iff], ← Measure.map_apply hm (measurableSet_singleton _)]
  rw [iidFieldMeasure, Measure.map_infinitePi_infinitePi_of_inj hv,
    Measure.infinitePi_singleton_of_fintype]

theorem pottsUniformColor_singleton (q : ℕ)
    (c : Set.Icc 1 q) :
    ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q)) {c} =
      (q : ℝ≥0∞)⁻¹ := by
  classical
  have h := ProbabilityTheory.uniformOn_apply_finset
    (s := (Finset.univ : Finset (Set.Icc 1 q))) (t := {c})
  have hcard : (Finset.univ : Finset (Set.Icc 1 q)).card = q := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      PottsDiscontinuity.Potts.card_pottsColors]
  rw [hcard] at h
  simpa using h

private theorem uniform_optional_cylinder {A : Type*} [Finite A] (q : ℕ) (hq : 0 < q)
    (R : Setoid A) (rep : A → Option Vertex) (pin : Set.Icc 1 q) (ξ : A → Set.Icc 1 q)
    (hrep : ∀ a b, R a b ↔ rep a = rep b)
    (hpin : R ≤ Setoid.ker ξ → ∀ a, rep a = none → ξ a = pin) :
    iidFieldMeasure (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q)))
      {u : Vertex → Set.Icc 1 q | ∀ a, (rep a).elim pin u = ξ a} =
    ENNReal.ofReal (if R ≤ Setoid.ker ξ then
      ((q : ℝ) ^ (Nat.card (Quotient R) - (if none ∈ Set.range rep then 1 else 0)))⁻¹ else 0) := by
  classical
  by_cases hc : R ≤ Setoid.ker ξ
  · let U := Set.range rep
    let T := {x : U // x.val ≠ none}
    let : Fintype U := Fintype.ofFinite _
    let : Fintype T := Fintype.ofFinite _
    let v (x : T) := x.val.val.get (Option.ne_none_iff_isSome.mp x.prop)
    have hv (x : T) : some (v x) = x.val.val := Option.some_get _
    have hinj : Function.Injective v := by
      intro x y h
      exact Subtype.ext (Subtype.ext ((hv x).symm.trans ((congrArg some h).trans (hv y))))
    let c (x : T) := ξ x.val.prop.choose
    have hc' (x : T) (a : A) (ha : rep a = x.val.val) : ξ a = c x :=
      hc ((hrep _ _).mpr (ha.trans x.val.prop.choose_spec.symm))
    have hset : {u : Vertex → Set.Icc 1 q | ∀ a, (rep a).elim pin u = ξ a} =
        {u : Vertex → Set.Icc 1 q | ∀ x : T, u (v x) = c x} := by
      ext u
      constructor
      · intro hu x
        have h := hu x.val.prop.choose
        change (rep x.val.prop.choose).elim pin u = c x at h
        rw [show rep x.val.prop.choose = some (v x) from
          x.val.prop.choose_spec.trans (hv x).symm] at h
        exact h
      · intro hu a
        cases ha : rep a with
        | none => exact (hpin hc a ha).symm
        | some y =>
          let x : T := ⟨⟨some y, ⟨a, ha⟩⟩, by simp⟩
          have hxy : v x = y := Option.some.inj (hv x)
          rw [← hxy, hc' x a ha]
          exact hu x
    let : Nonempty (Set.Icc 1 q) := ⟨pin⟩
    rw [hset, iidFieldMeasure_injective_cylinder _ _ hinj, ite_eq_left hc]
    simp_rw [pottsUniformColor_singleton, Finset.prod_const, Finset.card_univ]
    have hR : R = Setoid.ker rep := by ext a b; exact hrep a b
    have hU : Nat.card (Quotient R) = Fintype.card U := by
      rw [hR, Nat.card_congr (Setoid.quotientKerEquivRange rep), Nat.card_eq_fintype_card]
    let W := {x : U // x.val = none}
    let : Fintype W := Fintype.ofFinite _
    let : Subsingleton W := ⟨fun x y => Subtype.ext (Subtype.ext (x.prop.trans y.prop.symm))⟩
    have hW : Fintype.card W = if none ∈ Set.range rep then 1 else 0 := by
      split_ifs with h
      · let : Nonempty W := ⟨⟨⟨none, h⟩, rfl⟩⟩
        simp [← Nat.card_eq_fintype_card]
      · let : IsEmpty W := ⟨fun x => h (x.prop ▸ x.val.prop)⟩
        exact Fintype.card_of_isEmpty
    have hT : Fintype.card T = Fintype.card U - Fintype.card W :=
      Fintype.card_subtype_compl (fun x : U => x.val = none)
    have hq' : (q : ℝ) > 0 := by exact_mod_cast hq
    rw [hT, hW, hU, ENNReal.ofReal_inv_of_pos (pow_pos hq' _), ENNReal.ofReal_pow hq'.le,
      ENNReal.ofReal_natCast, ENNReal.inv_pow]
  · have hempty : {u : Vertex → Set.Icc 1 q | ∀ a, (rep a).elim pin u = ξ a} = ∅ := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hu
      apply hc
      intro a b hab
      change ξ a = ξ b
      rw [← hu a, ← hu b, (hrep a b).mp hab]
    simp [hempty, hc]

/-- For a fixed free bond configuration with finite clusters, the iid
representative coloring has the free Edwards--Sokal cylinder kernel. -/
theorem freeClusterColoring_fiber_cylinder_uniform (q : ℕ) (hq : 0 < q)
    (ω : LatticeConfiguration) (A : Finset Vertex) (ξ : SpinSpace q)
    [Fintype (Quotient (infiniteFreePartition (fun a : ↥A => a.val) ω))]
    (pin : Set.Icc 1 q) (hfinite : ∀ x, (cluster ω x).Finite) :
    iidFieldMeasure (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q)))
      {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
        clusterColoring pin (ω, u) a.val = ξ a.val} =
      ENNReal.ofReal (clusterCylinderProbability
        (infiniteFreePartition (fun a : ↥A => a.val) ω) id
        (fun a : ↥A => ξ a.val)) := by
  classical
  let R := infiniteFreePartition (fun a : ↥A => a.val) ω
  let rep := fun a : ↥A => clusterRepresentative ω a.val
  have hrep (a b : ↥A) : R a b ↔ rep a = rep b :=
    (clusterRepresentative_eq_iff_reachable ω a b (hfinite a) (hfinite b)).symm
  have hn (a : ↥A) : rep a ≠ none := fun h => (clusterRepresentative_none_iff ω a).mp h (hfinite a)
  have hr : none ∉ Set.range rep := by rintro ⟨a, h⟩; exact hn a h
  have h := uniform_optional_cylinder q hq R rep pin (fun a => ξ a.val) hrep
    (fun _ a ha => (hn a ha).elim)
  simpa [clusterColoring, clusterCylinderProbability, observedClassCount, hr, R,
    card_pottsColors] using h

/-- The representative of an observed wired class is the ghost point for the
pinned class, and the lexicographic representative otherwise. -/
def wiredObservedRepresentative {A : Type*} (ω : LatticeConfiguration)
    (v : A → Vertex) (a : Option A) : Option Vertex :=
  a.elim none (fun x => clusterRepresentative ω (v x))

private theorem representative_eq_merged (ω : LatticeConfiguration) (x y : Vertex) :
    infiniteMergedSetoid (rcInfiniteOpenGraph ω) (some x) (some y) ↔
      clusterRepresentative ω x = clusterRepresentative ω y := by
  rw [infiniteMergedSetoid_some_some]
  have hnone (a : Vertex) : clusterRepresentative ω a = none ↔ clusterIsInfinite (rcInfiniteOpenGraph ω) a :=
    clusterRepresentative_none_iff ω a
  constructor
  · rintro (h | ⟨hx, hy⟩)
    · have hi := clusterIsInfinite_saturated (rcInfiniteOpenGraph ω) x y h
      by_cases hx : (cluster ω x).Finite
      · have hy : (cluster ω y).Finite := by by_contra hn; exact hi.mpr hn hx
        exact (clusterRepresentative_eq_iff_reachable ω x y hx hy).mpr h
      · exact ((hnone x).mpr hx).trans ((hnone y).mpr (hi.mp hx)).symm
    · exact ((hnone x).mpr hx).trans ((hnone y).mpr hy).symm
  · intro h
    by_cases hx : clusterRepresentative ω x = none
    · exact Or.inr ⟨(hnone x).mp hx, (hnone y).mp (h.symm.trans hx)⟩
    · have hf (a : Vertex) (h : clusterRepresentative ω a ≠ none) : (cluster ω a).Finite :=
        not_not.mp (mt (hnone a).mpr h)
      exact Or.inl ((clusterRepresentative_eq_iff_reachable ω x y (hf x hx)
        (hf y fun h' => hx (h.trans h'))).mp h)

theorem wiredObservedRepresentative_eq_iff {A : Type*} [Fintype A]
    (ω : LatticeConfiguration) (v : A → Vertex) (a b : Option A) :
    infiniteWiredPartition (Option.map v) ω a b ↔
      wiredObservedRepresentative ω v a = wiredObservedRepresentative ω v b := by
  cases a <;> cases b
  · exact ⟨fun _ => rfl, fun _ => (infiniteMergedSetoid _).refl none⟩
  · rename_i b
    change infiniteMergedSetoid (rcInfiniteOpenGraph ω) none (some (v b)) ↔ none = clusterRepresentative ω (v b)
    rw [eq_comm]
    exact (show infiniteMergedSetoid (rcInfiniteOpenGraph ω) none (some (v b)) ↔
      infiniteMergedSetoid (rcInfiniteOpenGraph ω) (some (v b)) none from
        ⟨(infiniteMergedSetoid _).symm, (infiniteMergedSetoid _).symm⟩).trans
      ((infiniteMergedSetoid_some_none _ _).trans (clusterRepresentative_none_iff ω _).symm)
  · exact (infiniteMergedSetoid_some_none _ _).trans (clusterRepresentative_none_iff ω _).symm
  · exact representative_eq_merged ω _ _

/-- For a fixed wired configuration, pinning infinite clusters and coloring
finite clusters by iid representatives gives the pinned cylinder kernel. -/
theorem wiredClusterColoring_fiber_cylinder_uniform (q : ℕ) (hq : 0 < q)
    (ω : LatticeConfiguration) (A : Finset Vertex) (ξ : SpinSpace q)
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) :
    iidFieldMeasure (ProbabilityTheory.uniformOn (Set.univ : Set (Set.Icc 1 q)))
      {u : Vertex → Set.Icc 1 q | ∀ a : ↥A,
        clusterColoring (boundaryColor q i hi) (ω, u) a.val = ξ a.val} =
      ENNReal.ofReal (pinnedClusterCylinderProbability
        (infiniteWiredPartition (Option.map (fun a : ↥A => a.val)) ω)
        some (fun a : ↥A => ξ a.val) none (boundaryColor q i hi)) := by
  classical
  let v := fun a : ↥A => a.val
  let R := infiniteWiredPartition (Option.map v) ω
  let rep := wiredObservedRepresentative ω v
  let pin := boundaryColor q i hi
  let ξ' := markedMap (fun a : ↥A => ξ a.val) pin
  have hrep := wiredObservedRepresentative_eq_iff ω v
  have hpin (hc : R ≤ Setoid.ker ξ') (a : Option ↥A) (h : rep a = none) : ξ' a = pin :=
    hc ((hrep a none).mpr h)
  have hr : none ∈ Set.range rep := ⟨none, rfl⟩
  have hid : markedMap some none = (id : Option ↥A → Option ↥A) := by funext a; cases a <;> rfl
  have h := uniform_optional_cylinder q hq R rep pin ξ' hrep hpin
  simpa [pinnedClusterCylinderProbability, observedClassCount, hid, hr, card_pottsColors,
    Option.forall, ξ', markedMap, rep, wiredObservedRepresentative, clusterColoring, v, R, pin] using h

/-- Integrating a finite partition kernel over the first factor gives its
finite weighted sum. -/
theorem lintegral_finitePartitionKernel {Ω A : Type*} [MeasurableSpace Ω]
    [Fintype A] [Fintype (Setoid A)] (μ : Measure Ω)
    (r : Ω → Setoid A) (K : Setoid A → ℝ≥0∞)
    (hr : ∀ R, MeasurableSet {ω | r ω = R}) :
    ∫⁻ ω, K (r ω) ∂μ =
      ∑ R : Setoid A, K R * μ {ω | r ω = R} := by
  classical
  let f := fun R =>
    {ω | r ω = R}.indicator (fun _ => K R)
  have hf : (fun ω => K (r ω)) = fun ω => ∑ R : Setoid A, f R ω := by
    funext ω
    dsimp [f]
    rw [Finset.sum_eq_single (r ω)]
    · simp
    · intro R _ hR
      simp [hR.symm]
    · simp
  rw [hf, lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro R hR
    rw [lintegral_indicator_const (hr R)]
  · intro R hR
    exact measurable_const.indicator (hr R)

theorem toReal_lintegral_finitePartitionKernel {Ω A : Type*} [MeasurableSpace Ω]
    [Finite A] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Setoid A) (K : Setoid A → ℝ)
    (hK : ∀ R, 0 ≤ K R)
    (hr : ∀ R, MeasurableSet {ω | r ω = R}) :
    (∫⁻ ω, ENNReal.ofReal (K (r ω)) ∂μ).toReal =
      PottsDiscontinuity.Potts.partitionExpectation μ r K := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype (Setoid A) := Fintype.ofFinite (Setoid A)
  rw [lintegral_finitePartitionKernel μ r (fun R => ENNReal.ofReal (K R)) hr]
  unfold PottsDiscontinuity.Potts.partitionExpectation
  rw [ENNReal.toReal_sum (fun R hR =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _))]
  apply Finset.sum_congr rfl
  intro R hR
  calc
    (ENNReal.ofReal (K R) * μ {ω | r ω = R}).toReal =
        K R * (μ {ω | r ω = R}).toReal := by simp [hK R]
    _ = (μ {ω | r ω = R}).toReal * K R := mul_comm _ _

end
end PottsDiscontinuity.PottsThm
